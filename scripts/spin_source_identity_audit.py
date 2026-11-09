#!/usr/bin/env python3
"""Check the Lean finite-ladder definitions against the executable reduction.

The arbitrary-capacity statements are proved in Lean. These finite numerical
checks cover transcription, normalization, top states and clock-basis transport.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters
from holomorphic_tensor_phase_audit import finite_operators


def current(P, D):
    return (P @ D + D @ P) / 2


def source_from_ladders(ann, hbar):
    skew = [A - A.conj().T for A in ann]
    P = -1j * (skew[1] + skew[2])
    Qx = -1j * (skew[1] - skew[2])
    pi = -1j * (skew[3] + skew[4] + skew[5])
    phix = -1j * (skew[3] - skew[4])
    return hbar / 2 * (current(P, Qx) + current(pi, phix))


def arbitrary_weights(R, seed):
    rng = np.random.default_rng(seed)
    states, canonical = finite_operators(6, 6, None, R)
    states = np.asarray(states)
    n = states.sum(axis=1)
    q = states @ np.array([0, 1, -1, 1, -1, 0])
    weights = rng.normal(size=R + 2)
    weights[-1] = 0  # hard capacity boundary, independent of the radial profile
    ann = [A @ sp.diags(weights[n]) for A in canonical]
    source = source_from_ladders(ann, 0.73).toarray()
    expected = np.diag(0.73 / 2 * (weights[n]**2 + weights[n + 1]**2) * q)
    mean = source * (q[:, None] == q[None, :])
    error = float(la.norm(mean - expected))
    assert error < 2e-11
    square_errors = []
    for a, A in enumerate(ann):
        down = A.conj().T @ A - sp.diags(states[:, a] * weights[n]**2)
        up = A @ A.conj().T - sp.diags((states[:, a] + 1) * weights[n + 1]**2)
        square_errors.extend([float(sla.norm(down)), float(sla.norm(up))])
    assert max(square_errors) < 2e-11
    assert la.norm(mean[:, q == 0]) < 2e-11
    top = n == R
    top_error = float(la.norm(mean[top][:, top] - expected[top][:, top]))
    assert top_error < 2e-11
    return dict(capacity=R, seed=seed, dimension=len(n), top_states=int(sum(top)),
                maximum_square_error=max(square_errors), mean_identity_error=error,
                top_identity_error=top_error)


def box_compression(R):
    """Direct sparse transcription of the ambient Lean matrix definition."""
    states = list(itertools.product(range(R + 1), repeat=6))
    lookup = {v: i for i, v in enumerate(states)}
    active, _ = finite_operators(6, 6, None, R)
    chosen = np.array([lookup[tuple(v)] for v in active])
    outside = np.array([i for i, v in enumerate(states) if sum(v) > R], dtype=int)
    weights = np.cos(np.arange(R + 1) + 0.3)
    _, canonical = finite_operators(6, 6, None, R)
    n = np.sum(active, axis=1)
    errors = []
    for a in range(6):
        rows, cols, vals = [], [], []
        for j, v in enumerate(states):
            if v[a] and sum(v) <= R:
                target = list(v)
                target[a] -= 1
                rows.append(lookup[tuple(target)])
                cols.append(j)
                vals.append(np.sqrt(v[a]) * weights[sum(v)])
        A = sp.csr_matrix((vals, (rows, cols)), shape=(len(states),)*2)
        assert A[outside, :].nnz == 0 and A[:, outside].nnz == 0
        restricted = A[chosen, :][:, chosen]
        errors.append(float(sla.norm(restricted - canonical[a] @ sp.diags(weights[n]))))
    assert max(errors) < 1e-13
    return dict(capacity=R, box_dimension=len(states), active_dimension=len(active),
                inert_dimension=len(outside), compression_error=max(errors))


def executable_model(R, correction):
    model = ConstraintReducedSpinModel(Parameters(R=R, flavors=6, correction=correction,
                                                functional_order=2))
    n = model.number
    x = (n - 1) / R
    f = {'bare': lambda: np.ones_like(x),
         'second_order': lambda: 1 + x/2 + 3*x*x/8,
         'exact': lambda: 1/np.sqrt(1-x)}[correction]()
    _, canonical = finite_operators(6, 6, None, R)
    r = np.sqrt(1-x) * f
    ladder_error = max(float(sla.norm(A - B @ sp.diags(r)))
                       for A, B in zip(model.ann, canonical))
    source_error = float(la.norm(source_from_ladders(model.ann, model.params.hbar).toarray()
                                - model.source))
    assert ladder_error < 1e-12 and source_error < 1e-12

    # Diagonalize the actual positive clock within each charge sector.
    # Number and clock do not commute in general; the mean source after
    # this basis change must not be treated as occupation-diagonal.
    U = np.zeros_like(model.C)
    eigenvalues = np.zeros(model.dim)
    for q in np.unique(model.charge):
        selected = np.flatnonzero(model.charge == q)
        ix = np.ix_(selected, selected)
        values, vectors = la.eigh(model.C[ix])
        eigenvalues[selected] = values
        U[ix] = vectors
    transform = lambda A: U.conj().T @ A @ U
    assert la.norm(U.conj().T @ U - np.eye(model.dim)) < 2e-11
    assert np.min(eigenvalues) > 0
    assert la.norm(U * model.charge_difference) == 0
    clock_error = float(la.norm(transform(model.C) - np.diag(eigenvalues)))
    assert clock_error < 2e-11
    S = transform(model.source)
    averaged = S * model.same_charge
    covariance_error = float(la.norm(averaged - transform(model.mean_source)))
    assert covariance_error < 2e-11
    assert la.norm(averaged[:, model.physical]) < 2e-11
    K = np.zeros_like(S)
    np.divide(S, 1j * model.charge_difference, out=K, where=~model.same_charge)
    L = transform(model.Lbar) + 2*K/(eigenvalues[:, None] + eigenvalues[None, :])
    Lx = 1j * model.charge_difference * L
    D = S - (eigenvalues[:, None] + eigenvalues[None, :])/2 * Lx
    reconstruction_error = float(la.norm(D - averaged))
    assert reconstruction_error < 2e-11
    assert la.norm(L - transform(model.L)) < 2e-11
    packet, _ = model.physical_packet()
    evolved = sla.expm_multiply(-0.1j * transform(model.matrix(0.1))/model.params.hbar,
                               U.conj().T @ model.embed(packet))
    step_error = float(la.norm(D @ evolved))
    assert step_error < 2e-11
    return dict(capacity=R, correction=correction, dimension=model.dim,
                ladder_transcription_error=ladder_error, source_normalization_error=source_error,
                clock_diagonalization_error=clock_error, averaging_covariance_error=covariance_error,
                reconstructed_identity_error=reconstruction_error, constraint_after_step=step_error)


def main():
    report = dict(arbitrary_radial_weights=[arbitrary_weights(R, seed)
                                           for R in range(7) for seed in [17, 29, 43]],
                  box_compression=[box_compression(R) for R in range(4)],
                  executable_models=[executable_model(R, c) for R in [2, 4, 6]
                                     for c in ['bare', 'second_order', 'exact']])
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/spin_source_identity_audit.py', 'scripts/constraint_reduced_spin_model.py',
               'scripts/quantum_areal_spin_model.py', 'scripts/holomorphic_tensor_phase_audit.py']
    sources += ['UnifiedTheory/Audit/' + name + '.lean' for name in [
        'KFCausalFiniteOccupationLadders', 'KFCausalGradedSpinSource',
        'KFCausalSpinSourceIdentity', 'KFCausalQuantumConstraintReduction']]
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['numerical_environment'] = dict(numpy=np.__version__, scipy=scipy.__version__)
    report['scope'] = ('Numerical correspondence checks supporting separately compiled arbitrary-capacity '
                       'Lean theorems. The clock spectral basis is supplied in the formal endpoint. '
                       'This does not prove microscopic selection, a continuum limit, quantum Dirac '
                       'closure, exact canonical clock response, 3D gravity, or a TOE.')
    target = root/'data/spin_source_identity_audit.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'{target}: 21 radial profiles, 4 compressions, 9 executable-model/basis checks passed.')


if __name__ == '__main__':
    main()
