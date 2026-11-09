#!/usr/bin/env python3
"""Compensate the actual six-flavor finite-spin clock amplitudes.

Full collective spaces are retained. First-order compensation has fixed
collective polynomial degree; exact compensation is a benchmark with
growing microscopic interaction order. The canonical boundary term is
included in the exact Galerkin comparison.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla
import sympy as sy

from holomorphic_tensor_phase_audit import finite_operators


def exact_algebra():
    x = sy.symbols('x', real=True)
    f1 = 1+x/2
    f2 = 1+x/2+3*x*x/8
    assert sy.expand((1-x)*f1*f1-(1-3*x*x/4-x**3/4)) == 0
    assert sy.expand((1-x)*f2*f2-(1-5*x**3/8-15*x**4/64-9*x**5/64)) == 0
    return dict(first_order_squared_factor='1-3*x^2/4-x^3/4',
                second_order_squared_factor='1-5*x^3/8-15*x^4/64-9*x^5/64',
                exact_boundary_term='U*(R+6)*projector(N=R)/4')


def clock_operators(ann, correction):
    corrected = [a @ correction for a in ann]
    Q = (corrected[0]+corrected[0].T)/math.sqrt(2)
    P = [(a-a.T)/(1j*math.sqrt(2)) for a in corrected]
    H = sum((p @ p/2 for p in P), sp.csr_matrix(P[0].shape, dtype=complex))
    return Q, P[0], H


def canonical_compression(states):
    """Construct P_R (sum p_a^2/2) P_R directly from canonical amplitudes."""
    lookup = {tuple(state):i for i, state in enumerate(states)}
    row, col, value = [], [], []
    for j, state in enumerate(states):
        for a, n in enumerate(state):
            if n >= 2:
                target = list(state)
                target[a] -= 2
                row.append(lookup[tuple(target)])
                col.append(j)
                value.append(-math.sqrt(n*(n-1))/4)
    lower = sp.csr_matrix((value, (row, col)), shape=(len(states), len(states)))
    diagonal = sp.diags((2*np.sum(states, axis=1)+6)/4)
    return diagonal+lower+lower.T


def sparse_max(A):
    return float(np.max(abs(A.data), initial=0))


def run():
    rows = []
    matrix_checks = []
    for R in [2, 4, 8, 16]:
        states, ann = finite_operators(6, 6, R, R)
        dim = len(states)
        numbers = np.sum(states, axis=1)
        x = (numbers-1)/R
        factors = {'bare':np.ones(dim), 'first_order':1+x/2,
                   'second_order':1+x/2+3*x*x/8,
                   'exact':1/np.sqrt(1-x)}
        alpha = 0.75j
        z = alpha/math.sqrt(R)
        psi = np.zeros(dim, dtype=complex)
        for i, state in enumerate(states):
            if not any(state[1:]):
                n = state[0]
                psi[i] = math.sqrt(math.comb(R, n))*z**n/(1+abs(z)**2)**(R/2)
        assert abs(np.vdot(psi, psi)-1) < 3e-14
        for name, factor in factors.items():
            Q, P, H = clock_operators(ann, sp.diags(factor))
            if name == 'exact':
                # Compression of the untruncated canonical p² includes
                # the loop from N=R to N=R+1 and back.
                H += sp.diags((R+6)*(numbers == R)/4)
                # Exact annihilation amplitudes, not a low-number fit.
                A = ann[0] @ sp.diags(factor)
                columns = np.asarray(A.sum(axis=0)).ravel()
                assert np.max(abs(columns-np.sqrt(np.asarray(states)[:, 0]))) < 3e-14
                compression_error = sparse_max(H-canonical_compression(states))
                assert compression_error < 3e-14
                top = sp.diags((numbers == R).astype(float))
                identity = sp.eye(dim, format='csr')
                diagonal_commutator_error = sparse_max(A@A.T-A.T@A-identity+top@(identity+A.T@A))
                assert diagonal_commutator_error < 3e-14
                A1 = ann[1] @ sp.diags(factor)
                cross_commutator_error = sparse_max(A@A1.T-A1.T@A+top@(A1.T@A))
                assert cross_commutator_error < 3e-14
                # The exact-compensated rate and force defects live only
                # on the two highest occupation sectors.
                boundary = sp.diags((numbers >= R-1).astype(float))
                dq = 1j*(H@Q-Q@H)-P
                dp = 1j*(H@P-P@H)
                rate_support_error = sparse_max(dq-boundary@dq@boundary)
                force_support_error = sparse_max(dp-boundary@dp@boundary)
                assert rate_support_error < 8e-14
                assert force_support_error < 8e-14
                matrix_checks.append(dict(R=R, compression_error=compression_error,
                    diagonal_commutator_error=diagonal_commutator_error,
                    cross_commutator_error=cross_commutator_error,
                    rate_support_error=rate_support_error, force_support_error=force_support_error))
            p0 = float(np.vdot(psi, P @ psi).real)
            q0 = float(np.vdot(psi, Q @ psi).real)
            rate = float((1j*np.vdot(psi, (H @ Q-Q @ H) @ psi)).real)
            for t in [0.25, 0.5, 1.0]:
                evolved = sla.expm_multiply(-1j*t*H, psi, traceA=-1j*t*H.diagonal().sum())
                qmean = float(np.vdot(evolved, Q @ evolved).real)
                pmean = float(np.vdot(evolved, P @ evolved).real)
                target = q0+p0*t
                top_weight = float(np.sum(abs(evolved[numbers >= R-1])**2))
                assert abs(np.vdot(evolved, evolved)-1) < 5e-12
                rows.append(dict(R=R, full_dimension=dim, repair=name, time=t,
                                 initial_clock_momentum=p0, initial_rate=rate,
                                 initial_rate_error=abs(rate-p0), position=qmean,
                                 canonical_position=target, position_error=abs(qmean-target),
                                 calibrated_time_error=abs(qmean-target)/abs(p0),
                                 momentum_drift=abs(pmean-p0), top_two_sector_probability=top_weight))
            print(f'R={R} {name}, t=1 position error={rows[-1]["position_error"]:.6g}', flush=True)
    for R in [8, 16]:
        selected = {row['repair']:row for row in rows if row['R'] == R and row['time'] == 0.5}
        assert selected['first_order']['position_error'] < selected['bare']['position_error']
        assert selected['second_order']['position_error'] < selected['first_order']['position_error']
        assert selected['exact']['position_error'] < selected['second_order']['position_error']
    return rows, matrix_checks


def main():
    root = Path(__file__).resolve().parents[1]
    exact = exact_algebra()
    cases, matrix_checks = run()
    report = dict(exact=exact, cases=cases, matrix_checks=matrix_checks, scope=(
        'All six active flavors and the full symmetric block are retained. '
        'The initial spin-coherent state is identical across repairs. Both '
        'the clock Hamiltonian and its coordinate/momentum readout change. '
        'First- and second-order repairs have fixed collective polynomial '
        'degree; exact inverse-square-root compensation and its top-sector '
        'projector generally require growing microscopic interaction order. '
        'The remaining exact-compensation error is finite-boundary error. '
        'This is not a tensor-lattice clock factorization or Einstein limit.'))
    sources = ['scripts/spin_clock_repair_audit.py', 'scripts/holomorphic_tensor_phase_audit.py',
               'UnifiedTheory/Audit/KFCausalSpinClockRepair.lean']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    target = root/'data/spin_clock_repair_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, flush=True)


if __name__ == '__main__':
    main()
