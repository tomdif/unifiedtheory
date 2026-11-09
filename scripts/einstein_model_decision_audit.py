#!/usr/bin/env python3
"""Classical metric reconstruction and coordinate checks, not emergent gravity."""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy


def basis():
    out = [np.eye(3)/np.sqrt(3), np.diag([1., -1., 0.])/np.sqrt(2),
           np.diag([1., 1., -2.])/np.sqrt(6)]
    for i, j in [(0, 1), (1, 2), (0, 2)]:
        x = np.zeros((3, 3)); x[i, j] = x[j, i] = 1/np.sqrt(2)
        out.append(x)
    return np.array(out)


def exact_density_identities():
    z = sy.symbols('q0:6', real=True)
    q = sy.Matrix([[z[0], z[3], z[5]], [z[3], z[1], z[4]], [z[5], z[4], z[2]]])
    c = q.adjugate(); det = q.det()
    assert sy.expand(c.det()-det**2) == 0
    assert (c.adjugate()-det*q).applyfunc(sy.expand) == sy.zeros(3)
    b = sy.Matrix(3, 3, sy.symbols('b0:9', real=True))
    dq = b.T*q+q*b
    dz = [dq[0, 0], dq[1, 1], dq[2, 2], dq[0, 1], dq[1, 2], dq[0, 2]]
    dc = sy.zeros(3)
    for zi, dzi in zip(z, dz):
        dc += c.diff(zi)*dzi
    target = 2*sy.trace(b)*c-b*c-c*b.T
    assert (dc-target).applyfunc(sy.expand) == sy.zeros(3)
    return dict(determinant_identity=True, adjugate_reconstruction=True,
                density_transformation=True,
                scope='Exact polynomial identities for commuting classical components. Positivity is required to choose the positive square root for metric reconstruction.')


def matrix_checks():
    es = basis()
    vec = lambda a: np.einsum('aij,ij->a', es, a)
    mat = lambda v: np.einsum('a,aij->ij', v, es)
    rng = np.random.default_rng(9140)
    hs = [np.zeros((3, 3)), .6*np.eye(3), np.diag([.4, .4, -.7])]
    hs += [mat(rng.normal(size=6)*.55) for _ in range(80)]
    rows = []
    symplectic = np.block([[np.zeros((6, 6)), np.eye(6)], [-np.eye(6), np.zeros((6, 6))]])
    for case, h in enumerate(hs):
        q = la.expm(h); determinant = float(la.det(q))
        c = determinant*la.inv(q)
        recovered = np.sqrt(la.det(c))*la.inv(c)
        reconstruction = float(la.norm(q-recovered))
        assert reconstruction < 1e-11
        jac = np.column_stack([vec(la.expm_frechet(h, e, compute_expm=False)) for e in es])
        assert la.norm(jac-jac.T) < 1e-11
        assert la.eigvalsh(jac)[0] > 0
        pi, dh = rng.normal(size=(2, 6))
        canonical = abs(float(pi@(jac@dh)-(jac.T@pi)@dh))
        assert canonical < 1e-11
        b = rng.normal(size=(3, 3))*.4
        target = b.T@q+q@b
        f = mat(la.solve(jac, vec(target), assume_a='pos'))
        eig, u = la.eigh(h)
        bhat = u.T@b@u
        s, a = (bhat+bhat.T)/2, (bhat-bhat.T)/2
        gap = eig[:, None]-eig[None, :]
        weight = np.empty_like(gap)
        small = abs(gap) < 1e-7
        weight[small] = 2+gap[small]**2/6
        weight[~small] = gap[~small]/np.tanh(gap[~small]/2)
        independent = u@(weight*s+gap*a)@u.T
        spatial = float(la.norm(f-independent))
        assert spatial < 1e-10
        sigma = .7
        dilation = float(la.norm(mat(la.solve(jac, vec(2*sigma*q)))-2*sigma*np.eye(3)))
        assert dilation < 1e-10
        def log_symmetric(x):
            ev, uu = la.eigh(x)
            assert ev[0] > 0
            return (uu*np.log(ev))@uu.T
        dt = 2e-5
        gp, gm = la.expm(dt*b), la.expm(-dt*b)
        measured = (log_symmetric(gp.T@q@gp)-log_symmetric(gm.T@q@gm))/(2*dt)
        finite_difference = float(la.norm(measured-f))
        assert finite_difference < 1e-7
        # A canonical coordinate change preserves the linearized frequencies.
        change = la.block_diag(jac, la.inv(jac).T)
        symplectic_error = float(la.norm(change.T@symplectic@change-symplectic))
        assert symplectic_error < 1e-10
        frequencies = np.arange(1., 7.)*.31
        old_energy = la.block_diag(np.diag(frequencies**2), np.eye(6))
        new_energy = change.T@old_energy@change
        old_flow, new_flow = symplectic@old_energy, symplectic@new_energy
        similarity = float(la.norm(new_flow-la.solve(change, old_flow@change)))
        spectrum = np.sort(la.eigvals(new_flow).imag)
        spectral_error = float(np.max(abs(spectrum-np.sort(np.r_[-frequencies, frequencies]))))
        assert similarity < 1e-9 and spectral_error < 1e-9
        # Congruence cannot remove the negative trace direction either.
        dewitt = np.diag([-.5, 1., 1., 1., 1., 1.])
        transformed = la.inv(jac)@dewitt@la.inv(jac).T
        assert np.sum(la.eigvalsh(transformed) < 0) == 1
        rows.append(dict(case=case, metric_reconstruction_error=reconstruction,
                         canonical_pairing_error=canonical, spatial_map_error=spatial,
                         dilation_error=dilation, congruence_derivative_error=finite_difference,
                         symplectic_error=symplectic_error, linear_flow_similarity_error=similarity,
                         unchanged_frequency_error=spectral_error))
    return dict(cases=len(rows), includes_repeated_eigenvalues=True,
                maxima={k:max(r[k] for r in rows) for k in rows[0] if k != 'case'},
                rows=rows,
                scope='Classical six-component coordinate and local spatial-action checks. These do not construct finite-spin spatial generators, constrain physical modes, or establish a gravitational phase.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_density_identities=exact_density_identities(), matrices=matrix_checks())
    sources = ['EINSTEIN_MODEL_DECISION.md', 'scripts/einstein_model_decision_audit.py',
               'SPIN_CLOCK_BRACKET.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'BOND_TENSOR_CONSTRAINTS.md', 'MICROSCOPIC_SPIN_TWO_SEED.md', 'LOCAL_CAUSAL_CLOCK.md']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = 'Model assessment and checked classical coordinate identities; no new microscopic Einstein-gravity or TOE proof, and no new Lean theorem.'
    (root/'data/einstein_model_decision_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
