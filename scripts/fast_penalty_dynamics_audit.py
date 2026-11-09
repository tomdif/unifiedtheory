#!/usr/bin/env python3
"""Full finite-spin collective dynamics, and the separate areal-clock test.

The carrier is a periodic 1 x 2 x 1 lattice with all six tensor flavors.
Every occupation allowed by each block's finite R is retained. This is a
small-volume diagnostic, not a particle-cutoff extrapolation or a GR limit.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy

from compact_tensor_constraint_audit import stencil_symbols
from holomorphic_tensor_phase_audit import finite_operators


def thin_carrier_constraint():
    (_, _, _, gs, bs), _ = stencil_symbols()

    def matrix(stencil, rows, cols):
        out = np.zeros((2 * rows, 2 * cols))
        for y in range(2):
            for a, b, shift, value in stencil:
                out[2*a+y, 2*b+(y+shift[1]) % 2] += value
        return out

    weights = np.repeat([1, 1, 1, math.sqrt(2), math.sqrt(2), math.sqrt(2)], 2)
    G = weights[:, None] * matrix(gs, 6, 3)
    B = matrix(bs, 1, 6) / weights[None, :]
    order = [2*a+y for y in range(2) for a in range(6)]
    C = np.vstack([G.T, B])[:, order]
    assert la.norm(B @ G) < 1e-12
    assert np.linalg.matrix_rank(C) == 4
    assert np.allclose(la.eigvalsh(C.T @ C), [0]*8 + [8, 8, 16, 32])
    return C


def finite_parent(R, C):
    states, ann = finite_operators(12, 6, R, 2*R)
    dimension = math.comb(R+6, 6)**2
    assert len(states) == dimension
    zero = sp.csr_matrix((dimension, dimension))
    checks = [sum((v*a for v, a in zip(row, ann) if v), zero) for row in C]
    D = sum((check.T @ check for check in checks), zero)
    Q = [(a+a.T)/math.sqrt(2) for a in ann]
    p_im = [(a-a.T)/math.sqrt(2) for a in ann]
    U, r, g = 1.0, 0.4, 0.2
    F = sum((r/2*(q @ q)-U/2*(p @ p) for q, p in zip(Q, p_im)), zero)
    # Two directed positive-axis bonds of the periodic two-site y circle.
    for a in range(6):
        edge = Q[a]-Q[6+a]
        F += g * (edge @ edge)
    numbers = np.array([[sum(s[:6]), sum(s[6:])] for s in states])
    c = min(U, r)
    guard = np.sum(c*5*numbers/(2*R)+c*numbers**3/R**2, axis=1)
    F += sp.diags(guard)
    return D.toarray(), F.toarray(), states


def opnorm(A):
    return float(la.svdvals(A)[0])


def finite_dynamics():
    C = thin_carrier_constraint()
    cases = []
    for R in [1, 2]:
        D, F, states = finite_parent(R, C)
        d, v = la.eigh(D)
        zero = abs(d) < 1e-9
        assert d.min() > -1e-10
        J, W = v[:, zero], v[:, ~zero]
        positive = d[~zero]
        assert positive.min() > 1e-6
        L = (W / positive) @ W.T
        P = J @ J.T
        K = J.T @ F @ J
        correction = L @ F @ J
        bare_residual = F @ J-J @ K
        inverse_error = opnorm(D @ L-(np.eye(len(D))-P))
        solve_error = opnorm(D @ correction-bare_residual)
        assert inverse_error < 2e-11 and solve_error < 2e-11
        assert opnorm(D @ J) < 2e-11
        eta = opnorm(correction)
        residual_numerator = correction @ K-F @ correction
        exact_coefficient = opnorm(residual_numerator)
        coefficient = eta*opnorm(K)+opnorm(F @ correction)
        assert exact_coefficient <= coefficient+1e-12
        kval, kvec = la.eigh(K)
        rows = []
        for multiplier in [1, 4, 16, 64, 256]:
            # H_R / epsilon_R = Gamma R^2 D_R + F_R.
            Gamma = float(multiplier)
            strength = Gamma*R**2
            H = strength*D+F
            dressed = J-correction/strength
            remainder = H @ dressed-dressed @ K
            identity_error = opnorm(remainder-residual_numerator/strength)
            assert identity_error < 2e-9
            hval, hvec = la.eigh(H)
            for t in [0.25, 1.0, 2.0]:
                UJ = hvec @ (np.exp(-1j*t*hval)[:, None]*(hvec.T @ J))
                JV = (J @ kvec) @ (np.exp(-1j*t*kval)[:, None]*kvec.T)
                error = opnorm(UJ-JV)
                sharp_bound = (2*eta+t*exact_coefficient)/strength
                lean_bound = (2*eta+t*coefficient)/strength
                assert error <= sharp_bound+2e-8
                rows.append(dict(Gamma=Gamma, penalty=strength, time=t,
                                 bare_evolution_error=error,
                                 lean_sharp_bound=sharp_bound,
                                 norm_triangle_bound=lean_bound,
                                 dressing_identity_error=identity_error))
        assert rows[-1]['bare_evolution_error'] < rows[2]['bare_evolution_error']/20
        cases.append(dict(R=R, dimension=len(D), kernel_dimension=J.shape[1],
                          full_collective_space=True, occupation_cutoff=False,
                          positive_constraint_gap=float(positive.min()),
                          partial_inverse_error=inverse_error,
                          correction_equation_error=solve_error,
                          bare_generator_residual=opnorm(bare_residual),
                          correction_norm=eta, residual_coefficient=exact_coefficient,
                          evolution_cases=rows))
        print(f'R={R}, full dimension={len(D)}, kernel={J.shape[1]}, '
              f'last evolution error={rows[-1]["bare_evolution_error"]:.6g}', flush=True)
    return dict(cases=cases, scope=(
        'Actual six-flavor collective spin operators and the original integer tensor stencils '
        'on a periodic 1x2x1 carrier. All allowed local occupations, including N_total>R, '
        'are retained. The target K=J*F_R J is computed from the entire finite-R kernel, '
        'not identified with the continuum areal Hamiltonian. Gamma varies at fixed R; '
        'these cases do not establish uniform R, volume, or continuum convergence. '
        'Floating-point spectral and norm checks are not certified interval bounds.'))


def clock_checks():
    t, c, r = sy.symbols('t c r', positive=True)
    q, p, qx, qxx = sy.symbols('q p qx qxx', real=True)
    # Canonical time-dependent rescaling after t=exp(tau).
    # u=sqrt(c*t)*q, v=p/sqrt(c*t)+u/(2*t).
    u, v, ux, uxx = sy.symbols('u v ux uxx', real=True)
    scale = sy.sqrt(c*t)
    forward = {u:scale*q, v:p/scale+scale*q/(2*t)}
    assert sy.simplify(sy.diff(forward[u], q)*sy.diff(forward[v], p)
                       -sy.diff(forward[u], p)*sy.diff(forward[v], q)) == 1
    udot = sy.diff(scale, t)*q+scale*p/(c*t)
    vdot = (r*t*qxx/c)/scale-p*sy.diff(scale, t)/scale**2+udot/(2*t)-scale*q/(2*t**2)
    inverse = {q:u/scale, p:scale*(v-u/(2*t)), qxx:uxx/scale}
    assert sy.simplify(udot.subs(inverse)-v) == 0
    assert sy.simplify(vdot.subs(inverse)-(r*uxx/c**2-u/(4*t**2))) == 0
    # An explicit smooth periodic reconstruction: Q=A cos(s), P=B cos(s).
    s, A, B = sy.symbols('s A B', real=True)
    Q, P = A*sy.cos(s), B*sy.cos(s)
    L = A*B*sy.cos(2*s)/(4*c)
    assert sy.simplify(sy.diff(L, s)-P*sy.diff(Q, s)/c) == 0
    assert sy.integrate(P*sy.diff(Q, s), (s, 0, 2*sy.pi)) == 0
    cost = sy.simplify(sy.integrate(4*sy.diff(L, s)**2, (s, 0, 2*sy.pi)))
    assert cost == sy.pi*A**2*B**2/c**2
    return dict(canonical_rescaling=True, transformed_hamilton_equations=True,
                transformed_mass_squared='1/(4*t^2)',
                periodic_reconstruction=True, total_momentum_zero=True,
                longitudinal_classical_symbol_cost=str(cost),
                scope=('Exact SymPy identities for the supplied continuum target. '
                       'The bare linear tensor penalty charges its nonlinear longitudinal '
                       'metric reconstruction, even with zero total momentum. This is a '
                       'classical-symbol cost, not a finite-spin quantum no-go theorem. '
                       'Composite/dressed metric observables and an internal clock remain possible.'))


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(finite_spin_dynamics=finite_dynamics(), areal_clock=clock_checks())
    sources = ['scripts/fast_penalty_dynamics_audit.py',
               'scripts/holomorphic_tensor_phase_audit.py',
               'scripts/compact_tensor_constraint_audit.py',
               'UnifiedTheory/Audit/KFCausalFastPenaltyDynamics.lean',
               'UnifiedTheory/Audit/KFCausalFinitePenaltyInverse.lean',
               'UnifiedTheory/Audit/KFCausalArealMicroscopicBridge.lean']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    destination = root/'data/fast_penalty_dynamics_audit.json'
    destination.write_text(json.dumps(report, indent=2)+'\n')
    print(destination, flush=True)


if __name__ == '__main__':
    main()
