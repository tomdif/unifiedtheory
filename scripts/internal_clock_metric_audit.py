#!/usr/bin/env python3
"""Internal-clock and reconstructed-metric tests, with explicit scope.

Separates the canonical energy-shell clock, complete finite-spin packet
diagnostics, and the exact reduced lattice reconstruction. No claim of
an Einstein phase or a uniform spin/volume limit is made.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla
from scipy.integrate import solve_ivp
import sympy as sy

from holomorphic_tensor_phase_audit import finite_operators


def exact_checks():
    # Actual seven-state cell algebra underlying the coherent-block clock.
    qcell, pcell = [], []
    for i in range(1, 7):
        lower = sy.zeros(7)
        lower[0, i] = 1
        qcell.append((lower+lower.T)/sy.sqrt(2))
        pcell.append((lower-lower.T)/(sy.I*sy.sqrt(2)))
    square_sum = sum((p*p for p in pcell), sy.zeros(7))
    comm_sum = sy.I*(square_sum*qcell[0]-qcell[0]*square_sum)
    assert comm_sum == -sy.Rational(5, 2)*pcell[0]
    z = sy.symbols('z', real=True)
    psi = sy.Matrix([1, sy.I*z, 0, 0, 0, 0, 0])/sy.sqrt(1+z*z)
    expectation = lambda A: sy.simplify((sy.conjugate(psi).T*A*psi)[0])
    assert expectation(pcell[0]) == sy.sqrt(2)*z/(1+z*z)
    assert expectation(sy.I*(pcell[0]*qcell[0]-qcell[0]*pcell[0])) == (1-z*z)/(1+z*z)
    for i in range(1, 6):
        assert expectation(pcell[i]) == 0
    a, b, c, d, da, db, dc, dd, rho, k, mass = sy.symbols(
        'a b c d da db dc dd rho k mass', real=True)
    S = sy.Matrix([[a, b], [c, d]])
    dotS = sy.Matrix([[da, db], [dc, dd]])
    parent = sy.Matrix([[0, 1], [-k, 0]])
    target = sy.Matrix([[0, 1], [-k-mass, 0]])
    residual = dotS+rho*S*parent-target*S
    expected = sy.Matrix([[da-rho*b*k-c, db+rho*a-d],
                          [dc-rho*d*k+(k+mass)*a, dd+rho*c+(k+mass)*b]])
    assert (residual-expected).applyfunc(sy.expand) == sy.zeros(2)
    # Matching the k coefficient forces b=0, rho*d=a. Differentiating
    # b=0 gives db=0, hence d=rho*a. Symplecticity and rho>0 force
    # rho=1, a=+/-1. Differentiating a^2=1 gives da=0; then c=dc=0.
    assert residual.subs({a:1, b:0, c:0, d:1, da:0, db:0, dc:0, dd:0, rho:1}) == sy.Matrix([[0, 0], [mass, 0]])
    t = sy.symbols('t', positive=True)
    E, h = sy.symbols('E h', positive=True)
    root = sy.symbols('root', nonnegative=True)
    rate = 2*(E-root)
    assert sy.rem(sy.expand(4*E*(rate-h)-rate**2), root**2-E*(E-h), root) == 0
    # The autonomous positive interaction needed by the rescaled target.
    T, Pc, M, u, v, omega2 = sy.symbols('T Pc M u v omega2', positive=True)
    H = Pc**2/(2*M)+(v**2+omega2*u**2)/2+u**2/(8*T**2)
    assert sy.diff(H, Pc) == Pc/M
    assert -sy.diff(H, T) == u**2/(4*T**3)
    assert -sy.diff(H, u) == -omega2*u-u/(4*T**2)
    return dict(canonical_intertwiner_coefficients=True, clock_defect_identity=True,
                exact_seven_state_clock_commutators=True,
                coherent_block_rate_ratio='((R-1)/R)*((R-n)/(R+n))-5/(4R), n=|alpha|^2',
                required_positive_clock_interaction='u^2/(8*T^2)',
                interaction_clock_force='u^2/(4*T^3)',
                scope=('The required autonomous interaction is a proposed model change. '
                       'It exerts a clock force; treating T as an exact prescribed time '
                       'would omit backreaction. The Lean obstruction concerns pointwise '
                       'linear canonical maps and monotone time changes of the massless free parent.'))


def canonical_clock():
    rows = []
    for sites in [8, 32, 128]:
        k = 2*np.pi*np.arange(1, sites)/sites
        # One-quantum energies of both nonzero tensor polarizations, in
        # the canonical massless comparison; subtract the vacuum energy.
        energies = np.repeat(2*np.sin(k/2), 2)
        emax = float(energies.max())
        for total_energy in [10., 100., 1000.]:
            # Stable rationalized form of 2E(1-sqrt(1-h/E)).
            rate = 2*energies/(1+np.sqrt(1-energies/total_energy))
            defect = rate-energies
            assert np.max(abs(defect-rate**2/(4*total_energy))) < 2e-15
            for time in [0.5, 2.]:
                error = float(np.max(abs(np.exp(-1j*time*rate)-np.exp(-1j*time*energies))))
                bound = time*emax**2/total_energy
                assert error <= bound+1e-13
                rows.append(dict(sites=sites, energy_band_dimension=len(energies),
                                 total_energy=total_energy, time=time,
                                 entire_band_operator_error=error, bound=bound))
    return dict(cases=rows, scope=(
        'Exact diagonal conditional evolution for a canonical free clock on a fixed '
        'total-energy shell. These are generalized stationary clock states. '
        'This is not a preparation or conditioning theorem for finite-R spin packets. '
        'The bound depends on total system energy, not on the number of modes.'))


def finite_spin_clock():
    rows = []
    alpha = 0.75j
    U = 1.
    for R in [2, 4, 8, 16]:
        states, ann = finite_operators(6, 6, R, R)
        dim = math.comb(R+6, 6)
        assert len(states) == dim
        Q = (ann[0]+ann[0].T)/math.sqrt(2)
        P = [(a-a.T)/(1j*math.sqrt(2)) for a in ann]
        H = sum((U/2*(p @ p) for p in P), sp.csr_matrix((dim, dim), dtype=complex))
        # Exact normalized symmetric spin coherent state with all other
        # excitation flavors initially empty; evolution retains every flavor.
        z = alpha/math.sqrt(R)
        psi = np.zeros(dim, dtype=complex)
        for i, state in enumerate(states):
            if any(state[1:]):
                continue
            n = state[0]
            psi[i] = math.sqrt(math.comb(R, n))*z**n/(1+abs(z)**2)**(R/2)
        assert abs(np.vdot(psi, psi)-1) < 2e-14
        p0 = float(np.vdot(psi, P[0] @ psi).real)
        derivative = float((1j*np.vdot(psi, (H @ Q-Q @ H) @ psi)).real)
        n = abs(alpha)**2
        exact_ratio = (R-1)/R*(R-n)/(R+n)-5/(4*R)
        rate_bound = (2*n+9/4)/R
        assert abs(derivative-U*p0*exact_ratio) < 3e-13
        assert 0 <= 1-exact_ratio <= rate_bound
        time = 0.5
        evolved = sla.expm_multiply(-1j*time*H, psi, traceA=-1j*time*H.diagonal().sum())
        qmean = float(np.vdot(evolved, Q @ evolved).real)
        target = U*p0*time
        rows.append(dict(R=R, full_collective_dimension=dim, full_space_retained=True,
                         initial_momentum=p0, initial_clock_rate=derivative,
                         canonical_initial_rate=U*p0, exact_rate_ratio=exact_ratio,
                         relative_initial_rate_error=1-exact_ratio,
                         relative_initial_rate_bound=rate_bound, time=time,
                         clock_position=qmean, canonical_clock_position=target,
                         position_error=abs(qmean-target)))
        assert abs(np.vdot(evolved, evolved)-1) < 1e-12
        print(f'finite spin clock R={R}, dimension={dim}, error={abs(qmean-target):.6g}', flush=True)
    assert rows[-1]['position_error'] < rows[0]['position_error']
    return dict(cases=rows, scope=(
        'Complete six-flavor symmetric block, massless homogeneous kinetic Hamiltonian '
        'U sum P_alpha^2/2. This probes the actual collective spin clock mechanism '
        'on normalizable states. It is a one-block diagnostic with zero tensor penalty, '
        'not a finite-volume tensor-clock factorization or a uniform R theorem.'))


def periodic_metric():
    rows = []
    c, k = 1.3, 0.7
    for N in [8, 16, 32, 64, 128]:
        spacing = 2*np.pi/N
        x = spacing*np.arange(N)
        q = 0.2*np.cos(x)+0.1*np.sin(2*x)
        p = 0.4*q+0.07
        qnext, qprev = np.roll(q, -1), np.roll(q, 1)
        pnext, pprev = np.roll(p, -1), np.roll(p, 1)
        dq = (qnext-qprev)/(2*spacing)
        source = spacing*p*dq/c
        qdot = p/c
        pdot = k*(qnext-2*q+qprev)/(c*spacing**2)
        source_dot = (pdot*(qnext-qprev)+p*(pnext-pprev)/c)/(2*c)
        flux = (k*(qnext-q)**2/spacing**2+p*pnext)/(2*c**2)-0.5
        residual = float(np.max(abs(source_dot-(flux-np.roll(flux, 1)))))
        assert residual < 2e-13
        assert abs(source.sum()) < 2e-15 and abs(source_dot.sum()) < 2e-14
        L = np.r_[0., np.cumsum(source)]
        Ldot = np.r_[flux[-1], flux[-1]+np.cumsum(source_dot)]
        assert np.max(abs(Ldot[:-1]-np.roll(flux, 1))) < 2e-13
        energy = spacing*np.sum((p*p+k*dq*dq)/(2*c))
        assert np.max(abs(L)) <= energy/math.sqrt(k)+1e-14
        rows.append(dict(sites=N, spacing=spacing, source_sum=float(source.sum()),
                         continuity_error=residual, metric_log_amplitude=float(np.max(abs(L))),
                         energy_bound=float(energy/math.sqrt(k))))
    return dict(cases=rows, scope=(
        'Constructed periodic longitudinal log metric for the supplied reduced momentum '
        'constraint. Exact discrete flux uses p_j p_(j+1), not p_j^2; a continuum '
        'Leibniz rule was not imposed on the lattice. Clock/Einstein selection is separate.'))


def autonomous_completion():
    omega2 = 1.0
    initial = np.array([0.2, 0.1])
    times = np.linspace(1., 3., 101)
    energy0 = (initial[1]**2+(omega2+0.25)*initial[0]**2)/2
    target = solve_ivp(lambda T, z: [z[1], -(omega2+1/(4*T*T))*z[0]],
                       (1., 3.), initial, t_eval=times, rtol=2e-12, atol=2e-14)
    assert target.success
    rows = []
    for M in [8., 32., 128., 512.]:
        pc0 = M*math.sqrt(1-2*energy0/M)

        def relational_rhs(T, state):
            u, v, pc = state
            w = pc/M
            return [v/w, -(omega2+1/(4*T*T))*u/w, u*u/(4*T**3*w)]

        sol = solve_ivp(relational_rhs, (1., 3.), [*initial, pc0], t_eval=times,
                        rtol=2e-12, atol=2e-14)
        assert sol.success
        u, v, pc = sol.y
        energy = (v*v+(omega2+1/(4*times**2))*u*u)/2
        total = pc*pc/(2*M)+energy
        conservation_error = float(np.max(abs(total-M/2)))
        rate_error = float(np.max(M/pc-1))
        bound = 4*energy0/M
        trajectory_error = float(np.max(np.linalg.norm(sol.y[:2]-target.y, axis=0)))
        assert conservation_error < 2e-9
        assert energy.max() <= energy0+1e-12
        assert np.min(np.diff(pc)) >= -1e-12
        assert rate_error <= bound
        rows.append(dict(clock_mass=M, initial_wave_energy=energy0,
                         maximum_clock_rate_error=rate_error, proved_rate_bound=bound,
                         trajectory_error=trajectory_error, total_energy_error=conservation_error))
    assert rows[-1]['trajectory_error'] < rows[0]['trajectory_error']/50
    return dict(cases=rows, scope=(
        'Revised positive canonical Hamiltonian with an explicit u^2/(8T^2) '
        'clock interaction. T and Pc are dynamical; their force and feedback '
        'are included. This is a one-mode numerical trajectory diagnostic, '
        'not an implementation in the original spin Hamiltonian or a '
        'frequency-uniform trajectory convergence theorem.'))


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact=exact_checks(), canonical_clock=canonical_clock(),
                  finite_spin_clock=finite_spin_clock(), periodic_metric=periodic_metric(),
                  autonomous_completion=autonomous_completion())
    sources = ['scripts/internal_clock_metric_audit.py',
               'scripts/holomorphic_tensor_phase_audit.py',
               'UnifiedTheory/Audit/KFCausalInternalClock.lean',
               'UnifiedTheory/Audit/KFCausalLocalClockObstruction.lean',
               'UnifiedTheory/Audit/KFCausalPeriodicMetricReconstruction.lean',
               'UnifiedTheory/Audit/KFCausalAutonomousArealClock.lean']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    target = root/'data/internal_clock_metric_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, flush=True)


if __name__ == '__main__':
    main()
