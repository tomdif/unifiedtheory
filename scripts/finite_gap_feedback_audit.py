#!/usr/bin/env python3
"""Finite-gap feedback audit; finite matrices do not remove field regulators."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy

B = .4
D = .31
KAPPA = .25
OMEGA = np.sqrt(D*D+4*B*B)
P = (1-D/OMEGA)/2
ALPHA2 = P*(1-P)
NUMBER = np.diag([0., 1.])
GEO = np.array([[(OMEGA-D)/2, -B], [-B, (OMEGA+D)/2]])


def switch(lam, force):
    radius = np.hypot(lam*D+force, 2*lam*B)
    # Rationalization avoids cancellation when force is tiny.
    energy = (2*lam*(OMEGA-D)*force)/(2*(lam*OMEGA+force+radius))
    if abs(lam*OMEGA+force+radius) < 1e-8*radius:
        energy = (lam*OMEGA+force-radius)/2
    occupation = (1-(lam*D+force)/radius)/2
    return energy, occupation, radius


def symbolic_identities():
    a, b, c, d, k, q, lam, gap, bias, mix = sy.symbols(
        'a b c d k q lam gap bias mix', real=True)
    F = k*(a-d)*(b-c)
    original = k*((a-c)**2+(b-d)**2-(a-b)**2-(c-d)**2)/2
    grad2 = sum(sy.diff(F, x)**2 for x in [a, b, c, d])
    assert sy.expand(F-original) == 0
    assert sy.expand(grad2-2*k*k*((a-d)**2+(b-c)**2)) == 0
    # Differential double commutator, tested on an arbitrary function.
    psi = sy.Function('psi')(a, b, c, d)
    kinetic = lambda f: -3*k*sum(sy.diff(f, x, 2) for x in [a, b, c, d])
    commutator = 2*F*kinetic(F*psi)-F**2*kinetic(psi)-kinetic(F**2*psi)
    assert sy.simplify(commutator-6*k*grad2*psi) == 0
    force = sy.symbols('force', real=True)
    rad = sy.sqrt((lam*bias+force)**2+4*lam**2*mix**2)
    e = (lam*gap+force-rad)/2
    assert sy.simplify(sy.diff(e, force, 2)+2*lam**2*mix**2/rad**3) == 0
    assert sy.simplify(sy.diff(e, force, 3)-6*lam**2*mix**2*(lam*bias+force)/rad**5) == 0
    return dict(motif_factorization=True, gradient_norm=True,
                differential_double_commutator=True, response_derivatives=True)


def static_response():
    rows = []
    for lam in [.5, 1., 4., 16.]:
        for ratio in [-.5, -.2, -.01, 0., .01, .2, .5]:
            f = ratio*lam*OMEGA
            e, occ, rad = switch(lam, f)
            eig, vec = la.eigh(lam*GEO+f*NUMBER)
            energy_error = abs(e-(P*f-ALPHA2*f*f/(lam*OMEGA)))
            occupancy_error = abs(occ-(P-2*ALPHA2*f/(lam*OMEGA)))
            e_bound = 16*B*B*abs(f)**3/(lam*lam*OMEGA**4)
            n_bound = 48*B*B*f*f/(lam*lam*OMEGA**4)
            assert abs(e-eig[0]) < 1e-12
            assert abs(occ-abs(vec[1, 0])**2) < 1e-12
            assert abs(rad-(eig[1]-eig[0])) < 1e-12
            assert rad >= 2*lam*B-1e-14
            assert energy_error <= e_bound+1e-13
            assert occupancy_error <= n_bound+1e-13
            rows.append(dict(geometry_scale=lam, force_over_gap=ratio, exact_energy=float(e),
                             active_probability=float(occ), switch_gap=float(rad),
                             energy_remainder=float(energy_error), energy_bound=float(e_bound),
                             occupancy_remainder=float(occupancy_error), occupancy_bound=float(n_bound)))
    rng = np.random.default_rng(1907)
    worst = 1.
    for scale in [1e-3, .1, 1., 10., 1e3]:
        for _ in range(100):
            x = scale*rng.normal(size=4)
            v0 = KAPPA*np.sum(np.diff(x)**2)/2
            f = KAPPA*(x[0]-x[3])*(x[1]-x[2])
            energy, _, rad = switch(1., f)
            exact = v0+energy
            worst = min(worst, exact/v0)
            assert exact >= v0/4-1e-9
            assert rad >= 2*B
    amplitude = 100.
    x = amplitude*np.arange(4.)
    v0 = KAPPA*np.sum(np.diff(x)**2)/2
    f = KAPPA*(x[0]-x[3])*(x[1]-x[2])
    exact = v0+switch(1., f)[0]
    quartic = v0+P*f-ALPHA2*f*f/OMEGA
    assert exact > 0 and quartic < 0
    return dict(taylor_rows=rows, random_stability_cases=500,
                smallest_potential_to_reference_ratio=float(worst),
                large_strain_example=dict(force=float(f), exact_potential=float(exact),
                                          truncated_potential=float(quartic)))


def derivative_compression():
    rng = np.random.default_rng(2009)
    maximum_error = 0.
    for lam in [1., 4., 16.]:
        for _ in range(12):
            x = rng.normal(size=4)
            f = KAPPA*(x[0]-x[3])*(x[1]-x[2])
            grad = KAPPA*np.array([x[1]-x[2], x[0]-x[3], -x[0]+x[3], -x[1]+x[2]])
            rad = switch(lam, f)[2]
            predicted = (lam*B)**2*np.dot(grad, grad)/rad**4
            def ground(y):
                force = KAPPA*(y[0]-y[3])*(y[1]-y[2])
                theta = np.arctan2(2*lam*B, lam*D+force)
                return np.array([np.cos(theta/2), np.sin(theta/2)])
            gs = ground(x)
            measured = 0.
            for i in range(4):
                dx = np.eye(4)[i]*1e-5
                dg = (ground(x+dx)-ground(x-dx))/(2e-5)
                assert abs(np.dot(gs, dg)) < 1e-10
                measured += np.dot(dg, dg)
            error = abs(measured-predicted)
            maximum_error = max(maximum_error, error)
            assert error < 1e-9
    return dict(cases=36, largest_derivative_norm_error=float(maximum_error),
                interpretation='Exact ground-channel compression; its range is not dynamically invariant.')


def retarded_response():
    times = np.linspace(0., 12., 181)
    response_rows = []
    eig, vec = la.eigh(GEO)
    g = vec[:, 0]
    for force in [.008, .004, .002, .001]:
        values, vectors = la.eigh(GEO+force*NUMBER)
        initial = vectors.conj().T@g
        errors = []
        for time in times:
            psi = vectors@(np.exp(-1j*time*values)*initial)
            exact = abs(psi[1])**2-P
            linear = -2*ALPHA2*force*(1-np.cos(OMEGA*time))/OMEGA
            errors.append(abs(exact-linear))
        response_rows.append(dict(source=force, largest_linear_response_error=float(max(errors)),
                                  error_over_source_squared=float(max(errors)/force**2)))
    assert response_rows[-1]['largest_linear_response_error'] < response_rows[0]['largest_linear_response_error']/40
    n_eigen = vec.conj().T@NUMBER@vec
    operators = []
    for j in range(3):
        factors = [np.eye(2) for _ in range(3)]
        factors[j] = n_eigen
        op = factors[0]
        for factor in factors[1:]:
            op = np.kron(op, factor)
        operators.append(op)
    energies = OMEGA*np.array([bin(i).count('1') for i in range(8)])
    max_error = 0.
    for time in [.1, 1.1, 2.3]:
        for s, r in itertools.product(range(3), repeat=2):
            n_time = np.exp(1j*time*energies)[:, None]*operators[s]*np.exp(-1j*time*energies)[None, :]
            kernel = (-1j*(n_time@operators[r]-operators[r]@n_time))[0, 0]
            expected = -2*ALPHA2*np.sin(OMEGA*time) if s == r else 0.
            max_error = max(max_error, abs(kernel-expected))
            assert abs(kernel-expected) < 1e-13
    return dict(step_source_rows=response_rows, independent_switches=3,
                commutator_cases=27, largest_kernel_error=float(max_error),
                bare_pole_frequency=float(OMEGA), spatially_diagonal=True,
                static_susceptibility=float(-2*ALPHA2/OMEGA))


def occupation_basis(modes, maximum):
    def fixed(total, count):
        if count == 1:
            yield (total,)
        else:
            for value in range(total+1):
                for rest in fixed(total-value, count-1):
                    yield (value,)+rest
    return [x for total in range(maximum+1) for x in fixed(total, modes)]


def oscillator_motifs(maximum):
    # Two disjoint four-vertex path motifs. Extra levels implement compression
    # of the full degree-two polynomials, not squaring truncated q matrices.
    modes = 8
    basis = occupation_basis(modes, maximum+2)
    lookup = {state: i for i, state in enumerate(basis)}
    dim = len(occupation_basis(modes, maximum))
    qs, momenta = [], []
    for mode in range(modes):
        row, col, value = [], [], []
        for j, state in enumerate(basis):
            if state[mode]:
                dest = list(state)
                dest[mode] -= 1
                row.append(lookup[tuple(dest)])
                col.append(j)
                value.append(np.sqrt(state[mode]))
        annih = sp.csr_matrix((value, (row, col)), shape=(len(basis), len(basis)))
        qs.append((annih+annih.T)/np.sqrt(2))
        momenta.append((annih-annih.T)/(1j*np.sqrt(2)))
    compress = lambda op: np.real_if_close(op[:dim, :dim].toarray())
    kinetic = sum(3*KAPPA*(pi@pi) for pi in momenta)
    potential = sum(KAPPA*((qs[j]-qs[j+1])@(qs[j]-qs[j+1]))/2
                    for j in [0, 1, 2, 4, 5, 6])
    forces = [compress(KAPPA*((qs[j]-qs[j+3])@(qs[j+1]-qs[j+2]))) for j in [0, 4]]
    return compress(kinetic+potential), forces


def cutoff_elimination():
    output = []
    n = np.array([[P, np.sqrt(ALPHA2)], [np.sqrt(ALPHA2), 1-P]])
    for cutoff in [2, 3]:
        href, forces = oscillator_motifs(cutoff)
        dim = href.shape[0]
        V = np.kron(np.eye(4), href)+np.kron(np.kron(n, np.eye(2)), forces[0])+np.kron(np.kron(np.eye(2), n), forces[1])
        assert la.norm(V-V.T) < 1e-12
        veigs = la.eigvalsh(V)
        assert veigs[0] >= 0
        v = float(veigs[-1])
        A, off, C = V[:dim, :dim], V[:dim, dim:], V[dim:, dim:]
        beta = float(la.svdvals(off)[0])
        a_expected = href+P*(forces[0]+forces[1])
        assert la.norm(A-a_expected) < 1e-12
        geometry_levels = np.repeat([0., 1., 1., 2.], dim)
        samples = []
        for lam in [64., 128., 256., 512.]:
            gap = lam*OMEGA
            assert gap > 2*v
            d_inv = 1/(gap*geometry_levels[dim:])
            first = (off*d_inv)@off.T
            expected = ALPHA2*(forces[0]@forces[0]+forces[1]@forces[1])/gap
            assert la.norm(first-expected) < 1e-12
            H1 = A-first
            Z = np.eye(dim)+(off*d_inv**2)@off.T
            kval = H1+(off*d_inv)@C@(off*d_inv).T
            z_eig, z_vec = la.eigh(Z)
            zinv = (z_vec*(1/np.sqrt(z_eig)))@z_vec.T
            H2 = zinv@kval@zinv
            full = V+np.diag(gap*geometry_levels)
            exact_eig, exact_vec = la.eigh(full, subset_by_index=[0, 5])
            mean_eig = la.eigvalsh(A)
            first_eig = la.eigvalsh(H1)
            second_eig = la.eigvalsh(H2)
            w = 2*v
            bound1 = beta**2*w/(gap*(gap-w))
            bound2 = beta**2*w*w/(gap*gap*(gap-w))
            errors1, errors2, residuals1, residuals2 = [], [], [], []
            for idx, energy in enumerate(exact_eig):
                resolvent_off = la.solve(np.diag(1/d_inv)+C-energy*np.eye(3*dim), off.T, assume_a='pos')
                T = A-off@resolvent_off
                residuals1.append(float(la.norm(T-H1, 2)))
                approximated = kval-energy*Z
                residuals2.append(float(la.norm((T-energy*np.eye(dim))-approximated, 2)))
                assert residuals1[-1] <= bound1+1e-11
                assert residuals2[-1] <= bound2+1e-11
                u = exact_vec[:dim, idx]
                assert la.norm((T-energy*np.eye(dim))@u) < 1e-10
                errors1.append(float(np.min(abs(first_eig-energy))))
                errors2.append(float(np.min(abs(second_eig-energy))))
                assert errors1[-1] <= bound1+1e-11
                assert errors2[-1] <= bound2+1e-11
            samples.append(dict(geometry_scale=lam, gap=float(gap),
                                mean_ground_energy_error=float(abs(mean_eig[0]-exact_eig[0])),
                                first_spectral_distance=max(errors1), second_spectral_distance=max(errors2),
                                first_operator_remainder=max(residuals1), second_operator_remainder=max(residuals2),
                                first_bound=float(bound1), second_bound=float(bound2),
                                exact_lowest_energy=float(exact_eig[0])))
        assert samples[-1]['first_spectral_distance'] < samples[0]['first_spectral_distance']/40
        assert samples[-1]['second_spectral_distance'] < samples[0]['second_spectral_distance']/250
        output.append(dict(total_occupation_cutoff=cutoff, field_dimension=dim,
                           joint_dimension=4*dim, interaction_norm=v, off_diagonal_norm=beta,
                           samples=samples))
    return output


def continuum_scaling():
    rows = []
    ell, slope, lam = 12, .7, 4.
    for spacing in [.1, .05, .025, .0125]:
        x = spacing*slope*(spacing*np.arange(4.))
        force = KAPPA*(x[0]-x[3])*(x[1]-x[2])
        assert abs(force-3*KAPPA*spacing**4*slope*slope) < 1e-16
        density = -ALPHA2*force*force/(lam*OMEGA*ell**3*spacing**4)
        expected = -9*ALPHA2*KAPPA*KAPPA*spacing**4*slope**4/(lam*OMEGA*ell**3)
        assert abs(density-expected) < 1e-18
        grad2 = 2*KAPPA*KAPPA*((x[0]-x[3])**2+(x[1]-x[2])**2)
        bh = 3*KAPPA*B*B*grad2/(lam*lam*OMEGA**4*ell**3*spacing**4)
        bh_expected = 60*KAPPA**3*B*B*slope*slope/(lam*lam*OMEGA**4*ell**3)
        assert abs(bh-bh_expected) < 1e-17
        rows.append(dict(spacing=spacing, quartic_macroscopic_test_density=float(density),
                         quadratic_compression_test_density=float(bh),
                         fixed_gap_in_macroscopic_units=float(lam*OMEGA/spacing),
                         gap_if_Lambda_equals_a_fourth=float(OMEGA*spacing**3)))
    return dict(rows=rows, scope='Smooth affine test coordinates; not a quantum continuum or homogenized coefficient.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(parameters=dict(b=B, d=D, kappa=KAPPA, omega=float(OMEGA), p=float(P)),
                  symbolic=symbolic_identities(), static=static_response(),
                  derivative_compression=derivative_compression(), retarded_response=retarded_response(),
                  cutoff_quantum_elimination=cutoff_elimination(), continuum_test=continuum_scaling())
    sources = ['FINITE_GAP_GEOMETRY_FEEDBACK.md', 'scripts/finite_gap_feedback_audit.py',
               'UnifiedTheory/Audit/KFCausalFiniteGapFeedback.lean', 'COLLECTIVE_WAVE_SPACETIME.md',
               'scripts/collective_wave_audit.py', 'UnifiedTheory/Audit/KFCausalCollectiveWave.lean',
               'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md', 'scripts/projected_geometry_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    report['scope'] = ('Exact static and bare retarded switch response; exact ground-channel compression; '
                       'finite-cutoff quantum spectral bounds. No regulator-uniform quantum limit, '
                       'new massless tensor mode, original spin-half phase, or Einstein equation established.')
    (root/'data/finite_gap_feedback_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
