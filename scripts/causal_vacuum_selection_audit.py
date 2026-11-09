#!/usr/bin/env python3
"""Conditional clock selection, with explicit shared-modular-data controls.

No finite-spin phase, microscopic common cone, nonlinear GR, or TOE is proved.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.integrate import quad
import sympy as sp


def positive_power(matrix, exponent):
    values, vectors = la.eigh(matrix)
    assert min(values) > 0
    return (vectors*values**exponent) @ vectors.T


def oscillator_covariance(a, b, thermal=False):
    """Canonical reduction of H=(p^T A p+q^T B q)/2, no commutation assumed."""
    ah, ai = positive_power(a, .5), positive_power(a, -.5)
    values, vectors = la.eigh(ah @ b @ ah)
    assert min(values) > 0
    omega = np.sqrt(values)
    occupation = 1/np.tanh(omega/2) if thermal else np.ones_like(omega)
    x = ah @ (vectors*(occupation/(2*omega))) @ vectors.T @ ah
    p = ai @ (vectors*(occupation*omega/2)) @ vectors.T @ ai
    return x, p, omega


def regional_modular(x, p):
    """Return q and p blocks of -log rho, excluding its additive constant."""
    xh, xi = positive_power(x, .5), positive_power(x, -.5)
    values, vectors = la.eigh(xh @ p @ xh)
    nu = np.sqrt(values)
    # No eigenvalue clipping: a pure or unresolved mode must fail explicitly.
    assert min(nu) > .5+1e-8
    epsilon = np.log((2*nu+1)/(2*nu-1))
    mq = xi @ (vectors*(nu*epsilon)) @ vectors.T @ xi
    mp = xh @ (vectors*(epsilon/nu)) @ vectors.T @ xh
    rx, rp, spectrum = oscillator_covariance(mp, mq, thermal=True)
    reconstruction = max(la.norm(rx-x), la.norm(rp-p))
    assert reconstruction < 2e-10
    assert la.norm(np.sort(spectrum)-np.sort(epsilon)) < 2e-10
    return mq, mp, nu, reconstruction


def modular_ring_checks():
    rows = []
    for size in [8, 12, 16]:
        for mass in [.15, .4]:
            shift = np.roll(np.eye(size), 1, axis=0)
            lap = (mass*mass+2)*np.eye(size)-shift-shift.T
            xa, pa, wa = oscillator_covariance(np.eye(size), lap)
            xb, pb, wb = oscillator_covariance(lap, lap @ lap)
            cov_error = max(la.norm(xa-xb), la.norm(pa-pb))
            # The cubic ring diagonalizes L^3 (condition number up to 5.8e6).
            # Cross-check against the analytic precision, retaining raw errors.
            reference_x = .5*positive_power(lap, -.5)
            reference_p = .5*positive_power(lap, .5)
            reference_error = max(la.norm(xa-reference_x), la.norm(xb-reference_x),
                                  la.norm(pa-reference_p), la.norm(pb-reference_p))
            assert cov_error < 1e-9
            assert reference_error < 1e-9
            assert la.norm(xa @ pa-.25*np.eye(size)) < 2e-11
            assert la.norm(wb-wa**3) < 3e-12
            for region in [2, 3]:
                ma, na, nu, rec = regional_modular(xa[:region, :region], pa[:region, :region])
                mb, nb, _, _ = regional_modular(xb[:region, :region], pb[:region, :region])
                modular_error = max(la.norm(ma-mb), la.norm(na-nb))
                assert modular_error < 3e-9
                # The common vacuum still has different Euclidean time correlations.
                ah = np.eye(size)
                bh = positive_power(lap, .5)
                vals, vecs = la.eigh(lap)
                corr_a = (vecs*(np.exp(-np.sqrt(vals))/(2*np.sqrt(vals)))) @ vecs.T
                corr_b = bh @ (vecs*(np.exp(-vals**1.5)/(2*vals**1.5))) @ vecs.T @ bh
                time_difference = la.norm(ah @ corr_a @ ah-corr_b)
                assert time_difference > .01
                rows.append(dict(size=size, mass=mass, region=region,
                                 covariance_error=float(cov_error),
                                 analytic_covariance_error=float(reference_error),
                                 modular_matrix_error=float(modular_error),
                                 minimum_regional_symplectic_eigenvalue=float(min(nu)),
                                 thermal_covariance_reconstruction_error=float(rec),
                                 unequal_time_covariance_difference=float(time_difference)))
    return dict(cases=rows, scope="Finite massive oscillator rings. Independent canonical ground-state and thermal modular reconstructions. Their local spatial factors are legitimate oscillator factors, not TT graviton regions or finite-spin phases.")


def finite_volume_checks():
    rows, c, cutoff, tilt = [], np.sqrt(.7*1.3), .8, .05
    for size in [16, 32, 64, 128, 256, 512, 1024]:
        k = 2*np.pi*np.arange(1, int(np.floor(cutoff*size/(2*np.pi)))+1)/size
        q = 2*np.sin(k/2)
        e1, e3 = c*q, c*q**3
        critical = min(e3/k)
        predicted = c*(2*np.sin(np.pi/size))**3/(2*np.pi/size)
        assert abs(critical-predicted) < 1e-14
        assert np.argmin(e3/k) == 0
        assert min(e1/k) >= c*(1-cutoff*cutoff/24)-1e-13
        assert max(e1/k) <= c+1e-13
        # A single excitation suffices; do not assume a finite-spin Fock space.
        witness = e3[0]-tilt*k[0]
        assert (witness < 0) == (critical < tilt)
        asymptotic_ratio = critical/(c*k[0]**2)
        assert 1-k[0]**2/8 <= asymptotic_ratio <= 1+1e-13
        # Illustrate why a merely vanishing absolute energy tolerance is inadequate.
        eps_weak, eps_strong = 1/np.sqrt(size), 1/size**2
        rows.append(dict(size=size, first_momentum=float(k[0]), tilt=tilt,
                         cubic_critical_velocity=float(critical),
                         cubic_first_tilted_energy=float(witness),
                         uniform_cone_counterexample=bool(witness < 0),
                         critical_velocity_asymptotic_ratio=float(asymptotic_ratio),
                         linear_minimum_phase_velocity_in_window=float(min(e1/k)),
                         weak_relative_spectral_tolerance=float(eps_weak/k[0]),
                         strong_relative_spectral_tolerance=float(eps_strong/k[0])))
    assert rows[-1]['cubic_critical_velocity'] < 4e-5
    return dict(cases=rows, scope="An axial low-momentum lattice slice. Cubic observer stability shrinks as L^-2; the linear branch has a controlled window error. Tilted energies diagnose a proposed translation limit and do not establish microscopic boosts.")


def dispersion_checks():
    k = np.linspace(.001, .8, 4001)
    families = [
        ('linear', np.ones_like(k), np.zeros_like(k), True, True),
        ('slower_linear', .5*np.ones_like(k), np.zeros_like(k), False, True),
        ('faster_linear', 2*np.ones_like(k), np.zeros_like(k), True, False),
        ('cubic', k*k, 2*k, False, False),
        ('positive_cubic_correction', 1+.2*k*k, .4*k, True, False),
        ('negative_cubic_correction', 1-.2*k*k, -.4*k, False, True),
        ('rational_slowing', 1/(1+.2*k*k), -.4*k/(1+.2*k*k)**2, False, True),
    ]
    rows = []
    for name, f, derivative, expected_stability, expected_group_bound in families:
        energy, velocity = k*f, f+k*derivative
        stable = bool(min(energy-k) >= -1e-12)
        group_bound = bool(max(abs(velocity)) <= 1+1e-12)
        assert stable == expected_stability
        assert group_bound == expected_group_bound
        # All share the same scalar Gaussian precision W=k in this family.
        assert max(abs(np.sqrt((k*k*f)/f)-k)) < 1e-12
        rows.append(dict(name=name, passes_tilted_energy_test=stable,
                         passes_necessary_group_velocity_test=group_bound,
                         minimum_phase_velocity=float(min(f)),
                         maximum_group_speed=float(max(abs(velocity)))))
    return dict(cases=rows, scope="Dispersion-level tests for a unit spherical cone. Passing the group-velocity test does not prove microcausality. The cubic branch already fails stability in arbitrarily small windows, even where its group velocity is subluminal.")


def convex_cone_checks():
    rng, rows = np.random.default_rng(9112634), []
    for case in range(24):
        raw = rng.normal(size=(3, 3))
        d = raw @ raw.T+.3*np.eye(3)
        k = rng.normal(size=3)
        support = np.sqrt(k @ d @ k)
        gradient = d @ k/support
        boundary_error = abs(gradient @ la.solve(d, gradient)-1)
        assert boundary_error < 3e-13
        # Independently maximize the support in coordinates v=sqrt(D) u, |u|<=1.
        root = positive_power(d, .5)
        maximizer = root @ (root @ k/la.norm(root @ k))
        assert la.norm(maximizer-gradient) < 2e-13
        integral = quad(lambda t: float((d @ (t*k)/np.sqrt((t*k) @ d @ (t*k))) @ k),
                        0, 1, epsabs=1e-10, epsrel=1e-10)[0]
        assert abs(integral-support) < 3e-12
        # A smooth non-ellipsoidal support function gives the same cone saturation.
        dual_exponent = 4/3
        finsler = np.sum(abs(k)**dual_exponent)**(1/dual_exponent)
        grad_f = np.sign(k)*abs(k)**(dual_exponent-1)*finsler**(1-dual_exponent)
        assert abs(np.sum(abs(grad_f)**4)-1) < 2e-12
        assert abs(grad_f @ k-finsler) < 2e-12
        rows.append(dict(case=case, momentum=k.tolist(),
                         ellipsoid_support=float(support),
                         supporting_velocity=gradient.tolist(),
                         cone_boundary_error=float(boundary_error),
                         radial_integral_error=float(abs(integral-support)),
                         nonellipsoidal_support=float(finsler)))
    return dict(cases=rows, scope="Support-function saturation for positive ellipsoids and the l4 velocity ball. The latter satisfies the dispersion cone conditions without a quadratic metric; no local QFT realization is inferred.")


def response_checks():
    rng, rows = np.random.default_rng(9112635), []
    for delta in [.01, .05, .2]:
        for fraction in [-1., -.6, -.2, .2, .6, 1.]:
            f, k, alpha, c = 1+delta*fraction, .37, 1.4, .9
            # Two positive branches mixed by a real orthogonal polarization rotation.
            raw = rng.normal(size=(2, 2))
            rotation = la.qr(raw)[0]
            factors = np.array([f, 1-delta*fraction])
            mixing = (rotation*factors) @ rotation.T
            a, b = c*mixing/alpha, c*alpha*k*k*mixing
            x, p, energies = oscillator_covariance(a, b)
            assert la.norm(x-np.eye(2)/(2*alpha*k)) < 2e-12
            assert la.norm(p-np.eye(2)*alpha*k/2) < 2e-12
            assert la.norm(np.sort(energies)-np.sort(c*k*factors)) < 1e-12
            bound, worst = delta/(1-delta), 0.
            # Direct inverse kernels, including zero and widely separated frequencies.
            for s in [0., 1e-3, .2, 1., 5., 1e3]:
                frequency = s*c*k
                actual = la.inv(frequency**2*la.inv(a)+b)
                selected = (c/alpha)/(frequency**2+c*c*k*k)
                error = la.norm(actual/selected-np.eye(2), 2)
                worst = max(worst, error)
                assert error <= bound+3e-12
            rows.append(dict(delta=delta, fractional_offset=fraction,
                             frequency_factors=factors.tolist(),
                             actual_mode_energies=energies.tolist(),
                             maximum_sampled_response_relative_error=float(worst),
                             uniform_response_relative_error_bound=float(bound)))
    return dict(cases=rows, scope="Canonical two-polarization Gaussian systems of fixed vacuum width, including non-diagonal real polarization mixing. Frequencies come from full canonical diagonalization, and response errors from inverse kernels.")


def exact_identities():
    f, s = sp.symbols('f s', positive=True)
    ratio = f*(s*s+1)/(s*s+f*f)
    assert sp.factor(ratio-1) == (f-1)*(-f+s**2)/(f**2+s**2)
    # The harmonic oscillator pair-creation coefficient at precision w is
    # (B/w-A*w)/4; it vanishes precisely when B=A*w^2.
    a, w = sp.symbols('a w', positive=True)
    assert sp.simplify((a*w*w/w-a*w)/4) == 0
    defect = sp.simplify(2*(2**sp.Rational(3, 4))**2-4)
    assert defect == -4+4*sp.sqrt(2)
    return dict(response_ratio_error=str(sp.factor(ratio-1)),
                pair_creation_coefficient_after_shared_vacuum_condition="0",
                nonquadratic_support_parallelogram_defect=str(defect),
                scope="Three exact algebraic identities, supplementary to the analytical cone proof.")


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(modular_rings=modular_ring_checks(),
                  finite_volume_stability=finite_volume_checks(),
                  separate_cone_conditions=dispersion_checks(),
                  convex_cones=convex_cone_checks(),
                  gaussian_response_control=response_checks(),
                  exact_identities=exact_identities())
    sources = ['CAUSAL_VACUUM_SELECTION.md', 'scripts/causal_vacuum_selection_audit.py',
               'PROJECTED_TENSOR_VACUUM.md', 'SPIN_STATE_GAUGE_GEOMETRY.md',
               'PREPOTENTIAL_LATTICE_BRIDGE.md', 'COMPACT_TENSOR_DYNAMICS.md',
               'COMPACT_CONSTRAINT_NORMALIZER.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'EINSTEIN_MODEL_DECISION.md', 'COLLECTIVE_WAVE_SPACETIME.md',
               'LOCAL_CAUSAL_CLOCK.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = (
        'A common observer-stability and propagation cone conditionally fixes gapless dispersion. '
        'For the given canonical two-polarization Gaussian vacuum, a spherical cone fixes the '
        'free linear-wave Hamiltonian and its residue. The cubic Gaussian parent fails uniform '
        'tilted vacuum stability. Identical regional modular data alone cannot select the clock. '
        'No microscopic cone, finite-spin phase, full microcausality, nonlinear Einstein gravity, '
        'universal matter coupling, or TOE is proved. No Lean theorem.')
    target = root/'data/causal_vacuum_selection_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         exact_identities=3, source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
