#!/usr/bin/env python3
"""A commutative symbol interaction with the unchanged free determinant.

Tests physical packet widths, an exact finite quartic vertex, and its
first coupling derivative. This does not construct a local tensor-product
microscopic Hamiltonian or prove finite-coupling Einstein dynamics.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.special import gamma, sph_harm
import sympy as sy

from geometric_spectral_induction_audit import spin_matrices
from proper_resolution_induction_audit import coefficient, heat_limit, spectrum


SPECIES = 8
WICK_FACTOR = SPECIES*(SPECIES+2)/24


def symbol_isometry_checks():
    rows = []
    for size in [2, 3, 4, 5]:
        jx, jy, jz = spin_matrices(size-1)
        raising, lowering = jx+1j*jy, jx-1j*jy
        basis, labels = [], []
        for ell in range(size):
            state = np.linalg.matrix_power(raising, ell)
            state = state/np.linalg.norm(state)
            for m in range(ell, -ell-1, -1):
                basis.append(state.copy())
                labels.append((ell, m))
                if m > -ell:
                    state = (lowering @ state-state @ lowering)/np.sqrt((ell+m)*(ell-m+1))
        transform = np.column_stack([a.ravel(order='F') for a in basis])
        identity = np.eye(size)
        adjoints = [np.kron(identity, a)-np.kron(a.T, identity) for a in [jx, jy, jz]]
        lp = np.zeros((size**2, size**2), dtype=complex)
        lookup = {label: index for index, label in enumerate(labels)}
        for index, (ell, m) in enumerate(labels):
            if m < ell:
                lp[lookup[(ell, m+1)], index] = np.sqrt((ell-m)*(ell+m+1))
        lz = np.diag([m for ell, m in labels])
        angular = [(lp+lp.T)/2, (lp-lp.T)/(2j), lz]
        gram_error = np.max(abs(transform.conj().T @ transform-np.eye(size**2)))
        angular_error = max(np.max(abs(transform.conj().T @ a @ transform-l))
                            for a, l in zip(adjoints, angular))
        reality_error = max(np.max(abs(a.conj().T-(-1.)**m*basis[lookup[(ell, -m)]]))
                            for a, (ell, m) in zip(basis, labels))
        assert max(gram_error, angular_error, reality_error) < 2e-13
        pauli = [np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1])]
        matrix_d = np.eye(2*size**2)+sum(np.kron(s, a) for s, a in zip(pauli, adjoints))
        symbol_d = np.eye(2*size**2)+sum(np.kron(s, a) for s, a in zip(pauli, angular))
        spin_transform = np.kron(np.eye(2), transform)
        dirac_error = np.max(abs(spin_transform.conj().T @ matrix_d @ spin_transform-symbol_d))
        assert dirac_error < 2e-13
        # Mean-square-normalized coordinate: same quadratic form, different quartic.
        j = (size-1)/2
        z = np.sqrt(3)*jz/np.sqrt(j*(j+1))
        matrix_fourth = np.trace(np.linalg.matrix_power(z, 4)).real/size
        expected_fourth = 9/5-3/(5*j*(j+1))
        assert abs(matrix_fourth-expected_fourth) < 3e-14
        rows.append(dict(size=size, scalar_dimension=size**2, gram_error=float(gram_error),
                         angular_intertwiner_error=float(angular_error), reality_error=float(reality_error),
                         first_order_dirac_intertwiner_error=float(dirac_error),
                         normalized_matrix_coordinate_quartic=float(matrix_fourth),
                         pointwise_symbol_coordinate_quartic=9/5))
    return dict(cases=rows,
                scope='The unitary angular-momentum intertwiner preserves scalar and first-order fermion quadratic forms and measures. It does not preserve multiplication; the pointwise interaction is a specified model revision.')


def packet_raw(theta, n, power):
    return (np.sinc(n*theta/(2*np.pi))/np.sinc(theta/(2*np.pi)))**(2*power)


def packet_checks():
    rows = []
    for power in [2, 3]:
        for size in [8, 16, 32, 64, 128]:
            n, cutoff = (size-1)//power+1, 1.
            radius = size/cutoff
            assert power*(n-1) <= size-1
            def integrand(theta, moment):
                return 2*np.pi*radius**2*np.sin(theta)*(radius*theta)**moment*packet_raw(theta, n, power)**2
            norm, err = quad(lambda theta: integrand(theta, 0), 0, np.pi, epsabs=1e-9, limit=300)
            moment, _ = quad(lambda theta: integrand(theta, 2), 0, np.pi, epsabs=1e-8, limit=300)
            actual = moment/norm
            lower_norm = 4/np.pi*(23/24)**(4*power)*radius**2/n**2
            bound = np.pi**4/2*power**3/(power-1)*(24/23)**(4*power)/cutoff**2
            assert norm >= lower_norm and actual <= bound
            # Gauss-Legendre exactly integrates the squared polynomial packet.
            z, weights = leggauss(power*(n-1)+1)
            polynomial_norm = 2*np.pi*radius**2*np.dot(weights, packet_raw(np.arccos(z), n, power)**2)
            assert abs(norm-polynomial_norm) < 2e-8
            rows.append(dict(size=size, packet_power=power, internal_order=n,
                             harmonic_degree=power*(n-1), proper_radius=radius,
                             squared_norm=float(norm), independent_polynomial_norm=float(polynomial_norm),
                             geodesic_variance=float(actual), rms_proper_width=float(np.sqrt(actual)),
                             uniform_variance_bound=float(bound), quadrature_error=float(err)))
    # Verify the Chebyshev expression is a polynomial of the advertised degree.
    z = sy.Symbol('z')
    for n in [2, 3, 5, 8]:
        quotient, remainder = sy.div(1-sy.chebyshevt(n, z), n*n*(1-z), z)
        assert remainder == 0 and sy.degree(quotient, z) == n-1
        assert quotient.subs(z, 1) == 1
    return dict(cases=rows, exact_packet_polynomial_identity=True,
                scope='Normalized scalar-symbol packets have a volume-independent proper second moment. They are overlapping band-limited field packets, not positive matrix coherent states or independent sites.')


def packet_vertex_checks():
    rows = []
    for power in [2, 3]:
        ap = 4/np.pi*(23/24)**(4*power)
        lp = 4*np.pi*power**2/((power-1)*np.sqrt(ap))
        dp = (1+np.pi*power)**(2*power)/np.sqrt(ap)
        for size in [16, 32, 64]:
            n = (size-1)//power+1
            degree = power*(n-1)
            z, weights = leggauss(2*degree+1)
            azimuth = np.arange(4*degree+1)*2*np.pi/(4*degree+1)
            zz, az = np.meshgrid(z, azimuth, indexing='ij')
            zz, az = zz.ravel(), az.ravel()
            weights = np.repeat(weights, len(azimuth))*2*np.pi/len(azimuth)*size**2
            raw = packet_raw(np.arccos(zz), n, power)
            norm = np.sqrt(np.dot(weights, raw**2))
            first = raw/norm
            single_fourth = np.dot(weights, first**4)
            overlaps = []
            for distance in [0., 4., 8., 16.]:
                angle = distance/size
                cosine = zz*np.cos(angle)+np.sqrt(1-zz**2)*np.cos(az)*np.sin(angle)
                second = packet_raw(np.arccos(np.clip(cosine, -1, 1)), n, power)/norm
                # Product packets differ only on the first sphere.
                vertex = np.dot(weights, first**2*second**2)*single_fourth
                bound = 2*dp**2*lp**2/ap**2*(1+distance/2)**(-2*power)
                assert vertex <= bound and vertex > 0
                overlaps.append(dict(proper_separation=distance, quartic_vertex=float(vertex),
                                     relative_overlap=float(vertex/single_fourth**2),
                                     analytical_diameter_bound=float(bound)))
            assert overlaps[-1]['relative_overlap'] < .0003
            rows.append(dict(size=size, packet_power=power, profile=overlaps))
    return dict(cases=rows,
                scope='Exact positive cubature checks quartic interactions of localized product packets at fixed proper separations. The analytical bound is uniform; the packets do not form independent local sites.')


def sphere_cubature(size, radius, multiplier):
    ell_max = size-1
    z, wz = leggauss(multiplier*ell_max//2+1)
    azimuth = np.arange(multiplier*ell_max+1)*2*np.pi/(multiplier*ell_max+1)
    zz, az = np.meshgrid(z, azimuth, indexing='ij')
    theta, az = np.arccos(zz.ravel()), az.ravel()
    weights = np.repeat(wz, len(azimuth))*2*np.pi/len(azimuth)*radius**2
    columns = []
    for ell in range(size):
        columns.append(sph_harm(0, ell, az, theta).real/radius)
        for m in range(1, ell+1):
            y = sph_harm(m, ell, az, theta)*np.sqrt(2)*(-1)**m/radius
            columns.extend([y.real, y.imag])
    return np.column_stack(columns), weights


def quartic_cubature_checks():
    rng, rows = np.random.default_rng(9112026), []
    for left, right in [(2, 2), (2, 3), (3, 3)]:
        count = left**2*right**2
        coefficients = rng.normal(size=(count, SPECIES))
        direction = rng.normal(size=coefficients.shape)
        results = []
        for multiplier in [4, 6]:
            a, wa = sphere_cubature(left, left, multiplier)
            b, wb = sphere_cubature(right, right, multiplier)
            basis, weights = np.kron(a, b), np.kron(wa, wb)
            gram_error = np.max(abs(basis.T @ (weights[:, None]*basis)-np.eye(count)))
            assert gram_error < 2e-13
            values, variation = basis @ coefficients, basis @ direction
            squared = np.sum(values**2, axis=1)
            energy = np.dot(weights, squared**2)/24
            gradient = basis.T @ (weights[:, None]*values*squared[:, None])/6
            hessian = np.dot(weights, squared*np.sum(variation**2, axis=1)/6+
                              np.sum(values*variation, axis=1)**2/3)
            assert energy > 0 and hessian > 0
            if multiplier == 6:
                bound = np.dot(weights, squared**3)/36
                assert np.sum(gradient**2) <= bound+1e-12
                def energy_at(t):
                    return np.dot(weights, np.sum((values+t*variation)**2, axis=1)**2)/24
                # A two-step extrapolation is exact for a quartic polynomial
                # before roundoff, and avoids cancellation at tiny steps.
                differences = []
                for epsilon in [.004, .002]:
                    differences.append(np.array([
                        (energy_at(epsilon)-energy_at(-epsilon))/(2*epsilon),
                        (energy_at(epsilon)-2*energy_at(0)+energy_at(-epsilon))/epsilon**2]))
                finite_first, finite_second = (4*differences[1]-differences[0])/3
                assert abs(finite_first-np.sum(gradient*direction)) < 1e-8
                assert abs(finite_second-hessian) < 2e-8
            results.append((energy, gradient, len(weights)))
        assert abs(results[0][0]-results[1][0]) < 2e-12
        assert np.max(abs(results[0][1]-results[1][1])) < 2e-13
        rows.append(dict(matrix_sizes=[left, right], scalar_modes=count,
                         positive_quartic_cubature_nodes=results[0][2],
                         independent_sextic_cubature_nodes=results[1][2],
                         quartic_action=float(energy), directional_hessian=float(hessian),
                         squared_gradient=float(np.sum(gradient**2)), bessel_gradient_bound=float(bound),
                         independent_energy_error=float(abs(results[0][0]-results[1][0]))))
    return dict(cases=rows,
                scope='A pointwise O(8) quartic equals a finite positive weighted sum exactly. Node values remain linearly constrained by the harmonic cutoff; this is not a tensor-product site Hamiltonian.')


def resolvent_coefficients(c):
    a0 = c*np.log(c)-2*(c+1)*np.log1p(c)+(c+2)*np.log(c+2)
    a1 = np.log((c+1)**2/(c*(c+2)))/3+(1/(c+1)-1/(c+2))/6
    return a0, a1


def symbolic_and_integral_checks():
    t = sy.Symbol('t', positive=True)
    i = (1-sy.exp(-t))/t
    b = sy.Rational(1, 3)+(t/6-sy.Rational(1, 3))*sy.exp(-t)
    split = (1-sy.exp(-t))**2/(3*t)+(sy.exp(-t)-sy.exp(-2*t))/6
    assert sy.simplify(i*b-split) == 0
    x = sy.symbols('x:8', real=True)
    quartic = sy.expand(sum(y*y for y in x)**2)
    # Independent Gaussian moments, variance one, reproduce the O(n) Wick count.
    wick = 0
    for powers, coefficient_value in sy.Poly(quartic, *x).terms():
        moment = coefficient_value
        for power in powers:
            moment *= 0 if power % 2 else (sy.factorial2(power-1) if power else 1)
        wick += moment
    assert wick == SPECIES*(SPECIES+2)
    rows = []
    for c in [.01, .1, 1., 4.]:
        a0, a1 = resolvent_coefficients(c)
        i0, e0 = quad(lambda t: np.exp(-c*t)*heat_limit(t)[0]**2, 0, np.inf, epsabs=2e-12)
        i1, e1 = quad(lambda t: np.exp(-c*t)*heat_limit(t)[0]*heat_limit(t)[1], 0, np.inf, epsabs=2e-12)
        assert max(abs(a0-i0), abs(a1-i1)) < 3e-11
        assert a0 > 0 and a1 > 0
        rows.append(dict(mass_ratio=c, a0=a0, a1=a1, independent_integrals=[float(i0), float(i1)],
                         quadrature_errors=[float(e0), float(e1)],
                         first_coupling_volume_coefficient_over_cutoff_fourth=float(WICK_FACTOR*a0*a0/(256*np.pi**4)),
                         first_coupling_curvature_coefficient_over_cutoff_squared=float(WICK_FACTOR*a0*a1/(256*np.pi**4)),
                         free_inverse_newton_over_cutoff_squared=float(2*coefficient(c)/np.pi),
                         first_coupling_inverse_newton_derivative_over_cutoff_squared=float(-WICK_FACTOR*a0*a1/(16*np.pi**3))))
    return dict(cases=rows, resolvent_integrand_identity=True, independent_gaussian_wick_count=int(wick))


@lru_cache(maxsize=128)
def scalar_resolvent_trace(left, right, c):
    a, wa = spectrum(left, False)
    b, wb = spectrum(right, False)
    return np.sum(wa[:, None]*wb[None, :]/(a[:, None]+b[None, :]+c), dtype=np.longdouble)


def trace_remainder_bound(c, rho):
    constant = 102000+900*rho**2
    return constant*(1/3+np.exp(-c)/c)+4*rho**2/(np.e**2*c**3)+(1+3*rho**2)/(2*c)


def scaling_checks():
    rows = []
    for c in [.01, .1, 1.]:
        a0, a1 = resolvent_coefficients(c)
        for scale in [16, 32, 64, 128, 256]:
            for left, right in [(scale, scale), (scale, 3*scale//2)]:
                product, total = left**2*right**2, left**2+right**2
                trace = scalar_resolvent_trace(left, right, c)
                remainder = float(trace-product*a0-total*a1)
                bound = trace_remainder_bound(c, max(left, right)/min(left, right))
                assert abs(remainder) < bound
                action_derivative = WICK_FACTOR*trace**2/(16*np.pi**2*product)
                volume = WICK_FACTOR*product*a0*a0/(16*np.pi**2)
                curvature = WICK_FACTOR*total*a0*a1/(8*np.pi**2)
                residual = float(action_derivative-volume-curvature)
                if scale == 256:
                    assert abs(residual/curvature) < .001
                rows.append(dict(mass_ratio=c, matrix_sizes=[left, right], resolvent_trace=float(trace),
                                 resolvent_remainder=remainder, analytical_trace_remainder_bound=float(bound),
                                 first_coupling_derivative=float(action_derivative),
                                 first_coupling_volume_term=float(volume), first_coupling_curvature_term=float(curvature),
                                 first_coupling_action_remainder=residual))
    return dict(cases=rows,
                scope='Exact full-spectrum scalar resolvents determine the first derivative in coupling, including the volume and Einstein curvature terms. This does not establish the finite-coupling metric effective action.')


def shape_variations():
    c, rows = .1, []
    a0, a1 = resolvent_coefficients(c)
    shape_coefficient = WICK_FACTOR*a0*a1/(8*np.pi**2)
    for k in [2, 3, 4, 5]:
        scale, h = (k*(k+1))**2, np.log1p(1/k)
        pairs = [(scale, scale), (k*(k+1)**3, k**3*(k+1)), ((k+1)**4, k**4)]
        assert all(left*right == scale**2 for left, right in pairs)
        values = []
        for left, right in pairs:
            product = left**2*right**2
            trace = scalar_resolvent_trace(left, right, c)
            # A shape-independent volume term cancels exactly in these stencils.
            # Subtract it first to reduce floating-point cancellation.
            values.append(float(WICK_FACTOR/(16*np.pi**2)*(trace**2/product-product*a0*a0)/scale**2))
        targets = 2*shape_coefficient*np.cosh(2*h*np.arange(3))
        def stencil(v):
            return np.array([2*(v[1]-v[0])/h**2, (2*v[2]-8*v[1]+6*v[0])/h**4])
        actual, target = stencil(values), stencil(targets)
        if k == 5:
            assert abs(actual[0]-target[0]) < 3e-6
            assert abs(actual[1]-target[1]) < 5e-5
        rows.append(dict(k=k, scale=scale, shape_step=float(h), second_difference=float(actual[0]),
                         fourth_difference=float(actual[1]), einstein_finite_second=float(target[0]),
                         einstein_finite_fourth=float(target[1]), second_error=float(actual[0]-target[0]),
                         fourth_error=float(actual[1]-target[1])))
    return dict(cases=rows, limiting_second=float(8*shape_coefficient), limiting_fourth=float(32*shape_coefficient))


def finite_coupling_radial_checks():
    # N1=N2=1 is the exact constant-mode model. O(8) reduces the integral
    # to a Gamma(4,1) radial variable; no Monte Carlo sampling is involved.
    rows, volume, mass_squared = [], 16*np.pi**2, .1
    shape = SPECIES/2
    free_diagonal = 1/(volume*mass_squared)
    expected_u = WICK_FACTOR*volume*free_diagonal**2
    for coupling in [.01, .1, 1., 4.]:
        radial_coefficient = coupling/(6*volume*mass_squared**2)
        def density(z):
            return z**(shape-1)*np.exp(-z-radial_coefficient*z*z)/gamma(shape)
        partition, _ = quad(density, 0, np.inf, epsabs=2e-13)
        action = -np.log(partition)
        eu, _ = quad(lambda z: density(z)*z*z/(6*volume*mass_squared**2), 0, np.inf, epsabs=2e-13)
        eu2, _ = quad(lambda z: density(z)*(z*z/(6*volume*mass_squared**2))**2, 0, np.inf, epsabs=2e-13)
        variance = eu2/partition-(eu/partition)**2
        variance_bound = 8*SPECIES**3*volume*free_diagonal**3/(3*mass_squared)
        remainder = coupling*expected_u-action
        bound = coupling**2*variance_bound/2
        assert 0 <= remainder <= bound
        assert 0 <= variance <= variance_bound
        rows.append(dict(coupling=coupling, exact_interaction_action=float(action),
                         first_order_action=float(coupling*expected_u), actual_taylor_remainder=float(remainder),
                         uniform_analytical_taylor_bound=float(bound), exact_quartic_variance=float(variance),
                         uniform_variance_bound=float(variance_bound)))
    return dict(cases=rows,
                scope='Independent nonperturbative radial integrals check the coupling-remainder inequalities in the exact constant-mode member. The all-size proof uses convexity and Brascamp-Lieb, not these small cases.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbol_isometry=symbol_isometry_checks(), packets=packet_checks(),
                  packet_vertices=packet_vertex_checks(),
                  local_quartic=quartic_cubature_checks(), coefficients=symbolic_and_integral_checks(),
                  full_resolvent_scaling=scaling_checks(), first_coupling_shape_variations=shape_variations(),
                  finite_coupling_radial=finite_coupling_radial_checks())
    sources = ['LOCAL_SYMBOL_INTERACTION.md', 'scripts/local_symbol_interaction_audit.py',
               'PROPER_RESOLUTION_INDUCTION.md', 'scripts/proper_resolution_induction_audit.py',
               'GEOMETRIC_SPECTRAL_INDUCTION.md', 'scripts/geometric_spectral_induction_audit.py',
               'BALANCED_MATTER_INDUCTION.md', 'CONTINUUM_EINSTEIN_BRIDGE.md',
               'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A supplied unitary symbol map preserves the complete free determinant while a new pointwise '
                       'positive quartic interaction has uniformly localized field packets and an exact finite cubature. '
                       'The first coupling derivative is a volume term plus the homogeneous Einstein curvature functional '
                       'with a bounded remainder. Convexity bounds the finite-coupling Taylor error per volume, not per '
                       'curvature scale. No independent local site algebra, microscopic refinement law, arbitrary-metric '
                       'finite-coupling Einstein action, Lorentzian gravity, Standard Model, or TOE is proved. No new Lean theorem.')
    target = root/'data/local_symbol_interaction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {key: len(value['cases']) for key, value in report.items()
              if isinstance(value, dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
