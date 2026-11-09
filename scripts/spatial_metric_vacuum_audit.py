#!/usr/bin/env python3
"""Spatial transport, ultraviolet vacuum tests, and carried Gaussian geometry."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.special import jv
import sympy as sy


def exact_checks():
    # A derivation on the pointwise finite-site algebra must kill each idempotent.
    size = 3
    entries = sy.symbols('d0:9')
    derivative = sy.Matrix(size, size, entries)
    equations = []
    for i in range(size):
        e = sy.eye(size)[:, i]
        equations.extend(derivative*e-2*sy.diag(*e)*derivative*e)
    assert sy.linsolve(equations, entries) == sy.FiniteSet((0,)*9)
    z, y = sy.symbols('z y', real=True)
    second_moment = sy.integrate(z**2*sy.cos(y)**2, (y, -sy.pi, sy.pi))/(2*sy.pi)
    fourth_moment = sy.integrate(z**2*sy.sin(y)**2+z**4*sy.cos(y)**4, (y, -sy.pi, sy.pi))/(2*sy.pi)
    assert second_moment == z**2/2
    fourth_moment = sy.expand(fourth_moment)
    assert fourth_moment == z**2/2+3*z**4/8
    spacing = sy.symbols('a', positive=True)
    vacuum_density = (sy.sin(spacing/2)/spacing)**4*(sy.Rational(3, 8)+sy.cos(spacing/2)**2/2)
    assert sy.limit(vacuum_density, spacing, 0) == sy.Rational(7, 128)
    x, tau, k, l = sy.symbols('x tau k l', real=True)
    jacobian = sy.Matrix([[1, tau*sy.cos(y)], [0, 1]])
    metric = jacobian.T*jacobian
    assert sy.simplify(metric.det()) == 1
    wave = sy.exp(sy.I*(k*(x+tau*sy.sin(y))+l*y))
    inverse = metric.inv()
    coordinates = [x, y]
    laplace = sum(sy.diff(sum(inverse[i, j]*sy.diff(wave, coordinates[j])
                              for j in range(2)), coordinates[i]) for i in range(2))
    assert sy.simplify((laplace+(k*k+l*l)*wave)/wave) == 0
    return dict(pointwise_site_derivation_is_zero=True,
                bessel_second_moment=str(second_moment),
                bessel_fourth_moment=str(fourth_moment),
                product_vacuum_defect_squared_per_site_limit='7/128',
                shear_metric_determinant_one=True, shear_laplacian_intertwining=True,
                scope="Exact finite-algebra, Parseval moment, transport and metric identities. Infinite-dimensional conclusions use the proofs and stated representation assumptions in the note.")


def lattice_transport():
    rows = []
    for size in [16, 24, 32, 64, 128, 256]:
        spacing = 2*np.pi/size
        x = spacing*np.arange(size)
        shift = np.roll(np.eye(size), 1, axis=1)
        derivative = (shift-shift.T)/(2*spacing)
        assert la.norm(derivative@np.sin(x)-np.sin(spacing)/spacing*np.cos(x)) < 1e-12
        w = np.diag(np.sin(x))
        dw = np.diag(derivative@np.sin(x))
        defect = (derivative@w-w@derivative-dw)@derivative
        symmetric = (defect+defect.T)/2
        vacuum_squared = la.norm(symmetric, 'fro')**2/2
        expected_per_site = (np.sin(spacing/2)/spacing)**4*(3/8+np.cos(spacing/2)**2/2)
        assert abs(vacuum_squared/size-expected_per_site) < 2e-13
        smooth_error = la.norm(defect@np.exp(2j*x))/np.sqrt(size)
        assert smooth_error < 3.2*spacing**2
        # Verify the Wick formula independently by two-particle oscillator coefficients.
        pair_norm_squared = sum(symmetric[i, i]**2/2 for i in range(size))
        pair_norm_squared += sum(symmetric[i, j]**2 for i in range(size) for j in range(i+1, size))
        assert abs(pair_norm_squared-vacuum_squared) < 1e-11
        rows.append(dict(sites=size, spacing=spacing, smooth_mode_two_defect=float(smooth_error),
                         full_spatial_matrix_defect=float(la.norm(defect, 2)),
                         product_gaussian_commutator_defect=float(np.sqrt(vacuum_squared)),
                         defect_squared_per_site=float(vacuum_squared/size),
                         analytic_squared_per_site=float(expected_per_site),
                         local_gaussian_width_cancels=True))
    assert abs(rows[-1]['defect_squared_per_site']-7/128) < 1.1e-5
    return dict(cases=rows, scope="Exact centered finite-difference trace-channel generators on a circle. The discrete vector bracket removes the inhomogeneous residual, but the full-output quantum commutator on the product Gaussian retains an extensive defect. This is not a no-go for all stencils or states.")


def pair_sum(dimension, cutoff):
    grid = np.array(list(itertools.product(range(-cutoff, cutoff+1), repeat=dimension)), float)
    p = np.array([3.] if dimension == 1 else [0., 1.]+[0.]*(dimension-2))
    total, count = 0., 0
    for sign in [-1, 1]:
        partner = sign*p-grid
        wk = np.sqrt(np.sum(grid*grid, axis=1))
        wl = np.sqrt(np.sum(partner*partner, axis=1))
        keep = (wk > 0) & (wl > 0) & (np.max(abs(partner), axis=1) <= cutoff)
        k, l, wk, wl = grid[keep], partner[keep], wk[keep], wl[keep]
        coefficient = .5*(k[:, 0]*np.sqrt(wl/wk)+l[:, 0]*np.sqrt(wk/wl))
        total += float(coefficient@coefficient)/8
        count += int(np.sum(keep))
    return total, count


def independent_gaussian_pair_check(dimension, cutoff=3):
    # Fourier-to-real conversion provides a check separate from the pair sum.
    modes = [k for k in itertools.product(range(-cutoff, cutoff+1), repeat=dimension) if any(k)]
    lookup = {k: i for i, k in enumerate(modes)}
    size = len(modes)
    p = np.array([3] if dimension == 1 else [0, 1])
    matrix = np.zeros((size, size), complex)
    for j, mode in enumerate(modes):
        for sign in [-1, 1]:
            target = tuple(np.array(mode)+sign*p)
            if target in lookup:
                matrix[lookup[target], j] += .5j*mode[0]
    basis, frequencies = np.zeros((size, size), complex), []
    col = 0
    for mode in modes:
        neg = tuple(-k for k in mode)
        if mode < neg:
            i, j = lookup[mode], lookup[neg]
            basis[i, col] = basis[j, col] = 1/np.sqrt(2)
            basis[i, col+1], basis[j, col+1] = -1j/np.sqrt(2), 1j/np.sqrt(2)
            frequencies.extend([la.norm(mode)]*2)
            col += 2
    real = basis.conj().T@matrix@basis
    assert la.norm(real.imag) < 1e-12
    frequency = np.array(frequencies)
    whitened = np.sqrt(frequency[:, None]/frequency[None, :])*real.real
    wick = la.norm((whitened+whitened.T)/2, 'fro')**2/2
    pair, _ = pair_sum(dimension, cutoff)
    assert abs(wick-pair) < 2e-12
    return dict(spatial_dimension=dimension, cutoff=cutoff, real_gaussian_wick_norm_squared=float(wick),
                fock_pair_norm_squared=pair, difference=float(abs(wick-pair)))


def fock_generator():
    rows = []
    for dimension in [1, 2, 3]:
        for cutoff in [4, 8, 12, 16, 24, 32]:
            squared, count = pair_sum(dimension, cutoff)
            if dimension == 1:
                assert abs(squared-1) < 2e-12
            rows.append(dict(spatial_dimension=dimension, cutoff=cutoff,
                             nonzero_pair_channels=count, vacuum_pair_norm_squared=squared,
                             vacuum_pair_norm=math.sqrt(squared),
                             squared_norm_per_cutoff_volume=squared/cutoff**dimension))
    for dimension in [2, 3]:
        selected = [row for row in rows if row['spatial_dimension'] == dimension]
        assert selected[-1]['vacuum_pair_norm_squared'] > selected[-2]['vacuum_pair_norm_squared']*1.5
        assert selected[-1]['squared_norm_per_cutoff_volume'] > .01
    return dict(cases=rows, independent_real_gaussian_checks=[independent_gaussian_pair_check(d) for d in [1, 2]],
                scope="Pair-creation norm of the spatial generator in a massless scalar Fock vacuum, with nonzero modes in a Fourier cube. One dimension uses cos(3x); two and three dimensions use the volume-preserving shear cos(y) partial_x. Zero-mode and finite linear density-shift terms do not affect the ultraviolet conclusion. Generator divergence alone is not a finite-unitary no-go.")


def shear_column(tau, momentum, padding=60):
    z = tau*momentum
    limit = int(math.ceil(2*abs(z)+padding))
    orders = np.arange(-limit, limit+1)
    probabilities = jv(orders, z)**2
    ratio = np.sqrt(1+(orders/momentum)**2)
    beta_squared = (ratio-1)**2/(4*ratio)
    probability = float(np.sum(probabilities[abs(orders) >= abs(z)/2]))
    moments = [float(np.sum(probabilities*orders**n)) for n in [0, 2, 4]]
    return float(beta_squared@probabilities), probability, moments


def finite_shear():
    rows = []
    for tau in [.25, .5, 1.]:
        ratio_floor = math.sqrt(1+tau*tau/4)
        uniform_lower = (ratio_floor-1)**2/(56*ratio_floor)
        running = 0.
        for momentum in range(1, 129):
            beta, probability, moments = shear_column(tau, momentum)
            running += beta
            if momentum not in [4, 8, 16, 32, 64, 128]:
                continue
            refined, _, _ = shear_column(tau, momentum, padding=90)
            z = tau*momentum
            assert abs(moments[0]-1) < 3e-13
            assert abs(moments[1]-z*z/2) < 2e-11*max(1, z*z)
            assert abs(moments[2]-(3*z**4+4*z*z)/8) < 2e-11*max(1, z**4)
            probability_lower = z*z/(2*(3*z*z+4))
            assert probability >= probability_lower-1e-13
            assert beta >= uniform_lower and abs(beta-refined) < 2e-13
            cumulative_lower = max(0, momentum-math.ceil(1/tau)+1)*uniform_lower
            assert running >= cumulative_lower
            rows.append(dict(shear=tau, incoming_mode=[momentum, 0, 0],
                             beta_column_squared_norm=beta,
                             proved_uniform_column_lower_bound=uniform_lower,
                             tail_event_probability=probability,
                             proved_probability_lower_bound=probability_lower,
                             cumulative_selected_columns_squared_norm=running,
                             proved_cumulative_lower_bound=cumulative_lower,
                             bessel_sum_refinement=abs(beta-refined),
                             normalization_error=abs(moments[0]-1)))
    return dict(cases=rows, scope="An exact smooth volume-preserving shear has a non-Hilbert-Schmidt Bogoliubov coefficient in two or more dimensions. The note's Bessel/Parseval and probability bound proves divergence; finite Bessel sums only illustrate it. All outgoing transverse momenta enter the analytical column bound.")


def spectral_derivative(size):
    frequency = np.fft.fftfreq(size)*size
    matrix = np.fft.ifft((1j*frequency)[:, None]*np.fft.fft(np.eye(size), axis=0), axis=0)
    assert la.norm(matrix.imag) < 1e-12
    return matrix.real


def positive_power(matrix, exponent):
    values, vectors = la.eigh(matrix)
    assert values[0] > 0
    return (vectors*values**exponent)@vectors.T


def transported_covariance():
    rows = []
    mass = .7
    for size in [7, 11, 15]:
        derivative = spectral_derivative(size)
        dx, dy = np.kron(derivative, np.eye(size)), np.kron(np.eye(size), derivative)
        x, y = np.meshgrid(2*np.pi*np.arange(size)/size, 2*np.pi*np.arange(size)/size, indexing='ij')
        identity = np.eye(size*size)
        flat = -dx@dx-dy@dy+mass*mass*identity
        root = positive_power(flat, .25)  # sqrt(omega), omega=sqrt(flat).
        inverse_root = la.inv(root)
        covariance = positive_power(flat, -.5)/2
        momentum_covariance = positive_power(flat, .5)/2
        transport_generator = np.diag(np.sin(y.ravel()))@dx
        assert la.norm(transport_generator+transport_generator.T) < 2e-12
        test = (np.exp(1j*x)+.3*np.exp(2j*y)+.2*np.exp(1j*(x+y))).ravel()
        test /= la.norm(test)
        for tau in [.2, .5, .8]:
            transport = la.expm(tau*transport_generator)
            extra = la.expm(.17*transport_generator)
            composition_error = la.norm(la.expm((tau+.17)*transport_generator)-transport@extra, 2)
            fixed_beta = (root@transport@inverse_root-inverse_root@transport@root)/2
            carried_flat = transport@flat@transport.T
            carried_root = positive_power(carried_flat, .25)
            carried_inverse = la.inv(carried_root)
            carried_beta = (carried_root@transport@inverse_root-carried_inverse@transport@root)/2
            c_new = transport@covariance@transport.T
            p_new = transport@momentum_covariance@transport.T
            purity = la.norm(4*c_new@p_new-identity, 2)
            precision_match = la.norm(c_new-positive_power(carried_flat, -.5)/2, 2)
            # Independently discretize the pullback metric's covariant Laplacian.
            cross = np.diag(tau*np.cos(y.ravel()))
            metric_flat = -dx@(identity+cross@cross)@dx+dx@cross@dy+dy@cross@dx-dy@dy+mass*mass*identity
            smooth_intertwining = la.norm(metric_flat@transport@test-transport@flat@test)
            assert composition_error < 2e-12
            assert la.norm(carried_beta, 'fro') < 5e-11
            assert purity < 2e-11 and precision_match < 2e-12
            rows.append(dict(grid_per_axis=size, shear=tau, mass=mass,
                             fixed_covariance_beta_squared_norm=float(la.norm(fixed_beta, 'fro')**2),
                             transported_covariance_beta_norm=float(la.norm(carried_beta, 'fro')),
                             transported_pure_gaussian_residual=float(purity),
                             covariance_laplacian_match=float(precision_match),
                             finite_transport_composition_error=float(composition_error),
                             independently_discretized_metric_smooth_intertwining_error=float(smooth_intertwining)))
    for tau in [.2, .5, .8]:
        selected = [r for r in rows if r['shear'] == tau]
        assert selected[-1]['fixed_covariance_beta_squared_norm'] > selected[0]['fixed_covariance_beta_squared_norm']
        assert selected[-1]['independently_discretized_metric_smooth_intertwining_error'] < selected[0]['independently_discretized_metric_smooth_intertwining_error']/1000
    return dict(cases=rows, scope="Finite spectral scalar system: transporting covariance with the pulled-back metric removes relative Bogoliubov mixing exactly and composes consistently. The exact carried regulator is dense; an independent metric Laplacian is checked on smooth inputs only. This is a kinematic map between Gaussian representations, not one fixed-Fock unitary continuum limit or a gravity Hamiltonian.")


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_checks(), lattice_transport=lattice_transport(),
                  spatial_generator_fock_test=fock_generator(), finite_shear_obstruction=finite_shear(),
                  metric_carried_covariance=transported_covariance())
    sources = ['SPATIAL_METRIC_VACUUM.md', 'scripts/spatial_metric_vacuum_audit.py',
               'AFFINE_SPIN_METRIC.md', 'SPIN_CLOCK_BRACKET.md',
               'GRAVITY_FROM_CLOCK_CONSTRAINTS.md', 'PROJECTED_TENSOR_VACUUM.md',
               'SPIN_STATE_GAUGE_GEOMETRY.md', 'EMBEDDING_VERSUS_GRAVITY.md']
    report['source_sha256'] = {path: hashlib.sha256((root/path).read_bytes()).hexdigest() for path in sources}
    report['scope'] = ('Spatial coordinate covariance requires more than onsite affine metric kinematics. '
                       'A specified lattice product vacuum has a nonvanishing commutator defect density. '
                       'An explicit finite shear is not unitarily implementable in a fixed massless scalar '
                       'Fock representation in two or more dimensions, applying also to the metric trace '
                       'if that channel is assigned this independent Fock representation. A metric-carried '
                       'Gaussian covariance repairs kinematic transport between representations. '
                       'This is established representation theory with an explicit repository diagnostic; '
                       'it does not rule out quantum gravity or derive its microscopic phase, constraints or TOE.')
    target = root/'data/spatial_metric_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {key: len(value['cases']) for key, value in report.items() if isinstance(value, dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target), cases=counts, total_cases=sum(counts.values()),
                         independent_gaussian_checks=2, source_references=len(sources),
                         scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
