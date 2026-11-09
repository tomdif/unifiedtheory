#!/usr/bin/env python3
"""Entangled field response: exact finite-grid sums and finite spectral checks.

The analytical operator theorem has no Fock cutoff. The explicitly labelled
three-mode spectral cross-check below does; it is not a regulator-removal proof.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy
from scipy.sparse.linalg import LinearOperator, cg
from scipy.special import logsumexp

from induced_geometry_audit import GaussianCarrier, MeanCell, change_reference
from finite_gap_feedback_audit import occupation_basis

KAPPA, CHI, B, D = .25, 2/3, .4, .31
OMEGA = np.hypot(D, 2*B)
GEO = np.array([[(OMEGA-D)/2, -B], [-B, (OMEGA+D)/2]])


def motif_matrices():
    def laplacian(edges):
        out = np.zeros((4, 4))
        for i, j in edges:
            v = np.eye(4)[i]-np.eye(4)[j]
            out += np.outer(v, v)
        return out
    l0 = laplacian([(0, 1), (1, 2), (2, 3)])
    l1 = laplacian([(0, 2), (1, 2), (1, 3)])
    val, basis = la.eigh(l0)
    relative = basis[:, 1:]
    a0 = KAPPA*relative.T@l0@relative
    a1 = KAPPA*relative.T@l1@relative
    comparison = la.eigvalsh(a1, a0)
    assert np.max(abs(comparison-np.array([2-np.sqrt(3), 1, 2+np.sqrt(3)]))) < 1e-13
    assert la.eigvalsh(a1-a0/4)[0] > 0
    assert la.eigvalsh(4*a0-a1)[0] > 0
    return a0, a1, relative, val[1:]


def spectral_motif(cutoff, scale):
    a0, a1, relative, lvals = motif_matrices()
    stiff, rot = la.eigh((a0+a1)/2)
    freq = np.sqrt(stiff/CHI)
    # Reference oscillator coordinates are the eigenvectors of A_mid.
    basis = occupation_basis(3, cutoff+2)
    lookup = {state: i for i, state in enumerate(basis)}
    dim = len(occupation_basis(3, cutoff))
    coords = []
    for mode in range(3):
        rows, cols, values = [], [], []
        for j, state in enumerate(basis):
            if state[mode]:
                dest = list(state)
                dest[mode] -= 1
                rows.append(lookup[tuple(dest)])
                cols.append(j)
                values.append(np.sqrt(state[mode]))
        ann = sp.csr_matrix((values, (rows, cols)), shape=(len(basis), len(basis)))
        coords.append((ann+ann.T)/np.sqrt(2*CHI*freq[mode]))
    v = rot.T@(a1-a0)@rot
    force_full = sum(v[i, j]*(coords[i]@coords[j])/2 for i in range(3) for j in range(3))
    force = force_full[:dim, :dim].toarray()
    field = np.diag((np.array(basis[:dim])+.5)@freq)
    h = (np.kron(scale*GEO, np.eye(dim))+np.kron(np.eye(2), field)
         + np.kron(np.diag([-.5, .5]), force))
    energies, vectors = la.eigh(h)
    ground = vectors[:, 0]
    gaps = energies[1:]-energies[0]
    assert gaps[0] > 0
    ground_matrix = ground.reshape(2, dim)
    rho = ground_matrix@ground_matrix.T
    purity = float(np.trace(rho@rho))
    assert purity < 1-1e-5
    # Lowest reference L0 mode in the midpoint eigenbasis.
    f = np.array([1., 0., 0.])
    observable_full = sum(x*q for x, q in zip(rot.T@f, coords))
    observable = np.kron(np.eye(2), observable_full[:dim, :dim].toarray())
    amplitudes = vectors.T@(observable@ground)
    assert abs(amplitudes[0]) < 1e-11
    weights = amplitudes[1:]**2
    mu = 2*CHI*gaps*weights
    omega = np.sqrt(KAPPA*lvals[0]/CHI)
    normalized_sum = float(np.sum(mu))
    inverse_moment = float(np.sum(mu/gaps**2))
    second_moment = float(np.sum(mu*gaps**2))
    expected_second = float(((1-rho[1, 1])*(f@a0@f)+rho[1, 1]*(f@a1@f))/CHI)
    variance = float(np.sum(weights))
    rows = []
    for nu in [0., .01, .1, .5, 1., 5., 20.]:
        value = float(np.sum(2*gaps*weights/(nu*nu+gaps*gaps)))
        lo, hi = 1/(CHI*(nu*nu+4*omega**2)), 1/(CHI*(nu*nu+omega**2/4))
        assert lo-1e-8 <= value <= hi+1e-8
        rows.append(dict(frequency=nu, response=value, lower=lo, upper=hi))
    band = (gaps >= omega/4) & (gaps <= 4*omega)
    energy_fraction = float(np.sum(mu[band])/np.sum(mu))
    ordinary_fraction = float(np.sum(weights[band])/np.sum(weights))
    assert energy_fraction >= .5 and ordinary_fraction >= 1/16
    assert inverse_moment <= 4/omega**2+1e-8
    assert second_moment <= 4*omega**2+1e-8
    assert 1/(4*CHI*omega) <= variance <= 1/(CHI*omega)
    assert 1/(2*CHI*variance) <= 2*omega
    parity = np.tile((-1.)**np.sum(basis[:dim], axis=1), 2)
    parity_error = float(la.norm(parity*ground-ground))
    assert parity_error < 1e-10
    # Cutoff defects are reported and convergence checked outside this function.
    return dict(total_occupation_cutoff=cutoff, geometry_scale=scale,
                joint_dimension=2*dim, relative_field_modes=3,
                ground_energy=float(energies[0]), ground_parity_error=parity_error,
                geometry_purity=purity, geometry_occupancy=float(rho[1, 1]),
                normalized_sum_rule=normalized_sum, sum_rule_defect=abs(normalized_sum-1),
                second_moment=second_moment, expected_second_moment=expected_second,
                third_sum_rule_defect=abs(second_moment-expected_second),
                inverse_second_moment=inverse_moment, equal_time_variance=variance,
                omega_reference=float(omega), energy_weighted_band_fraction=energy_fraction,
                unweighted_band_fraction=ordinary_fraction, response_rows=rows,
                scope='Fock compression of a canonical one-switch four-vertex path motif, not the full carrier spectrum.')


def solve(carrier, matrix, shift, source):
    operator = LinearOperator(matrix.shape,
        matvec=lambda x: matrix@x+shift*x+carrier.g*np.dot(carrier.g, x), dtype=float)
    inverse_diagonal = 1/(matrix.diagonal()+shift+1/carrier.n)
    preconditioner = LinearOperator(matrix.shape, matvec=lambda x: inverse_diagonal*x, dtype=float)
    value, info = cg(operator, source, M=preconditioner, rtol=2e-12, atol=2e-14, maxiter=6000)
    residual = la.norm(operator@value-source)
    assert info == 0 and residual < 1e-10
    return value, float(residual)


def carrier_histories(carrier, steps, beta=2.):
    dt = beta/steps
    nus = np.sqrt(2*(1-np.cos(2*np.pi*np.arange(steps)/steps)))/dt
    grams = [carrier.gram(float(nu)) for nu in nus]
    gram = np.block([[sum(np.cos(2*np.pi*n*(i-j)/steps)*grams[n] for n in range(steps))/steps
                      for j in range(steps)] for i in range(steps)])
    ev, basis = la.eigh(gram)
    assert ev[0] > 0
    root = (basis*np.sqrt(ev))@basis.T
    coefficients = []
    for s in range(2*steps):
        i = 2*s
        coefficients.append(KAPPA*(np.outer(root[:, i], root[:, i+1])+np.outer(root[:, i+1], root[:, i])))
    coefficients = np.array(coefficients)
    coords = np.array(list(itertools.product(range(24), range(12), range(12))))
    fx = np.cos(2*np.pi*coords[:, 0]/24)
    fy = np.cos(2*np.pi*coords[:, 1]/12)
    fx, fy = fx/la.norm(fx), fy/la.norm(fy)
    local = carrier.U[:, 0]/np.sqrt(2)
    us = sp.csr_matrix(carrier.U)
    a0 = (carrier.A-.5*us@sp.csr_matrix(sum(carrier.Js))@us.T).tocsr()
    assert la.norm(a0@fx-4*KAPPA*np.sin(np.pi/24)**2*fx) < 1e-12
    assert la.norm(a0@fy-4*KAPPA*np.sin(np.pi/12)**2*fy) < 1e-12
    names = [('long_x_static', fx, 0), ('long_x_time_mode_1', fx, 1),
             ('long_y_static', fy, 0), ('local_difference_static', local, 0)]
    probes, y_columns, reference, lowers, uppers = [], [], [], [], []
    max_residual = 0.
    for name, f, time_mode in names:
        g = np.cos(2*np.pi*time_mode*np.arange(steps)/steps)
        g /= la.norm(g)
        shift = CHI*nus[time_mode]**2
        inv, residual = solve(carrier, carrier.A, shift, f)
        inv_lo, rlo = solve(carrier, 4*a0, shift, f)
        inv_hi, rhi = solve(carrier, a0/4, shift, f)
        max_residual = max(max_residual, residual, rlo, rhi)
        compressed = np.kron(g, carrier.U.T@inv)
        y_columns.append(la.solve(root, compressed, assume_a='pos'))
        reference.append(float(f@inv))
        lowers.append(float(f@inv_lo))
        uppers.append(float(f@inv_hi))
        probes.append(dict(name=name, finite_grid_frequency=float(nus[time_mode]),
                           gaussian_lower=lowers[-1], gaussian_upper=uppers[-1]))
    y = np.column_stack(y_columns)
    reference = np.array(reference)
    lower, upper = np.array(lowers), np.array(uppers)
    gram_y = y.T@y
    log_weight_rows = {scale: [] for scale in [.2, 1., 4.]}
    transfers = {scale: la.expm(-dt*scale*GEO) for scale in log_weight_rows}
    all_variances, all_gamma, all_occupancies = [], [], []
    max_radius, max_correction_error = 0., 0.
    for start in range(0, 2**(2*steps), 256):
        labels = np.arange(start, min(2**(2*steps), start+256), dtype=np.uint64)
        bits = ((labels[:, None] >> np.arange(2*steps, dtype=np.uint64)) & 1).astype(int)
        perturb = ((bits-.5)@coefficients.reshape(2*steps, -1)).reshape(-1, 4*steps, 4*steps)
        spectrum, eigenvectors = np.linalg.eigh(perturb)
        max_radius = max(max_radius, float(np.max(abs(spectrum))))
        assert np.max(abs(spectrum)) <= 1/np.sqrt(3)+1e-11
        projections = np.einsum('bji,jp->bip', eigenvectors, y)
        # Woodbury correction using the symmetric relative operator.
        correction = np.sum((spectrum/(1+spectrum))[:, :, None]*projections**2, axis=1)
        variance = reference[None, :]-correction
        assert np.all(variance >= lower[None, :]-1e-9)
        assert np.all(variance <= upper[None, :]+1e-9)
        protected_response = 1/(4*KAPPA*np.sin(np.pi/12)**2)
        assert np.max(abs(variance[:, 2]-protected_response)) < 2e-12
        if start == 0:
            inv_action = np.linalg.solve(np.eye(4*steps)+perturb[0], y)
            alternate = reference-np.diag(gram_y)+np.sum(y*inv_action, axis=0)
            max_correction_error = max(max_correction_error, float(max(abs(alternate-variance[0]))))
            # Independently solve the full 27,648-dimensional space-time operator
            # for a nonconstant history, rather than reusing the low-rank formula.
            test = 1
            zpath = bits[test].reshape(steps, 2)
            def action(x):
                x = x.reshape(steps, carrier.n)
                out = (carrier.A@x.T).T+CHI*(2*x-np.roll(x, 1, axis=0)-np.roll(x, -1, axis=0))/dt**2
                for t in range(steps):
                    j = sum((zpath[t, s]-.5)*carrier.Js[s] for s in range(2))
                    out[t] += carrier.U@(j@(carrier.U.T@x[t]))
                out += (x@carrier.g)[:, None]*carrier.g[None, :]
                return out.ravel()
            full = LinearOperator((steps*carrier.n,)*2, matvec=action, dtype=float)
            f = names[-1][1]
            src = np.tile(f/np.sqrt(steps), steps)
            direct, info = cg(full, src, rtol=2e-11, atol=2e-13, maxiter=7000)
            full_residual = float(la.norm(full@direct-src))
            assert info == 0 and full_residual < 1e-9
            error = abs(float(src@direct)-variance[test, -1])
            assert error < 1e-9
            max_correction_error = max(max_correction_error, error)
        gamma = np.sum(np.log1p(spectrum), axis=1)/2
        paths = bits.reshape(-1, steps, 2)
        successor = np.roll(paths, -1, axis=1)
        for scale, transfer in transfers.items():
            logs = np.sum(np.log(transfer[paths, successor]), axis=(1, 2))
            log_weight_rows[scale].extend(logs.tolist())
        all_variances.extend(variance.tolist())
        all_gamma.extend(gamma.tolist())
        all_occupancies.extend(np.mean(paths, axis=1).tolist())
    variances = np.asarray(all_variances)
    gamma, occupancies = np.asarray(all_gamma), np.asarray(all_occupancies)
    averaged_rows = []
    for scale, logs in log_weight_rows.items():
        logs = np.asarray(logs)
        log_bare = logsumexp(logs)
        assert abs(log_bare-2*np.log1p(np.exp(-beta*scale*OMEGA))) < 2e-12
        normalized = np.exp(logs-gamma-logsumexp(logs-gamma))
        mean = normalized@variances
        variance_of_variance = normalized@(variances-mean)**2
        fourth = 3*(normalized@(variances**2))
        cumulant = 3*variance_of_variance
        subtraction_error = float(np.max(abs(fourth-3*mean**2-cumulant)))
        # The stable centered expression resolves small cumulants even when
        # the two uncentered fourth-order terms are about 10,000 each.
        assert subtraction_error < 5e-12*(1+np.max(abs(fourth)))
        assert np.min(cumulant) > -1e-15
        # Coupled local sources should have a detectable non-Gaussian mixture.
        assert cumulant[-1] > 1e-8
        mean_n = normalized@occupancies
        covariance_n_x2 = ((occupancies-mean_n).T@(normalized[:, None]*(variances-mean)))
        assert np.max(abs(covariance_n_x2[:, 2])) < 1e-11
        source_mgf_rows = []
        for amplitude in [.1, .3]:
            log_mgf = logsumexp((logs-gamma-logsumexp(logs-gamma))[:, None]
                                +amplitude**2*variances/2, axis=0)
            assert np.all(log_mgf >= amplitude**2*lower/2-1e-12)
            assert np.all(log_mgf <= amplitude**2*upper/2+1e-12)
            source_mgf_rows.append(dict(amplitude=amplitude, log_mgf=log_mgf.tolist()))
        averaged_rows.append(dict(geometry_scale=scale, occupancy=mean_n.tolist(),
            exact_grid_field_response=mean.tolist(), fourth_cumulant=cumulant.tolist(),
            cumulant_uncentered_subtraction_error=subtraction_error,
            excess_kurtosis=(cumulant/mean**2).tolist(),
            geometry_field_squared_covariance=covariance_n_x2.tolist(), mgf_rows=source_mgf_rows))
    return dict(time_steps=steps, inverse_temperature=beta, histories=2**(2*steps),
                field_vertices=carrier.n, relative_field_modes=carrier.n-1,
                probes=probes, geometry_rows=averaged_rows,
                max_history_relative_radius=max_radius,
                max_cg_residual=max_residual,
                full_space_time_cg_residual=full_residual,
                largest_independent_covariance_error=max_correction_error,
                protected_transverse_response=float(protected_response),
                scope='Exact correlated history sum and untruncated Gaussian field on the specified finite Euclidean grid; no time-grid convergence rate.')


def protected_sector(carrier):
    # All 144 transverse profiles, including the one constant later removed.
    embedding = np.tile(np.eye(144), (24, 1))/np.sqrt(24)
    lap1 = 2*np.eye(12)-np.roll(np.eye(12), 1, axis=1)-np.roll(np.eye(12), -1, axis=1)
    lap2 = np.kron(lap1, np.eye(12))+np.kron(np.eye(12), lap1)
    isometry_error = float(la.norm(embedding.T@embedding-np.eye(144)))
    source_error = float(la.norm(carrier.U.T@embedding))
    intertwining_error = float(la.norm(carrier.A@embedding-KAPPA*embedding@lap2))
    assert isometry_error < 1e-12 and source_error == 0 and intertwining_error < 1e-12
    # This simultaneously verifies all switch configurations: U^T T=0
    # annihilates each perturbation, without a mean-geometry approximation.
    rng = np.random.default_rng(9013)
    continuum = []
    slope = np.sqrt(KAPPA/CHI)
    for a in [.2, .1, .05, .025]:
        momenta = rng.normal(size=(100, 2))
        norm = la.norm(momenta, axis=1)
        freq = slope*la.norm(2*np.sin(a*momenta/2), axis=1)/a
        errors = abs(freq-slope*norm)
        bounds = slope*a*a*norm**3/24
        assert np.all(errors <= bounds+1e-13)
        continuum.append(dict(spacing=a, momentum_cases=100,
                               largest_frequency_error=float(max(errors)),
                               largest_error_to_bound=float(max(errors/bounds))))
    # Two independent normalizations of the free transverse shear spectrum.
    theta, r = sy.symbols('theta r', real=True)
    angular = sy.integrate(sy.cos(theta)**2*sy.sin(theta)**2, (theta, 0, 2*sy.pi))
    assert angular == sy.pi/4
    radial = sy.integrate(r*((1+r*r)**-3-3*r*r*(1+r*r)**-4
                             +sy.Rational(9, 4)*r**4*(1+r*r)**-5), (r, 0, sy.oo))
    assert radial == sy.Rational(3, 32)
    # Fourier convention: integral dt d^2x exp(i omega t-ik.x) <O(t,x)O(0)>.
    # O = :partial_y phi partial_z phi:, S(omega,0)=omega^3/(256 chi^2 c^6).
    euclidean_coefficient = radial/(8*sy.pi)
    laplace_coefficient = sy.factorial(3)/(512*sy.pi)
    assert euclidean_coefficient == laplace_coefficient
    return dict(protected_relative_modes=143, all_relative_modes=carrier.n-1,
                isometry_error=isometry_error, all_switch_source_annihilation_error=source_error,
                stiffness_intertwining_error=intertwining_error,
                exact_protected_spatial_momenta='k_x=0; nonzero (k_y,k_z)',
                all_orders_geometry_backreaction_from_free_factor=0,
                continuum_rows=continuum,
                free_shear_spectrum='omega^3 theta(omega)/(256 chi^2 c^6)',
                shear_angular_integral=str(angular), shear_euclidean_radial_integral=str(radial),
                scope='Exact invariant Gaussian factor of the full supplied Hamiltonian; free transverse scalar poles and two-particle shear continuum, not gravitational modes.')


def spin_diagnostic():
    # Exact algebra: a single spin-half has no on-site traceless quadrupole.
    spins = [sy.Matrix([[0, 1], [1, 0]])/2,
             sy.Matrix([[0, -sy.I], [sy.I, 0]])/2,
             sy.diag(1, -1)/2]
    for i, j in itertools.product(range(3), repeat=2):
        q = (spins[i]*spins[j]+spins[j]*spins[i])/2-(sy.eye(2)/4 if i == j else sy.zeros(2))
        assert q == sy.zeros(2)
    block = []
    for component in spins:
        total = sy.zeros(16)
        for site in range(4):
            factors = [sy.eye(2) for _ in range(4)]
            factors[site] = component
            total += sy.kronecker_product(*factors)
        block.append(total)
    casimir = sum((j*j for j in block), sy.zeros(16))
    multiplicities = casimir.eigenvals()
    assert multiplicities == {sy.Integer(0): 2, sy.Integer(2): 9, sy.Integer(6): 5}
    # The internal spin-2 multiplet exists; no Hamiltonian, spatial rotation
    # identification, gauge constraints, or massless dispersion follows.
    a, b, c, s = sy.symbols('a b c s', real=True)
    rotation = sy.Matrix([[c, -s], [s, c]])
    tensor = sy.Matrix([[a, b], [b, -a]])
    transformed = sy.expand(rotation*tensor*rotation.T)
    assert sy.expand(transformed[0, 0]-((c*c-s*s)*a-2*c*s*b)) == 0
    assert sy.expand(transformed[0, 1]-(2*c*s*a+(c*c-s*s)*b)) == 0
    return dict(single_spin_half_quadrupole_zero_components=9,
                four_spin_half_block_dimension=16,
                total_spin_squared_multiplicities={str(k): int(v) for k, v in multiplicities.items()},
                spin_two_multiplet_dimension=5, rank_two_double_angle_identity=True,
                scope='Internal angular-momentum representation algebra only. It does not establish a physical spatial helicity-two pole or gravity in the repository Hamiltonian.')


def atomless_counterexample():
    omega, chi = .2, CHI
    a, b = omega**2/4, 4*omega**2
    points, weights = np.polynomial.legendre.leggauss(160)
    y = (a+b)/2+(b-a)*points/2
    weights = weights/2
    rows = []
    for nu in [0., .01, .1, .5, 1., 10.]:
        value = np.log1p((b-a)/(nu**2+a))/(chi*(b-a))
        direct = np.sum(weights/(nu*nu+y))/chi
        assert abs(value-direct) < 1e-10
        lo, hi = 1/(chi*(nu*nu+b)), 1/(chi*(nu*nu+a))
        assert lo <= value <= hi
        rows.append(dict(frequency=nu, response=float(value), lower=lo, upper=hi))
    return dict(energy_squared_distribution='Uniform on [omega^2/4, 4 omega^2]',
                omega=omega, has_spectral_atom=False, response_rows=rows,
                inverse_second_moment=float(np.log(b/a)/(b-a)), second_moment=float((a+b)/2),
                scope='Counterexample to inferring an isolated wave pole from the bounds; not a proposed spectrum of the repository model.')


def main():
    root = Path(__file__).resolve().parents[1]
    spectral = [spectral_motif(cutoff, scale) for scale in [.2, 1., 4.] for cutoff in [6, 10, 14]]
    for i in range(0, len(spectral), 3):
        coarse, middle, fine = spectral[i:i+3]
        assert fine['sum_rule_defect'] < middle['sum_rule_defect'] < coarse['sum_rule_defect']
        assert fine['sum_rule_defect'] < 2e-7
        assert fine['third_sum_rule_defect'] < 2e-6
        assert abs(fine['ground_energy']-middle['ground_energy']) < 1e-7
        assert abs(fine['geometry_purity']-middle['geometry_purity']) < 1e-6
    carrier = GaussianCarrier(change_reference(MeanCell(), .5))
    grids = [carrier_histories(carrier, steps) for steps in [4, 6, 8]]
    report = dict(finite_spectral_checks=spectral, full_carrier_history_sums=grids,
                  protected_transverse_sector=protected_sector(carrier), spin_diagnostic=spin_diagnostic(),
                  atomless_response=atomless_counterexample(),
                  analytical_constants=dict(energy_weighted_band_fraction=.5,
                      unweighted_band_fraction=1/16, lower_energy_over_reference=.25,
                      upper_energy_over_reference=4., variational_gap_upper_factor=2.,
                      reference_small_wave_number_slope=float(np.sqrt(6)*KAPPA)))
    sources = ['ENTANGLED_ACOUSTIC_BOUNDS.md', 'scripts/entangled_acoustic_audit.py',
               'UnifiedTheory/Audit/KFCausalEntangledAcoustic.lean',
               'COLLECTIVE_GEOMETRY_STABILITY.md', 'scripts/collective_geometry_stability_audit.py',
               'scripts/induced_geometry_audit.py', 'scripts/finite_gap_feedback_audit.py',
               'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    report['scope'] = ('Exact full entangled large-spin covariance and acoustic spectral-weight bounds; '
                       'unique even and entangled finite-volume relative-field ground state. '
                       'Exact free transverse wave poles, but no general three-dimensional wave-pole theorem. '
                       'No theorem of geometry thermodynamic uniqueness or physical spin-half phase, '
                       'regulator selection, universal matter coupling, or Einstein gravity.')
    (root/'data/entangled_acoustic_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
