#!/usr/bin/env python3
"""Projection, finite-qudit Berry control, and identical z=1/z=3 vacua.

Separates exact finite-code projection and Gaussian reduction from a
thermodynamic finite-spin gravitational phase, which is not proved here.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.integrate import quad

from prepotential_lattice_bridge_audit import continuum_operators


def discrete_gaussian(prime, center, momentum, variance_parameter):
    indices = np.arange(-(prime//2), prime//2+1)
    x = np.sqrt(2*np.pi/prime)*indices
    state = np.exp(-(x-center)**2/(2*variance_parameter)+
                   1j*momentum*(x-center/2))
    return state/la.norm(state)


def physical_pair(prime, center, momentum, variance_parameter, pair=True):
    indices = np.arange(-(prime//2), prime//2+1)
    x = np.sqrt((4 if pair else 2)*np.pi/prime)*indices
    state = np.exp(-(x-center)**2/(2*variance_parameter)+1j*momentum*x)
    return state/la.norm(state)


def tensor_product(vectors):
    state = vectors[0]
    for vector in vectors[1:]:
        state = np.multiply.outer(state, vector)
    return state


def six_qudit_projection(prime, h, p, variance_parameter):
    # Component order xx, yy, zz, xy, yz, zx. Three X checks on zz,yz,zx;
    # scalar Z check on xx+yy. Odd-prime centered representatives obey
    # centered(-n)=-centered(n), including near the finite boundary.
    vectors = [discrete_gaussian(prime, x, y, variance_parameter) for x, y in zip(h, p)]
    state = tensor_product(vectors)
    labels = np.arange(-(prime//2), prime//2+1)
    mask = ((labels[:, None]+labels[None, :]) % prime == 0)
    state *= mask[:, :, None, None, None, None]
    for axis in [2, 4, 5]:
        state = np.broadcast_to(state.mean(axis=axis, keepdims=True), (prime,)*6).copy()
    probability = float(np.vdot(state.ravel(), state.ravel()).real)
    assert probability > 0
    state /= np.sqrt(probability)
    plus = np.ones(prime)/np.sqrt(prime)
    pair = physical_pair(prime, (h[0]-h[1])/np.sqrt(2),
                         (p[0]-p[1])/np.sqrt(2), variance_parameter)
    shear = physical_pair(prime, h[3], p[3], variance_parameter, pair=False)
    encoded = np.zeros((prime, prime), complex)
    encoded[np.arange(prime), np.arange(prime-1, -1, -1)] = pair
    expected = (encoded[:, :, None, None, None, None]*
                plus[None, None, :, None, None, None]*
                shear[None, None, None, :, None, None]*
                plus[None, None, None, None, :, None]*
                plus[None, None, None, None, None, :])
    error = float(1-abs(np.vdot(expected.ravel(), state.ravel()))**2)
    assert abs(error) < 2e-12
    pair_probability = np.sum(abs(vectors[0]*vectors[1][::-1])**2)
    prediction = pair_probability*np.prod([abs(np.vdot(plus, vectors[a]))**2 for a in [2, 4, 5]])
    assert abs(probability-prediction) < 2e-13
    return state, probability, error


def finite_projection_checks():
    rows = []
    h = np.array([.17, -.17, .21, -.13, -.19, .12])
    p = np.array([.23, -.23, 0., .16, 0., 0.])
    for prime in [3, 5, 7]:
        for variance_parameter in [.6, 1.4]:
            state, probability, error = six_qudit_projection(prime, h, p, variance_parameter)
            for check in [2, 4, 5]:
                assert la.norm((np.roll(state, 1, axis=check)-state).ravel()) < 2e-12
            shifted_h = h+np.array([0., 0., .3, 0., -.4, .2])
            shifted_p = p+np.array([.37, .37, 0., 0., 0., 0.])
            shifted, shifted_probability, _ = six_qudit_projection(
                prime, shifted_h, shifted_p, variance_parameter)
            fidelity = float(abs(np.vdot(state.ravel(), shifted.ravel()))**2)
            assert abs(fidelity-1) < 3e-12
            rows.append(dict(prime=prime, variance_parameter=variance_parameter,
                             direct_code_projection_probability=probability,
                             shifted_projection_probability=shifted_probability,
                             logical_gaussian_ray_error=error, gauge_ray_fidelity=fidelity))
    return dict(cases=rows, scope='Direct full vectors in a six-qudit axis-momentum constraint benchmark. Projection exactly removes the nominal gauge dependence and leaves two discrete-Gaussian logical coordinates. This is not a computation of the full spatial tensor-code wavefunction.')


def finite_berry(prime, variance_parameter, pair):
    indices = np.arange(-(prime//2), prime//2+1)
    d2 = (4 if pair else 2)*np.pi/prime
    x = np.sqrt(d2)*indices
    weights = np.exp(-x*x/variance_parameter)
    weights /= weights.sum()
    variance = float(np.dot(weights, x*x))
    eta = 2*variance/variance_parameter
    # Independent normalized-state tangent calculation at center=momentum=0.
    state = np.sqrt(weights)
    tangent_h = x*state/variance_parameter
    tangent_p = 1j*x*state
    actual_eta = float(2*np.vdot(tangent_h, tangent_p).imag)
    assert abs(actual_eta-eta) < 1e-13
    assert -1e-13 <= eta <= 1+1e-12
    b = d2/variance_parameter
    m = prime//2
    t = m*np.sqrt(b)
    if b <= 1 and t >= 1:
        a = np.pi**2/b
        ratio = math.exp(-a)
        alias = 4*a*ratio*(1+ratio)/(1-ratio)**3
        tail = math.e*(2*t*math.exp(-t*t)+math.sqrt(math.pi)*math.erfc(t))
        error_bound = min(1., alias+tail)
    else:
        error_bound = 1.
    assert 1-eta <= error_bound+2e-12
    saturation_bound = 2*d2*m*m/variance_parameter
    assert eta <= saturation_bound+1e-12
    return eta, error_bound, saturation_bound


def finite_berry_checks():
    rows = []
    for prime in [5, 11, 23, 47, 97, 193]:
        for wave_number in [1., .2, .04]:
            for pair in [False, True]:
                eta, bound, saturation = finite_berry(prime, 1/wave_number, pair)
                rows.append(dict(prime=prime, wave_number=wave_number, diagonal_pair=pair,
                                 canonical_berry_coefficient=eta,
                                 canonical_error_upper_bound=bound,
                                 finite_window_saturation_bound=saturation))
    for prime in [5, 23]:
        for pair in [False, True]:
            eta, _, _ = finite_berry(prime, 1e7, pair)
            d2 = (4 if pair else 2)*np.pi/prime
            expected = d2*(prime*prime-1)/(6*1e7)
            assert abs(eta/expected-1) < 2e-6
    return dict(cases=rows, scope='Finite logical-mode Gaussian states have exact gauge identification but a cutoff-dependent Berry coefficient. The analytical alias and tail bounds recover coefficient one when the logical cutoff grows sufficiently; fixed-prime infrared saturation is a statement about this encoding, not all finite-spin phases.')


def gaussian_projection_checks():
    rng, rows = np.random.default_rng(9112612), []
    for case in range(16):
        v = rng.normal(size=3)
        v *= rng.uniform(.1, 1.2)/la.norm(v)
        r, s, _, o, _, tt = continuum_operators(v)
        k = la.norm(v)
        image = la.eigh(tt)[1][:, -2:]
        rp, sp = image.conj().T @ r, image.conj().T @ s
        repaired = rp.conj().T @ sp
        assert la.norm(repaired-o) < 1e-11
        # Tensor coherent wavefunctions after real gauge averaging/restriction.
        width = k
        metric = la.block_diag(rp.conj().T @ rp/(2*width),
                              width*sp.conj().T @ sp/2)
        expected = .5*k**3*la.block_diag(tt, tt)
        assert la.norm(metric-expected) < 1e-11
        assert np.linalg.matrix_rank(metric, tol=1e-11) == 4
        # Uniformly positive input Gaussian precision cannot become critical
        # merely by eliminating gauge coordinates and fixing constrained ones.
        raw = rng.normal(size=(6, 6))
        precision = raw @ raw.T+.6*np.eye(6)
        # Three spatial-gauge directions, two physical ones, one fixed coordinate.
        waa, wat, wtt = precision[:3, :3], precision[:3, 3:5], precision[3:5, 3:5]
        effective = wtt-wat.T @ la.solve(waa, wat, assume_a='pos')
        lower, upper = min(la.eigvalsh(precision)), max(la.eigvalsh(precision))
        assert min(la.eigvalsh(effective)) >= lower-1e-12
        assert max(la.eigvalsh(effective)) <= upper+1e-12
        rows.append(dict(case=case, momentum=v.tolist(),
                         projected_berry_error=float(la.norm(repaired-o)),
                         projected_critical_metric_error=float(la.norm(metric-expected)),
                         projected_metric_rank=4,
                         input_precision_lower=float(lower),
                         reduced_precision_lower=float(min(la.eigvalsh(effective)))))
    return dict(cases=rows, scope='The exact noncompact Gaussian rigging map removes the gauge directions, preserves the physical Berry form, and retains the input physical width. Matrix checks also verify the uniform-precision Schur bound. No finite-spin thermodynamic projection theorem is inferred.')


def shared_vacuum_checks():
    rows, J, g = [], .7, 1.3
    for wave_number in [.025, .05, .1, .2, .4, .8]:
        k = wave_number
        precision = np.sqrt(g/J)*k
        reference_variance = 1/(2*precision)
        spectral = []
        for exponent in [1, 3]:
            a = J if exponent == 1 else J*k*k
            b = g*k*k if exponent == 1 else g*k**4
            omega = np.sqrt(a*b)
            assert abs(np.sqrt(b/a)-precision) < 1e-13
            # Independent spectral integral for the same equal-time variance.
            integral = quad(lambda u: a/(omega*(1+u*u))/np.pi,
                            0, np.inf, epsabs=1e-11, epsrel=1e-11)[0]
            assert abs(integral/reference_variance-1) < 1e-12
            spectral.append(dict(exponent=exponent, frequency=float(omega),
                                 equal_time_variance=float(integral),
                                 static_response=float(1/b),
                                 covariance_at_time_inverse_k=float(reference_variance*np.exp(-omega/k))))
        assert abs(spectral[1]['frequency']/spectral[0]['frequency']-k*k) < 1e-13
        rows.append(dict(wave_number=k, shared_ground_precision=float(precision),
                         shared_equal_time_variance=float(reference_variance),
                         two_dynamics=spectral))
    return dict(cases=rows, scope='The positive Gaussian tensor Hamiltonians with linear and cubic dispersion have exactly the same vacuum and displaced-state geometry at each nonzero mode. Their full time-dependent and zero-frequency responses differ. This does not prove the Gaussian phase of the compact five-state Hamiltonian.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(finite_code_projection=finite_projection_checks(),
                  finite_logical_berry=finite_berry_checks(),
                  gaussian_reduction=gaussian_projection_checks(),
                  shared_vacuum=shared_vacuum_checks())
    sources = ['PROJECTED_TENSOR_VACUUM.md', 'scripts/projected_tensor_vacuum_audit.py',
               'SPIN_STATE_GAUGE_GEOMETRY.md', 'PREPOTENTIAL_LATTICE_BRIDGE.md',
               'scripts/prepotential_lattice_bridge_audit.py',
               'COMPACT_TENSOR_CONSTRAINTS.md', 'COMPACT_TENSOR_DYNAMICS.md',
               'COMPACT_CONSTRAINT_NORMALIZER.md', 'BOND_TENSOR_CONSTRAINTS.md',
               'EINSTEIN_MODEL_DECISION.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Exact projection in a six-qudit tensor constraint benchmark removes gauge-ray '
                       'distinguishability. The finite logical Gaussian Berry coefficient has explicit '
                       'cutoff errors and saturates in the infrared at fixed prime. A noncompact Gaussian '
                       'rigging map repairs the prepotential state quotient but does not create a critical '
                       'width from uniformly bounded Gaussian precision. The linear and cubic tensor '
                       'Gaussian Hamiltonians have the same vacuum and different time response. No local '
                       'finite-spin gravitational phase, nonlinear Einstein gravity, or TOE is proved. No Lean theorem.')
    target = root/'data/projected_tensor_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
