#!/usr/bin/env python3
"""Positive Gaussian transfer, uniform coefficient locality, and off-axis TT response.

The response is an external-source Hessian, not a proved spin-phase spectrum.
Numerical checks support the analytical arguments in the accompanying note;
they are not interval certificates or a Lean proof.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigvalsh
from scipy.special import roots_hermite
import sympy as sy


def symbolic_moments():
    c = sy.Symbol('c', positive=True)
    sh = sy.sqrt(c*c-1)
    moments = [1/(2*sh)]
    for power in range(1, 4):
        moments.append(sy.diff(moments[-1], c)/(-2*power))
    targets = [c/(4*sh**3), (2*c*c+1)/(16*sh**5),
               c*(2*c*c+3)/(32*sh**7)]
    for actual, target in zip(moments[1:], targets):
        assert sy.simplify(actual-target) == 0
    sine_moment = (1-c*c)*moments[3]+c*moments[2]-moments[1]/4
    assert sy.simplify(sine_moment-c/(32*sh**5)) == 0
    return dict(derivative_recursion=True, sine_squared_fourth_moment=True)


def frequency_checks():
    rng = np.random.default_rng(95304)
    rows = []
    for _ in range(12):
        ea, eb = rng.uniform(.15, 3, 2)
        p = float(rng.uniform(-np.pi, np.pi))
        def integrand(nu):
            return 1/(4*(np.cosh(ea)-np.cos(nu))*
                      (np.cosh(eb)-np.cos(nu+p)))/(2*np.pi)
        actual, error = quad(integrand, -np.pi, np.pi,
                             epsabs=1e-12, epsrel=1e-11, limit=200)
        target = np.sinh(ea+eb)/(4*np.sinh(ea)*np.sinh(eb)*
                                (np.cosh(ea+eb)-np.cos(p)))
        assert abs(actual-target) < 2e-10
        rows.append(dict(energies=[float(ea), float(eb)], frequency=p,
                         absolute_error=float(abs(actual-target)),
                         quadrature_error=float(error)))
    return dict(cases=rows)


def tt_basis(raw_direction):
    n = np.asarray(raw_direction, dtype=float)
    n /= np.linalg.norm(n)
    u = np.cross(n, np.eye(3)[np.argmin(abs(n))])
    u /= np.linalg.norm(u)
    v = np.cross(n, u)
    tensors = np.array([(np.outer(u, u)-np.outer(v, v))/np.sqrt(2),
                        (np.outer(u, v)+np.outer(v, u))/np.sqrt(2)])
    assert np.max(abs(tensors @ n)) < 1e-14
    assert np.max(abs(np.trace(tensors, axis1=1, axis2=2))) < 1e-14
    assert np.max(abs(np.einsum('aij,bij->ab', tensors, tensors)-np.eye(2))) < 1e-14
    return n, tensors


def grid(points, mass):
    q1 = (np.arange(points)+.5)*2*np.pi/points-np.pi
    q = np.array(np.meshgrid(q1, q1, q1, indexing='ij')).reshape(3, -1)
    sine, cosine = np.sin(q), np.cos(q)
    stiffness = mass*mass+2*np.sum(1-cosine, axis=0)
    c = 1+stiffness/2
    sh = np.sqrt(stiffness*(1+stiffness/4))
    return dict(q=q, sine=sine, cosine=cosine, stiffness=stiffness, c=c, sh=sh,
                i2=c/(4*sh**3), i3=(2*c*c+1)/(16*sh**5),
                i4=c*(2*c*c+3)/(32*sh**7))


def contract(left, tensors, right):
    return np.einsum('ix,aij,jx->ax', left, tensors, right)


def gram(left, right, weight):
    return np.einsum('ax,bx,x->ab', left, right, weight)/weight.size


def response(data, raw_direction):
    n, tensors = tt_basis(raw_direction)
    s, co = data['sine'], data['cosine']
    v0 = contract(s, tensors, s)
    v2 = -.25*(contract(s*n[:, None]**2, tensors, s)+
                contract(co*n[:, None], tensors, co*n[:, None]))
    d1 = 2*n @ s
    d2 = 2*(n*n) @ co
    zt = gram(v0, v0, data['c']/(32*data['sh']**5))
    propagator_part = gram(v0, v0, (d2*data['i3']-d1*d1*data['i4'])/8)
    vertex_part = -.5*(gram(v2, v0, data['i2'])+gram(v0, v2, data['i2']))
    zs = propagator_part+vertex_part
    return dict(n=n, tensors=tensors, v0=v0, v2=v2, time=zt, space=zs,
                propagator_part=propagator_part, vertex_part=vertex_part,
                ratios=eigvalsh(zs, zt))


DIRECTIONS = [[0, 0, 1], [1, 1, 0], [1, 1, 1], [1, 2, 3]]


def directional_checks():
    rows = []
    previous = {}
    for points in [32, 64, 96]:
        data = grid(points, 0.)
        for raw in DIRECTIONS:
            r = response(data, raw)
            if points == 96:
                if raw == [0, 0, 1]:
                    assert np.max(abs(r['ratios']-1)) < .002
                    assert np.max(abs(r['vertex_part'])) < 1e-17
                else:
                    assert min(r['ratios']) > 2.9
                assert np.max(abs(r['ratios']-previous[tuple(raw)])) < .004
            previous[tuple(raw)] = r['ratios']
            rows.append(dict(points_per_axis=points, scalar_mass=0., direction=raw,
                             time_matrix=r['time'].tolist(), space_matrix=r['space'].tolist(),
                             vertex_correction=r['vertex_part'].tolist(),
                             projected_squared_response_ratios=r['ratios'].tolist()))
    return dict(cases=rows, normalization='Frobenius-orthonormal TT tensors; one real scalar; gamma squared and lattice spacing are one.',
                scope='Generalized eigenvalues of the TT-projected source Hessian. Off-axis mixing with other strain components and the absence of constraints preclude identifying these with physical graviton speeds. Massless integrals use midpoint quadrature with an infrared convergence check.')


def finite_momentum_checks():
    data = grid(48, .2)
    rows = []
    for raw in DIRECTIONS:
        r = response(data, raw)
        base = gram(r['v0'], r['v0'], data['i2'])
        errors = []
        for p in [.04, .02, .01]:
            plus = data['q']+p*r['n'][:, None]/2
            minus = data['q']-p*r['n'][:, None]/2
            vp = contract(np.sin(plus), r['tensors'], np.sin(minus))
            la = .2**2+2*np.sum(1-np.cos(plus), axis=0)
            lb = .2**2+2*np.sum(1-np.cos(minus), axis=0)
            ea, eb = 2*np.arcsinh(np.sqrt(la)/2), 2*np.arcsinh(np.sqrt(lb)/2)
            bubble = np.sinh(ea+eb)/(4*np.sinh(ea)*np.sinh(eb)*(np.cosh(ea+eb)-1))
            actual = -.5*(gram(vp, vp, bubble)-base)/(p*p)
            error = np.linalg.norm(actual-r['space'])/np.linalg.norm(r['space'])
            errors.append(error)
            rows.append(dict(direction=raw, momentum=p, relative_space_coefficient_error=float(error)))
        assert errors[-1] < 3e-5
        assert 3.8 < errors[0]/errors[1] < 4.2
        assert 3.8 < errors[1]/errors[2] < 4.2
        # A separate finite-frequency difference uses the exact spectral bubble.
        energy = 2*np.arcsinh(np.sqrt(data['stiffness'])/2)
        denom0 = np.cosh(2*energy)-1
        for frequency in [.02, .01]:
            shift = 2*np.sin(frequency/2)**2
            weight = .5*data['i2']*shift/(denom0+shift)/frequency**2
            actual = gram(r['v0'], r['v0'], weight)
            error = np.linalg.norm(actual-r['time'])/np.linalg.norm(r['time'])
            assert error < .0007
            rows.append(dict(direction=raw, frequency=frequency,
                             relative_time_coefficient_error=float(error)))
    return dict(cases=rows, points_per_axis=48, scalar_mass=.2,
                scope='Independent unexpanded finite-momentum bubble, after subtracting its zero-momentum mass matrix. Subtraction is supplied tuning, not protected masslessness.')


def vertex_checks():
    rng = np.random.default_rng(95305)
    errors = []
    for _ in range(32):
        n, tensors = tt_basis(rng.normal(size=3))
        q = rng.uniform(-np.pi, np.pi, (3, 20))
        s, co = np.sin(q), np.cos(q)
        v0 = contract(s, tensors, s)
        v2 = -.25*(contract(s*n[:, None]**2, tensors, s)+
                    contract(co*n[:, None], tensors, co*n[:, None]))
        local_errors = []
        for p in [.02, .01]:
            a, b = s*np.cos(p*n[:, None]/2), co*np.sin(p*n[:, None]/2)
            exact = contract(np.sin(q+p*n[:, None]/2), tensors,
                             np.sin(q-p*n[:, None]/2))
            assert np.max(abs(exact-contract(a, tensors, a)+contract(b, tensors, b))) < 2e-15
            local_errors.append(np.max(abs(exact-v0-p*p*v2)))
        assert local_errors[1] < 1e-9
        assert 15 < local_errors[0]/local_errors[1] < 17
        errors.append(float(local_errors[1]))
    return dict(cases=32, largest_vertex_remainder_at_p_001=max(errors),
                exact_shift_identity=True, fourth_order_remainder_scaling=True)


def coefficient_a(z):
    z = np.asarray(z)
    result = np.ones_like(z, dtype=np.result_type(z, float))
    nonzero = z != 0
    result[nonzero] = 2*np.arcsinh(np.sqrt(z[nonzero])/2)/(
        np.sqrt(z[nonzero])*np.sqrt(1+z[nonzero]/4))
    return result


def transfer_checks():
    rows = []
    for stiffness in [.1, .5, 2., 8., 12.]:
        energy = 2*np.arcsinh(np.sqrt(stiffness)/2)
        a = float(coefficient_a(stiffness))
        b = stiffness*(1+stiffness/4)*a
        assert abs(np.sqrt(a*b)-energy) < 1e-14
        assert abs(energy/(a*np.sinh(energy))-1) < 1e-14
        for nodes in [80, 120]:
            x, w = roots_hermite(nodes)
            logw = np.log(w)/2
            # Symmetric Nystrom discretization with Hermite quadrature.
            kernel = np.exp(logw[:, None]+logw[None, :]-stiffness/4*(
                x[:, None]**2+x[None, :]**2)+x[:, None]*x[None, :])/np.sqrt(2*np.pi)
            eigenvalues = np.linalg.eigvalsh(kernel)
            target = np.exp(-energy*(np.arange(5)+.5))
            error = np.max(abs(eigenvalues[-5:][::-1]-target))
            assert error < (3e-10 if nodes == 80 else 2e-13)
            assert eigenvalues.min() > -3e-15
            rows.append(dict(stiffness=stiffness, quadrature_nodes=nodes,
                             first_five_eigenvalue_max_error=float(error),
                             smallest_numerical_eigenvalue=float(eigenvalues.min())))
    return dict(cases=rows,
                scope='Mehler kernel checked against an independently discretized positive integral operator. Tiny negative numerical eigenvalues are roundoff; positivity follows analytically from the symmetric transfer product.')


def locality_checks():
    angles = 2*np.pi*np.arange(512)/512
    circle = 6+8*np.exp(1j*angles)
    values = coefficient_a(circle)
    assert max(abs(values)) < 2
    coefficients = (np.fft.fft(values)/512)[:40]/(8.**np.arange(40))
    assert max(abs(coefficients.imag)) < 1e-14
    coefficients = coefficients.real
    z = np.linspace(0, 12, 1001)
    amin = float(coefficient_a(12.))
    rows = []
    for degree in [13, 20, 30]:
        polynomial = np.polynomial.polynomial.polyval(z-6, coefficients[:degree+1])
        bound = 8*.75**(degree+1)
        error = max(abs(polynomial-coefficient_a(z)))
        assert error < bound < amin/2
        assert min(polynomial) >= amin-bound
        rows.append(dict(degree=degree, max_sampled_error=float(error),
                         analytical_uniform_error_bound=bound,
                         sampled_minimum=float(min(polynomial)),
                         analytical_positive_lower_bound=amin-bound,
                         relative_quadratic_form_error_bound=bound/amin))
    # An independent periodic matrix check: polynomial support is exactly finite.
    size = 81
    lap = 2*np.eye(size)-np.roll(np.eye(size), 1, axis=1)-np.roll(np.eye(size), -1, axis=1)
    eigen, basis = np.linalg.eigh(lap)
    eigen = np.maximum(eigen, 0.)
    exact_a = (basis*coefficient_a(eigen)) @ basis.T
    exact_b = (basis*(eigen*(1+eigen/4)*coefficient_a(eigen))) @ basis.T
    shifted = lap-6*np.eye(size)
    polynomial = coefficients[13]*np.eye(size)
    for coefficient in coefficients[12::-1]:
        polynomial = polynomial @ shifted+coefficient*np.eye(size)
    polynomial_b = lap @ (np.eye(size)+lap/4) @ polynomial
    offsets = abs(np.arange(size)[:, None]-np.arange(size)[None, :])
    distance = np.minimum(offsets, size-offsets)
    assert np.max(abs(polynomial[distance > 13])) < 1e-15
    assert np.max(abs(polynomial_b[distance > 15])) < 1e-15
    assert np.max(abs(exact_a)-8*.75**distance) <= 1e-13
    assert np.max(abs(exact_b)-384*.75**np.maximum(distance-2, 0)) <= 1e-13
    assert np.linalg.eigvalsh(polynomial).min() > 0
    return dict(polynomials=rows, periodic_matrix_size=size,
                polynomial_a_range=13, polynomial_b_range=15,
                coefficient_a_at_12=amin,
                scope='Analytical bounds hold for any nearest-neighbor cubic Laplacian with spectrum in [0,12], uniformly in volume. The finite matrix is a check in one dimension. These are Gaussian coefficient and relative energy-form bounds, not bounded-operator-norm locality of interacting spin dynamics.')


def full_temporal_gram():
    data = grid(32, .2)
    sx, sy_, sz = data['sine']
    vertices = np.array([sx*sx, sy_*sy_, sz*sz, np.sqrt(2)*sx*sy_,
                         np.sqrt(2)*sy_*sz, np.sqrt(2)*sz*sx])
    matrix = gram(vertices, vertices, data['c']/(32*data['sh']**5))
    eigenvalues = np.linalg.eigvalsh(matrix)
    assert eigenvalues.min() > 1e-5
    return dict(eigenvalues=eigenvalues.tolist(), rank=6,
                scope='Positive weighted Gram matrix; no gravitational constraint reduction follows.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_moments(), frequency=frequency_checks(),
                  vertex=vertex_checks(), directional_response=directional_checks(),
                  finite_momentum=finite_momentum_checks(), transfer=transfer_checks(),
                  locality=locality_checks(), temporal_gram=full_temporal_gram())
    sources = ['ISOTROPIC_TENSOR_REGULATOR.md', 'scripts/isotropic_tensor_regulator_audit.py',
               'INDUCED_TENSOR_DYNAMICS.md', 'scripts/induced_tensor_dynamics_audit.py',
               'SPIN_CLOCK_BRACKET.md', 'EINSTEIN_MODEL_DECISION.md',
               'GRAVITY_FROM_CLOCK_CONSTRAINTS.md', 'COMPACT_TENSOR_DYNAMICS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('The isotropic Euclidean Gaussian scalar has a positive transfer operator, '
                       'exponentially local Hamiltonian coefficients and positive finite-range approximants. '
                       'It repairs the axial TT response ratio but fails generic-direction Einstein matching '
                       'for the specified centered-derivative source. No full interacting spin locality theorem, '
                       'graviton phase, nonlinear constraint algebra, or TOE is proved.')
    target = root/'data/isotropic_tensor_regulator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(report=str(target), directional_cases=12, finite_momentum_cases=20,
                          frequency_cases=12, vertex_cases=32, transfer_cases=10,
                          finite_range_approximants=3, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
