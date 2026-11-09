#!/usr/bin/env python3
"""Distinguish embedding covariance from an independent gravitational phase."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy


ETA = np.diag([-1., 1., 1., 1.])
EPS = np.array([[[int(sy.LeviCivita(i, j, k)) for k in range(3)]
                 for j in range(3)] for i in range(3)])


def norm(a):
    return float(la.norm(np.asarray(a).ravel()))


def exact_identities():
    t, x = sy.symbols('t x', real=True)
    q = x*x-t*t
    e, n = sy.Matrix([t, x]), sy.Matrix([x, t])/sy.sqrt(q)
    eta = sy.diag(-1, 1)
    assert sy.simplify((n.T*eta*n)[0]+1) == 0
    assert sy.simplify((n.T*eta*e)[0]) == 0
    assert (n.jacobian([t, x])*n-e/q).applyfunc(sy.simplify) == sy.zeros(2, 1)
    tp, xp, xi, dxi = sy.symbols('tp xp xi dxi', real=True)
    de = dxi*e+xi*sy.Matrix([tp, xp])
    assert sy.expand(2*(e.T*eta*de)[0]-xi*2*(x*xp-t*tp)-2*dxi*q) == 0
    a, w = sy.symbols('a w', real=True)
    assert sy.simplify((1-1/(1+a))*w-a*w/(1+a)) == 0
    return dict(normal_normal_coefficient=True, spatial_metric_lie_derivative=True,
                independent_metric_mismatch=True,
                scope="Exact symbolic identities. The general three-dimensional Poisson-algebra proof is in the note, not an exact finite lattice or continuum quantum theorem.")


def normal(e):
    velocity = la.solve(e[:, 1:], e[:, 0])
    return np.r_[1., velocity]/np.sqrt(1-velocity @ velocity)


def normal_derivative(e, de):
    n = normal(e)
    return -e.T @ la.solve(e @ ETA @ e.T, de @ ETA @ n)


def embedding_variations():
    rng, rows, step = np.random.default_rng(9112641), [], 2e-6
    for case in range(10):
        spatial = np.eye(3)+.1*rng.normal(size=(3, 3))
        velocity = rng.normal(size=3)
        velocity *= (.1+.06*case)/la.norm(velocity)
        e = np.column_stack([spatial @ velocity, spatial])
        n, q = normal(e), e @ ETA @ e.T
        second = .2*rng.normal(size=(3, 3, 4))
        second = (second+second.swapaxes(0, 1))/2
        dn = np.array([normal_derivative(e, second[:, i, :]) for i in range(3)])
        lapse_n, lapse_m = rng.normal(size=2)
        grad_n, grad_m = rng.normal(size=(2, 3))
        de_n = grad_n[:, None]*n+lapse_n*dn
        de_m = grad_m[:, None]*n+lapse_m*dn
        var_n = (normal(e+step*de_n)-normal(e-step*de_n))/(2*step)
        var_m = (normal(e+step*de_m)-normal(e-step*de_m))/(2*step)
        shift = la.solve(q, lapse_n*grad_m-lapse_m*grad_n)
        bracket_error = norm(lapse_m*var_n-lapse_n*var_m+e.T @ shift)
        assert bracket_error < 3e-8
        curvature = e @ ETA @ dn.T
        normal_metric_error = norm(de_n @ ETA @ e.T+e @ ETA @ de_n.T-2*lapse_n*curvature)
        assert normal_metric_error < 3e-12
        xi, dxi = rng.normal(size=3), rng.normal(size=(3, 3))
        de_xi = dxi @ e+np.einsum('j,ijm->im', xi, second)
        dq = np.array([second[:, k, :] @ ETA @ e.T+e @ ETA @ second[:, k, :].T
                       for k in range(3)])
        lie = np.einsum('k,kij->ij', xi, dq)+dxi @ q+q @ dxi.T
        spatial_error = norm(de_xi @ ETA @ e.T+e @ ETA @ de_xi.T-lie)
        assert spatial_error < 3e-12
        rows.append(dict(case=case, minimum_metric_eigenvalue=float(min(la.eigvalsh(q))),
                         normal_commutator_finite_difference_error=bracket_error,
                         normal_metric_variation_error=normal_metric_error,
                         spatial_metric_variation_error=spatial_error))
    return dict(cases=rows, scope="General embedding tangents and second derivatives at a point. The normal commutator is checked by independently perturbing the embedding tangents.")


def graph_geometry(v, hessian, third):
    """Compute curvature from metric derivatives, without assuming Gauss."""
    s = np.sqrt(1-v @ v)
    q = np.eye(3)-np.outer(v, v)
    qi = la.inv(q)
    dq, ddq = np.zeros((3, 3, 3)), np.zeros((3, 3, 3, 3))
    for k, i, j in itertools.product(range(3), repeat=3):
        dq[k, i, j] = -hessian[i, k]*v[j]-v[i]*hessian[j, k]
        for l in range(3):
            ddq[l, k, i, j] = (-third[i, k, l]*v[j]-hessian[i, k]*hessian[j, l]
                               -hessian[i, l]*hessian[j, k]-v[i]*third[j, k, l])
    dqi = np.array([-qi @ derivative @ qi for derivative in dq])
    gamma, dgamma = np.zeros((3, 3, 3)), np.zeros((3, 3, 3, 3))
    for a, i, j in itertools.product(range(3), repeat=3):
        for b in range(3):
            coefficient = dq[i, b, j]+dq[j, b, i]-dq[b, i, j]
            gamma[a, i, j] += .5*qi[a, b]*coefficient
            for k in range(3):
                dgamma[k, a, i, j] += .5*(dqi[k, a, b]*coefficient+
                    qi[a, b]*(ddq[k, i, b, j]+ddq[k, j, b, i]-ddq[k, b, i, j]))
    riemann = np.zeros((3, 3, 3, 3))
    for a, b, c, d in itertools.product(range(3), repeat=4):
        riemann[a, b, c, d] = dgamma[c, a, d, b]-dgamma[d, a, c, b]
        for l in range(3):
            riemann[a, b, c, d] += gamma[a, c, l]*gamma[l, d, b]-gamma[a, d, l]*gamma[l, c, b]
    ricci = np.einsum('abad->bd', riemann)
    lower_riemann = np.einsum('ia,ajkl->ijkl', q, riemann)
    kform = hessian/s
    cov_k = np.zeros((3, 3, 3))
    for k, i, j in itertools.product(range(3), repeat=3):
        cov_k[k, i, j] = third[i, j, k]/s+hessian[i, j]*(v @ hessian[:, k])/s**3
        for l in range(3):
            cov_k[k, i, j] -= gamma[l, k, i]*kform[l, j]+gamma[l, k, j]*kform[i, l]
    tau = float(np.sum(qi*kform))
    electric = ricci+tau*kform-kform @ qi @ kform
    volume_epsilon = np.einsum('im,mkl->ikl', q, EPS)/np.sqrt(la.det(q))
    magnetic = np.einsum('ikl,klj->ij', volume_epsilon, cov_k)
    momentum = np.einsum('ki,kij->j', qi, cov_k)-np.einsum('ik,jik->j', qi, cov_k)
    scalar = float(np.sum(qi*ricci))
    hconstraint = scalar+tau*tau-float(np.trace(qi @ kform @ qi @ kform))
    gauss = -(np.einsum('ik,jl->ijkl', kform, kform)-np.einsum('il,jk->ijkl', kform, kform))
    result = dict(slope_norm=float(la.norm(v)), spatial_scalar_curvature=scalar,
                  gauss_error=norm(lower_riemann-gauss), electric_weyl_norm=norm(electric),
                  magnetic_weyl_norm=norm(magnetic), scalar_constraint_error=abs(hconstraint),
                  momentum_constraint_error=norm(momentum))
    assert max(result[key] for key in result if key.endswith('error') or 'weyl_norm' in key) < 2e-10
    return result


def graph_checks():
    rng, rows = np.random.default_rng(9112642), []
    for slope, case in itertools.product([0., .2, .5, .8], range(4)):
        v = rng.normal(size=3)
        v *= slope/la.norm(v)
        h = .3*rng.normal(size=(3, 3))
        h = (h+h.T)/2
        raw = .2*rng.normal(size=(3, 3, 3))
        third = sum(raw.transpose(perm) for perm in itertools.permutations(range(3)))/6
        rows.append(dict(case=case, **graph_geometry(v, h, third)))
    assert max(abs(row['spatial_scalar_curvature']) for row in rows) > .1
    return dict(cases=rows, scope="Curvature is constructed from first and second derivatives of q, including arbitrary symmetric third derivatives of the graph. Gauss, Codazzi, vacuum constraints and zero Weyl are independent comparisons.")


def gaussian_slices():
    rows = []
    for amplitude, point in itertools.product([.1, .4, .8],
                                              [[0., 0., 0.], [.3, -.4, .6], [1., 1., .5]]):
        x = np.array(point)
        value = amplitude*np.exp(-(x @ x)/2)
        v = -value*x
        h = value*(np.outer(x, x)-np.eye(3))
        third = np.empty((3, 3, 3))
        for i, j, k in itertools.product(range(3), repeat=3):
            third[i, j, k] = value*(-x[i]*x[j]*x[k]+
                (int(i == j)*x[k]+int(i == k)*x[j]+int(j == k)*x[i]))
        rows.append(dict(amplitude=amplitude, point=point,
                         global_maximum_slope=amplitude/np.sqrt(np.e),
                         **graph_geometry(v, h, third)))
    return dict(cases=rows, scope="Globally spacelike Gaussian graph examples. Zero ADM energy follows analytically from exponential metric falloff; a finite-radius flux is not called the ADM energy.")


def tt_project(matrix, momentum):
    transverse = np.eye(3)-np.outer(momentum, momentum)/(momentum @ momentum)
    return transverse @ matrix @ transverse-.5*transverse*np.trace(transverse @ matrix)


def tensor_quotient():
    rng, rows = np.random.default_rng(9112643), []
    for case in range(8):
        k = rng.normal(size=3)
        columns = []
        for axis in range(4):
            u = np.eye(3)[axis] if axis < 3 else np.zeros(3)
            metric = 1j*(np.outer(k, u)+np.outer(u, k))
            extrinsic = -np.outer(k, k) if axis == 3 else np.zeros((3, 3))
            canonical = extrinsic-np.eye(3)*np.trace(extrinsic)
            columns.append(np.r_[tt_project(metric, k).ravel(), tt_project(canonical, k).ravel()])
        mapping = np.column_stack(columns)
        error = norm(mapping)
        assert error < 2e-13
        rank = int(np.linalg.matrix_rank(mapping, tol=1e-12))
        assert rank == 0
        rows.append(dict(case=case, momentum=k.tolist(), tensor_phase_space_map_norm=error,
                         tensor_phase_space_map_rank=rank))
    return dict(cases=rows, scope="All four linear embedding perturbations are projected into both TT metric and TT canonical momentum. The map has rank zero around a flat slice.")


def nonflat_control():
    rows = []
    for amplitude, wave in itertools.product([.07, .2], [1, 2, 3]):
        z = .37
        c, s = np.cos(wave*z), np.sin(wave*z)
        sigma = amplitude*np.array([[c, s, 0.], [s, -c, 0.], [0., 0., 0.]])
        dsigma = amplitude*wave*np.array([[-s, c, 0.], [c, s, 0.], [0., 0., 0.]])
        tau = np.sqrt(3)*amplitude
        kform = sigma+tau*np.eye(3)/3
        derivatives = np.zeros((3, 3, 3))
        derivatives[2] = dsigma
        magnetic = np.einsum('ikl,klj->ij', EPS, derivatives)
        electric = tau*kform-kform @ kform
        hres = abs(np.trace(kform)**2-np.trace(kform @ kform))
        mres = norm(np.einsum('iij->j', derivatives)-np.einsum('jii->j', derivatives))
        assert hres+mres < 2e-13
        assert norm(magnetic+wave*sigma) < 2e-13
        assert abs(norm(magnetic)**2-2*amplitude**2*wave**2) < 2e-13
        assert norm(electric) > 0 and norm(magnetic) > 0
        rows.append(dict(amplitude=amplitude, wave_number=wave, scalar_constraint_error=hres,
                         momentum_constraint_error=mres, electric_weyl_norm=norm(electric),
                         magnetic_weyl_squared_norm=norm(magnetic)**2))
    return dict(cases=rows, scope="The existing periodic Einstein initial-data benchmark passes vacuum constraints but fails the flat-embedding zero-Weyl condition. Einstein dynamics remain supplied.")


def structure_function():
    rng, rows = np.random.default_rng(9112644), []
    for amplitude, case in itertools.product([.002, .01, .05, .2], range(2)):
        rotation, _ = la.qr(rng.normal(size=(3, 3)))
        h = rotation @ np.diag([amplitude, -amplitude, 0.]) @ rotation.T
        k = rotation[:, 2]
        w = rotation[:, 0]+.3*rotation[:, 1]
        assert norm(tt_project(h, k)-h) < 1e-13
        mismatch = (np.eye(3)-la.inv(np.eye(3)+h)) @ w
        remainder = norm(mismatch-h @ w)
        bound = amplitude**2*norm(w)/(1-amplitude)
        assert remainder <= bound+2e-13
        assert norm(mismatch) > .9*amplitude*norm(w)/(1+amplitude)
        rows.append(dict(amplitude=amplitude, case=case, structure_function_mismatch=norm(mismatch),
                         linear_prediction_norm=norm(h @ w), linear_remainder=remainder,
                         remainder_bound=bound))
    return dict(cases=rows, scope="An independent TT perturbation changes the required inverse metric in the off-constraint-surface bracket. Keeping the embedding metric misses a first-order term.")


def lattice_bracket():
    rows = []
    for length in [8, 16, 24, 32]:
        spacing = 2*np.pi/length
        x, y, z = np.meshgrid(*(np.arange(length)*spacing for _ in range(3)), indexing='ij')
        def derivative(f, axis):
            return (np.roll(f, -1, axis=axis)-np.roll(f, 1, axis=axis))/(2*spacing)
        clock = .15*np.sin(x)+.11*np.sin(y+.3)+.09*np.cos(z)
        v = np.stack([derivative(clock, i) for i in range(3)], axis=-1)
        exact_v = np.stack([.15*np.cos(x), .11*np.cos(y+.3), -.09*np.sin(z)], axis=-1)
        lapse_n = 1+.2*np.sin(x)+.15*np.cos(x+y)
        lapse_m = .8+.17*np.cos(x)+.12*np.sin(y+z)
        grad_n = np.stack([.2*np.cos(x)-.15*np.sin(x+y), -.15*np.sin(x+y), np.zeros_like(x)], axis=-1)
        grad_m = np.stack([-.17*np.sin(x), .12*np.cos(y+z), .12*np.cos(y+z)], axis=-1)
        p = np.stack([.4+.13*np.sin(x+y), .2*np.sin(x)+.3*np.cos(y),
                      .12*np.cos(x-y), .25*np.sin(z)], axis=-1)
        def frame(slopes):
            s2 = 1-np.sum(slopes**2, axis=-1)
            n = np.concatenate([np.ones(slopes.shape[:-1]+(1,)), slopes], axis=-1)/np.sqrt(s2)[..., None]
            qi = np.eye(3)+np.einsum('...i,...j->...ij', slopes, slopes)/s2[..., None, None]
            ep = slopes*p[..., :1]+p[..., 1:]
            return n, np.einsum('...ij,...j->...i', qi, ep)
        n, tangent_p = frame(v)
        n_cov = n*np.diag(ETA)
        def x_gradient(lapse):
            return sum(derivative(lapse[..., None]*tangent_p[..., i, None]*n_cov, i)
                       for i in range(3))
        # Independently check that x_gradient is the derivative of the actual
        # discrete Hamiltonian, including spatial embedding perturbations.
        perturbation = np.stack([np.sin(x+y), .13*np.cos(x), .19*np.sin(y+z),
                                 .11*np.cos(x+z)], axis=-1)
        de = np.stack([derivative(perturbation, i) for i in range(3)], axis=-2)
        e = np.zeros(v.shape[:-1]+(3, 4))
        e[..., 0], e[..., 1:] = v, np.eye(3)
        def hamiltonian(tangents):
            velocity = np.linalg.solve(tangents[..., :, 1:], tangents[..., :, 0])
            unit_normal = np.concatenate([np.ones(velocity.shape[:-1]+(1,)), velocity], axis=-1)
            unit_normal /= np.sqrt(1-np.sum(velocity**2, axis=-1))[..., None]
            return spacing**3*np.sum(lapse_n[..., None]*unit_normal*p)
        step = 1e-6
        variation = (hamiltonian(e+step*de)-hamiltonian(e-step*de))/(2*step)
        predicted_variation = spacing**3*np.sum(x_gradient(lapse_n)*perturbation)
        gradient_error = float(abs(variation-predicted_variation))
        assert gradient_error < 1e-7
        bracket = spacing**3*np.sum(x_gradient(lapse_n)*lapse_m[..., None]*n-
                                    x_gradient(lapse_m)*lapse_n[..., None]*n)
        _, exact_tangent_p = frame(exact_v)
        target = spacing**3*np.sum(exact_tangent_p*(lapse_n[..., None]*grad_m-lapse_m[..., None]*grad_n))
        error = float(abs(bracket-target))
        assert abs(target) > .1
        rows.append(dict(grid_per_axis=length, canonical_bracket=float(bracket),
                         continuum_target_quadrature=float(target), absolute_error=error,
                         relative_error=error/abs(float(target)),
                         hamiltonian_gradient_finite_difference_error=gradient_error))
    orders = [float(np.log(a['absolute_error']/b['absolute_error'])/
                    np.log(b['grid_per_axis']/a['grid_per_axis'])) for a, b in zip(rows, rows[1:])]
    assert all(order > 1.8 for order in orders)
    return dict(cases=rows, observed_convergence_orders=orders,
                scope="Canonical Poisson bracket of discrete embedding generators with centered differences on a periodic flat spatial quotient. The finite bracket is not exactly the continuum algebra; this is smooth-profile convergence evidence only.")


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_identities(), embedding_variations=embedding_variations(),
                  graph_geometry=graph_checks(), gaussian_slices=gaussian_slices(),
                  tensor_quotient=tensor_quotient(), nonflat_control=nonflat_control(),
                  physical_structure_function=structure_function(), lattice_bracket=lattice_bracket())
    sources = ['EMBEDDING_VERSUS_GRAVITY.md', 'scripts/embedding_gravity_audit.py',
               'QUANTUM_ENERGY_DRESSING.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'SPIN_CLOCK_BRACKET.md', 'NONLINEAR_TENSOR_BACKREACTION.md',
               'GRAVITATIONAL_BOUNDARY_DRESSING.md', 'PREPOTENTIAL_LATTICE_BRIDGE.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Classical fixed-flat-spacetime embeddings realize the metric-dependent deformation '
                       'algebra and vacuum initial-data constraints with no independent gravitational tensor '
                       'phase space and zero spacetime Weyl curvature. This rejects a specific pure-clock '
                       'metric identification. A physical TT perturbation must affect the same structure '
                       'function. No Einstein spin phase, quantum anomaly cancellation, Standard Model, or TOE is proved.')
    target = root/'data/embedding_gravity_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
