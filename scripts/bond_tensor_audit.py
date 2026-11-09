#!/usr/bin/env python3
"""Conditional bond-tensor construction; no microscopic gravity claim."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy


def bond_encoding():
    xx, yy, zz, xy, yz, zx = sy.symbols('xx yy zz xy yz zx', real=True)
    h = sy.Matrix([[xx, xy, zx], [xy, yy, yz], [zx, yz, zz]])
    axes = [sy.eye(3)[:, i] for i in range(3)]
    pairs = [(0, 1), (1, 2), (2, 0)]
    directions = axes+[axes[i]+axes[j] for i, j in pairs]
    coeff = [xx-xy-zx, yy-xy-yz, zz-yz-zx, xy, yz, zx]
    assert sy.simplify(sum((w*r*r.T for w, r in zip(coeff, directions)), sy.zeros(3))-h) == sy.zeros(3)
    flatten = lambda m: sy.Matrix([m[0, 0], m[1, 1], m[2, 2], m[0, 1], m[1, 2], m[2, 0]])
    encoding = sy.Matrix.hstack(*[flatten(r*r.T) for r in directions])
    assert encoding.det() != 0
    wa, wd = sy.symbols('wa wd', positive=True)
    reference = wa*sy.eye(3)
    delta = sy.diag(xx, yy, zz)
    for (i, j), shear in zip(pairs, [xy, yz, zx]):
        plus, minus = axes[i]+axes[j], axes[i]-axes[j]
        reference += wd*(plus*plus.T+minus*minus.T)
        delta += shear*(plus*plus.T-minus*minus.T)/2
    assert reference == (wa+4*wd)*sy.eye(3)
    assert sy.simplify(delta-h) == sy.zeros(3)
    return dict(axis_only_rank=3, six_direction_rank=int(encoding.rank()),
                six_direction_determinant=str(encoding.det()), isotropic_positive_direction_count=9,
                isotropic_stiffness='(w_axis + 4 w_diagonal) I',
                full_tensor_reconstruction=True, positive_reference_reconstruction=True)


def symbolic_constraints():
    k = sy.Matrix(sy.symbols('kx ky kz', real=True))
    names = sy.symbols('xx yy zz xy yz zx', real=True)
    x, y, z, xy, yz, zx = names
    h = sy.Matrix([[x, xy, zx], [xy, y, yz], [zx, yz, z]])
    q2 = (k.T*k)[0]
    tr = sy.trace(h)
    hk = h*k
    a, b, d = sy.symbols('a b d', real=True)
    v = q2*sy.trace(h*h)+a*q2*tr**2+b*(hk.T*hk)[0]+d*tr*(k.T*h*k)[0]
    xi = sy.Matrix(sy.symbols('xi0 xi1 xi2', real=True))
    gauge = k*xi.T+xi*k.T
    components = [gauge[0, 0], gauge[1, 1], gauge[2, 2], gauge[0, 1], gauge[1, 2], gauge[2, 0]]
    variation = sy.expand(sum(sy.diff(v, variable)*change for variable, change in zip(names, components)))
    equations = sy.Poly(variation, *list(k), *names, *list(xi)).coeffs()
    solution = sy.solve(equations, [a, b, d], dict=True)
    assert solution == [{a: -1, b: -2, d: 2}]
    assert sy.expand(variation.subs(solution[0])) == 0
    scalar = k*k.T-q2*sy.eye(3)
    assert sy.simplify(scalar*k) == sy.zeros(3, 1)
    alpha = sy.symbols('alpha', real=True)
    scalar_dot = sy.expand(sy.trace(scalar*(h+alpha*tr*sy.eye(3))))
    expected = (k.T*h*k)[0]-(1+2*alpha)*q2*tr
    assert sy.expand(scalar_dot-expected) == 0
    # Nonzero transverse trace is allowed before quotienting the scalar gauge.
    witness = scalar_dot.subs(dict(zip(list(k)+list(names), [0, 0, 1, 1, 1, 0, 0, 0, 0])))
    assert sy.solve(witness, alpha) == [-sy.Rational(1, 2)]
    return dict(spatial_gauge_solution={str(key): str(value) for key, value in solution[0].items()},
                momentum_trace_coefficient='-1/2', independent_polynomial_coefficients=len(equations),
                scalar_vector_constraint_brackets_zero=True,
                scope='Uniqueness within the explicitly supplied rotational quadratic ansatz and four constraints.')


def basis_matrices():
    out = [np.diag(np.eye(3)[i]) for i in range(3)]
    for i, j in [(0, 1), (1, 2), (2, 0)]:
        e = np.zeros((3, 3)); e[i, j] = e[j, i] = 1/np.sqrt(2)
        out.append(e)
    return np.array(out)


def matrix_blocks(k):
    basis = basis_matrices()
    q2 = np.dot(k, k)
    traces = np.trace(basis, axis1=1, axis2=2)
    div = np.column_stack([e@k for e in basis])
    second = np.array([k@e@k for e in basis])
    scalar = second-q2*traces
    kinetic = np.eye(6)-np.outer(traces, traces)/2
    potential = q2*np.eye(6)-q2*np.outer(traces, traces)-2*div.T@div+np.outer(traces, second)+np.outer(second, traces)
    constraint = np.zeros((4, 12)); constraint[:3, 6:] = div; constraint[3, :6] = scalar
    cross = np.array([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    curl_p = np.column_stack([(cross@(e-np.trace(e)*np.eye(3)/2)).ravel() for e in basis])
    curl_h = np.column_stack([(cross@e@cross.T).ravel() for e in basis])
    perp = np.eye(3)-np.outer(k, k)/q2
    tt = np.column_stack([[np.sum(f*(perp@e@perp-perp*np.trace(perp@e)/2)) for f in basis] for e in basis])
    return kinetic, potential, div, scalar, constraint, curl_p.T@curl_p, curl_h.T@curl_h, tt


def generic_momenta():
    random = np.random.default_rng(5291)
    directions = [np.array(x, dtype=float) for x in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 1), (1, 2, -3)]]
    directions += list(random.normal(size=(55, 3)))
    symplectic = np.block([[np.zeros((6, 6)), np.eye(6)], [-np.eye(6), np.zeros((6, 6))]])
    rows=[]
    J, g = .7, 1.3
    for k in directions:
        k = k/la.norm(k)*random.uniform(.1, 2)
        q2 = np.dot(k, k)
        kinetic, potential, div, scalar, a, kp, vp, tt = matrix_blocks(k)
        assert np.linalg.matrix_rank(a, tol=1e-10) == 4
        gauge = symplectic@a.T
        bracket = a@gauge
        assert la.norm(bracket) < 1e-11
        null = la.null_space(a)
        assert null.shape[1] == 8 and np.linalg.matrix_rank(gauge) == 4
        assert la.norm(a@gauge) < 1e-11
        assert la.norm(tt@tt-tt) < 1e-12
        assert abs(np.trace(tt)-2) < 1e-12
        vals, vecs = la.eigh(tt)
        physical = vecs[:, -2:]
        assert la.norm(physical.T@kinetic@physical-np.eye(2)) < 1e-12
        assert la.norm(physical.T@potential@physical-q2*np.eye(2)) < 1e-11
        assert la.norm(physical.T@kp@physical-q2*np.eye(2)) < 1e-11
        assert la.norm(physical.T@vp@physical-q2*q2*np.eye(2)) < 1e-10
        evolution = np.block([[np.zeros((6, 6)), J*kinetic], [-g*potential, np.zeros((6, 6))]])
        constraint_evolution = np.zeros((4, 4)); constraint_evolution[3, :3] = J*k
        residual = la.norm(a@evolution-constraint_evolution@a)
        assert residual < 1e-10
        assert la.norm(kp@scalar) < 1e-10 and la.norm(vp@div.T) < 1e-10
        reduced = np.block([[np.zeros((2, 2)), J*np.eye(2)], [-g*q2*np.eye(2), np.zeros((2, 2))]])
        frequencies = np.sort(abs(np.imag(la.eigvals(reduced))))
        assert np.max(abs(frequencies-np.sqrt(J*g*q2))) < 1e-12
        rows.append(dict(wavevector=k.tolist(), constraint_rank=4, constraint_surface_dimension=8,
                         gauge_dimension=4, physical_phase_dimension=4, physical_polarizations=2,
                         bracket_residual=float(la.norm(bracket)), evolution_residual=float(residual),
                         linear_frequency=float(np.sqrt(J*g*q2)),
                         curvature_square_frequency=float(np.sqrt(J*g)*q2**1.5)))
    return dict(momentum_rows=rows, independent_generic_directions=len(rows),
                scope='Finite Fourier blocks of the supplied canonical constrained continuum model, not a microscopic lattice-limit proof.')


def penalty_spectra():
    rows=[]
    c = np.sqrt(6)/4
    for U, W in [(1., 1.), (1e4, 1e4)]:
        for q in [1., .1, .01, .001, .0001]:
            kinetic, potential, div, scalar, a, kp, vp, tt = matrix_blocks(np.array([0., 0., q]))
            ksoft = np.eye(6)+U*div.T@div
            vsoft = c*c*q*q*np.eye(6)+W*np.outer(scalar, scalar)
            eig, vec = la.eigh(ksoft)
            root = (vec*np.sqrt(eig))@vec.T
            frequency_squared = la.eigvalsh(root@vsoft@root)
            expected = np.sort([c*c*q*q]*2+[c*c*q*q*(1+U*q*q/2)]*2+
                               [c*c*q*q*(1+U*q*q), c*c*q*q+2*W*q**4])
            assert np.max(abs(frequency_squared-expected))/(1+max(expected)) < 1e-11
            assert np.min(frequency_squared) > 0
            rows.append(dict(U=U, W=W, wave_number=q, frequencies_over_q=(np.sqrt(frequency_squared)/q).tolist(),
                             number_of_gapless_branches=6,
                             trace_momentum_energy_coefficient=float((-1.5+U*q*q)/2),
                             trace_coordinate_energy_coefficient=float(-q*q+2*W*q**4)))
        last = rows[-1]
        assert last['trace_momentum_energy_coefficient'] < 0
        assert last['trace_coordinate_energy_coefficient'] < 0
        assert max(abs(np.array(last['frequencies_over_q'])-c)) < .0003
    # Symbolic axis spectrum in the orthonormal xx,yy,zz,xy,yz,zx basis.
    q, U, W, c2, lam = sy.symbols('q U W c2 lam', positive=True)
    div = sy.Matrix([[0,0,0,0,0,q/sy.sqrt(2)], [0,0,0,0,q/sy.sqrt(2),0], [0,0,q,0,0,0]])
    scalar = sy.Matrix([-q*q,-q*q,0,0,0,0])
    k = sy.eye(6)+U*div.T*div
    v = c2*q*q*sy.eye(6)+W*scalar*scalar.T
    characteristic = sy.factor((lam*sy.eye(6)-k*v).det())
    expected = ((lam-c2*q*q)**2*(lam-c2*q*q*(1+U*q*q/2))**2*
                (lam-c2*q*q*(1+U*q*q))*(lam-c2*q*q-2*W*q**4))
    assert sy.factor(characteristic-expected) == 0
    return dict(axis_characteristic_polynomial=str(characteristic), rows=rows,
                scope='Noncompact quadratic tensor variables and fixed finite derivative penalties; compact spin models are not ruled out.')


def matter_ward():
    # Independent jet variables verify the divergence as a polynomial.
    phi1 = sy.Matrix(sy.symbols('f0:4', real=True))
    variables = sy.symbols('s0:10', real=True)
    second = sy.zeros(4); cursor=0
    for i in range(4):
        for j in range(i,4):
            second[i,j] = second[j,i] = variables[cursor]; cursor+=1
    eta = sy.diag(-1,1,1,1)
    upper = eta*phi1
    norm = (phi1.T*eta*phi1)[0]
    stress = upper*upper.T-eta*norm/2
    box = sy.trace(eta*second)
    divergence=[]
    for nu in range(4):
        value = sy.expand(sum(sy.diff(stress[mu,nu],phi1[r])*second[mu,r] for mu in range(4) for r in range(4)))
        assert sy.expand(value-box*upper[nu]) == 0
        divergence.append(str(sy.factor(value)))
    shear = sy.diag(0,1,-1); protected_gradient=sy.Matrix([0,1,0])
    vertex=(protected_gradient.T*shear*protected_gradient)[0]
    assert vertex == 1
    return dict(stress_divergence_components=divergence, free_stress_identity=True,
                old_switch_blind_gradient_new_shear_contraction=str(vertex),
                unequal_free_species_couplings_also_conserved=True,
                scope='First-order on-shell free-scalar Ward identity and a nonzero static/off-shell vertex. Universal coupling and interacting constraint closure are not proved.')


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(bond_encoding=bond_encoding(), symbolic_constraints=symbolic_constraints(),
                constrained_modes=generic_momenta(), soft_penalty_test=penalty_spectra(), scalar_coupling=matter_ward())
    sources=['BOND_TENSOR_CONSTRAINTS.md','scripts/bond_tensor_audit.py',
             'UnifiedTheory/Audit/KFCausalBondTensor.lean','ENTANGLED_ACOUSTIC_BOUNDS.md',
             'scripts/entangled_acoustic_audit.py','COLLECTIVE_GEOMETRY_STABILITY.md',
             'COLLECTIVE_WAVE_SPACETIME.md','PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256']={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in sources}
    report['scope']=('Conditional canonical spatial-tensor construction with imposed first-class constraints; '
                     'two linear TT modes and explicit failures of noncompact finite-penalty realizations. '
                     'No microscopic canonical tensor, emergent constraint phase, universal matter coupling, '
                     'nonlinear Einstein dynamics, or TOE is established.')
    (root/'data/bond_tensor_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
