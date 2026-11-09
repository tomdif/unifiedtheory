#!/usr/bin/env python3
"""Positive metric affine kinematics on finite symmetric spin blocks.

Quadrature results illustrate the separate analytical Galerkin estimates.
They are not certified integration errors or an Einstein constraint algebra.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.special import expit, roots_hermite
import sympy as sy

from microscopic_spin_two_audit import exact_cell


def opnorm(value):
    return float(la.norm(value, 2))


def occupations(modes, cutoff):
    def exact_total(total, count):
        if count == 1:
            yield (total,)
        else:
            for first in range(total+1):
                for rest in exact_total(total-first, count-1):
                    yield (first,)+rest
    return [state for total in range(cutoff+1)
            for state in exact_total(total, modes)]


def symmetric_basis(size):
    result = []
    for i in range(size):
        value = np.zeros((size, size))
        value[i, i] = 1
        result.append(value)
    for i in range(size):
        for j in range(i+1, size):
            value = np.zeros((size, size))
            value[i, j] = value[j, i] = 1/np.sqrt(2)
            result.append(value)
    return np.array(result)


def generators(size):
    return np.eye(size*size).reshape(size*size, size, size)


def rotation_matrices():
    return [np.column_stack([np.cross(np.eye(3)[axis], np.eye(3)[j])
                             for j in range(3)]) for axis in range(3)]


def exact_algebra():
    # Noncommuting GL(2) action checked as polynomial vector fields on SPD(2).
    x, y, z = sy.symbols('x y z', real=True)
    q = sy.Matrix([[x, z], [z, y]])
    variables = sy.Matrix([x, y, z])
    units = [sy.Matrix(2, 2, lambda i, j: int(2*i+j == a)) for a in range(4)]
    vector = lambda matrix: sy.Matrix([matrix[0, 0], matrix[1, 1], matrix[0, 1]])
    actions, bounded_actions = [], []
    for a in units:
        actions.append(vector(a*q+q*a.T))
        bounded_actions.append(vector((sy.eye(2)-q)*a*q+q*a.T*(sy.eye(2)-q)))
    for family in [actions, bounded_actions]:
        for i, j in itertools.product(range(4), repeat=2):
            bracket = family[j].jacobian(variables)*family[i]-family[i].jacobian(variables)*family[j]
            commutator = units[i]*units[j]-units[j]*units[i]
            expected = sum((commutator[k, l]*family[2*k+l] for k, l in itertools.product(range(2), repeat=2)), sy.zeros(3, 1))
            assert (bracket+expected).applyfunc(sy.expand) == sy.zeros(3, 1)
    # Differential of B=q(I+q)^(-1), without assuming A commutes with q.
    inverse = (sy.eye(2)+q).inv()
    b = sy.eye(2)-inverse
    for a in units:
        derivative = inverse*(a*q+q*a.T)*inverse
        target = (sy.eye(2)-b)*a*b+b*a.T*(sy.eye(2)-b)
        assert (derivative-target).applyfunc(sy.cancel) == sy.zeros(2)
    return dict(affine_vector_field_sign_pairs=16,
                bounded_metric_vector_field_sign_pairs=16,
                bounded_transform_derivative=True,
                scope="Exact polynomial identities in dimension two; the note proves the matrix identities in arbitrary finite dimension.")


def spin_encoding():
    cell, _ = exact_cell()
    singlet = np.array([0., 1., -1., 0.])/np.sqrt(2)
    eta = np.kron(singlet, singlet)
    active = np.column_stack([cell['omega'], eta, cell['states']])
    gram_error = opnorm(active.conj().T@active-np.eye(7))
    assert gram_error < 2e-14
    excitation_basis = np.array([np.eye(3)/np.sqrt(3)]+[e.real for e in cell['basis']])
    pauli = [np.array([[0, 1], [1, 0]])/2,
             np.array([[0, -1j], [1j, 0]])/2, np.diag([1, -1])/2]
    rotation_errors = []
    for spin, omega in zip(pauli, rotation_matrices()):
        total = np.zeros((16, 16), complex)
        for site in range(4):
            factors = [spin if j == site else np.eye(2) for j in range(4)]
            operator = factors[0]
            for factor in factors[1:]:
                operator = np.kron(operator, factor)
            total += operator
        tangent = np.einsum('aij,bij->ab', excitation_basis, omega@excitation_basis-excitation_basis@omega)
        target = np.zeros((7, 7), complex)
        target[1:, 1:] = 1j*tangent
        # Full sixteen-row comparison also detects leakage out of the active cell.
        rotation_errors.append(opnorm(total@active-active@target))
    assert max(rotation_errors) < 2e-14
    rows = []
    for cutoff in [1, 2, 4, 8]:
        states = occupations(6, cutoff)
        lookup = {state: i for i, state in enumerate(states)}
        assert len(states) == math.comb(cutoff+6, 6)
        # Check every collective transition coefficient, including its top face.
        error = 0.
        for state in states:
            total = sum(state)
            for axis in range(6):
                next_state = list(state)
                next_state[axis] += 1
                next_state = tuple(next_state)
                raw = math.sqrt((state[axis]+1)*(1-total/cutoff))
                dressed = raw/math.sqrt(1-total/cutoff) if total < cutoff else 0.
                expected = math.sqrt(state[axis]+1) if next_state in lookup else 0.
                error = max(error, abs(dressed-expected))
        assert error < 2e-14
        rows.append(dict(cells=cutoff, microscopic_qubits=4*cutoff,
                         symmetric_dimension=len(states), dressed_transition_error=error))
    return dict(active_cell_gram_error=gram_error, microscopic_rotation_errors=rotation_errors, cases=rows,
                scope="Exact occupation-space isometry into a selected symmetric block of seven active states per four-spin cell. No local parent, phase selection, or bounded body order is supplied.")


class Galerkin:
    def __init__(self, size, cutoff, order, scale=.3):
        self.size, self.cutoff, self.order, self.scale = size, cutoff, order, scale
        self.basis = symmetric_basis(size)
        self.modes = len(self.basis)
        self.states = occupations(self.modes, cutoff)
        self.dim = len(self.states)
        self.units = generators(size)
        lookup = {state: i for i, state in enumerate(self.states)}
        lower = []
        for axis in range(self.modes):
            columns = [j for j, state in enumerate(self.states) if state[axis]]
            parents, coefficients = [], []
            for column in columns:
                state = list(self.states[column])
                coefficients.append(math.sqrt(2*state[axis]))
                state[axis] -= 1
                parents.append(lookup[tuple(state)])
            lower.append((np.array(columns, int), np.array(parents, int), np.array(coefficients)))
        nodes, weights = roots_hermite(order)
        weights /= np.sqrt(np.pi)
        polynomials = [np.ones(order), np.sqrt(2)*nodes]
        for n in range(1, cutoff):
            polynomials.append(np.sqrt(2/(n+1))*nodes*polynomials[n]-np.sqrt(n/(n+1))*polynomials[n-1])
        polynomials = np.array(polynomials[:cutoff+1])
        self.gram = np.zeros((self.dim, self.dim))
        self.metric = np.zeros((size, size, self.dim, self.dim))
        weak = np.zeros((size*size, self.dim, self.dim))
        # Batching bounds memory independently of the tensor quadrature node count.
        count = order**self.modes
        for start in range(0, count, 8192):
            indices = np.array(np.unravel_index(np.arange(start, min(start+8192, count)), (order,)*self.modes)).T
            x = nodes[indices]
            weight = np.prod(weights[indices], axis=1)
            u = np.ones((len(indices), self.dim))
            for axis in range(self.modes):
                degrees = np.array([state[axis] for state in self.states])
                u *= polynomials[degrees[None, :], indices[:, axis, None]]
            weighted_u = (weight[:, None]*u).T
            self.gram += weighted_u@u
            h = scale*np.einsum('pa,aij->pij', x, self.basis)
            values, vectors = np.linalg.eigh(h)
            transpose = vectors.swapaxes(-1, -2)
            metric = (vectors*expit(values)[:, None, :])@transpose
            q = (vectors*np.exp(values)[:, None, :])@transpose
            midpoint = (values[:, :, None]+values[:, None, :])/2
            difference = (values[:, :, None]-values[:, None, :])/2
            ratio = np.ones_like(difference)
            np.divide(np.sinh(difference), difference, out=ratio, where=abs(difference) > 1e-12)
            frechet_factors = np.exp(midpoint)*ratio
            for i in range(size):
                for j in range(i, size):
                    self.metric[i, j] += weighted_u@(metric[:, i, j, None]*u)
            for index, a in enumerate(self.units):
                tangent = a@q+q@a.T
                flow = vectors@((transpose@tangent@vectors)/frechet_factors)@transpose
                coordinates = np.einsum('pij,aij->pa', flow, self.basis)
                derivative = np.zeros_like(u)
                for axis, (columns, parents, coefficients) in enumerate(lower):
                    derivative[:, columns] += coordinates[:, axis, None]*u[:, parents]*coefficients
                weak[index] += weighted_u@derivative
        for i in range(size):
            for j in range(i, size):
                self.metric[i, j] = (self.metric[i, j]+self.metric[i, j].T)/2
                self.metric[j, i] = self.metric[i, j]
        self.d = -1j*(weak-weak.swapaxes(-1, -2))/(2*scale)
        self.big_b = np.block([[self.metric[i, j] for j in range(size)] for i in range(size)])
        assert opnorm(self.gram-np.eye(self.dim)) < 3e-13

    def measure(self, input_cutoff=1):
        inputs = np.array([i for i, state in enumerate(self.states) if sum(state) <= input_cutoff])
        auxiliary_inputs = np.concatenate([inputs+i*self.dim for i in range(self.size)])
        lie_error, component_error, covariance_error = 0., 0., 0.
        worst_pair = None
        for i, j in itertools.combinations(range(self.size**2), 2):
            a, c = self.units[i], self.units[j]
            comm = a@c-c@a
            target = np.einsum('a,aij->ij', comm.ravel(), self.d)
            defect = self.d[i]@self.d[j][:, inputs]-self.d[j]@self.d[i][:, inputs]-1j*target[:, inputs]
            error = opnorm(defect)
            if error > lie_error:
                lie_error, worst_pair = error, [i, j]
        unique = [self.metric[i, j] for i in range(self.size) for j in range(i, self.size)]
        for b, c in itertools.combinations(unique, 2):
            component_error = max(component_error, opnorm(b@c[:, inputs]-c@b[:, inputs]))
        identity = np.eye(self.size*self.dim)
        for a, d in zip(self.units, self.d):
            dext = np.kron(np.eye(self.size), d)
            aext = np.kron(a, np.eye(self.dim))
            action = ((identity-self.big_b)@aext@self.big_b[:, auxiliary_inputs]
                      +self.big_b@aext.T@(identity-self.big_b)[:, auxiliary_inputs])
            defect = 1j*(dext@self.big_b[:, auxiliary_inputs]-self.big_b@dext[:, auxiliary_inputs])-action
            covariance_error = max(covariance_error, opnorm(defect))
        eigenvalues = la.eigvalsh(self.big_b)
        assert 0 < eigenvalues[0] < eigenvalues[-1] < 1
        rotation_error = None
        if self.size == 3:
            lookup = {state: i for i, state in enumerate(self.states)}
            rotation_error = 0.
            for omega in rotation_matrices():
                tangent = np.einsum('aij,bij->ab', self.basis, omega@self.basis-self.basis@omega)
                expected = np.zeros((self.dim, self.dim), complex)
                for col, state in enumerate(self.states):
                    for a, b in itertools.product(range(self.modes), repeat=2):
                        if not state[b] or tangent[a, b] == 0:
                            continue
                        target = list(state)
                        factor = math.sqrt(target[b])
                        target[b] -= 1
                        factor *= math.sqrt(target[a]+1)
                        target[a] += 1
                        expected[lookup[tuple(target)], col] += 1j*tangent[a, b]*factor
                actual = np.einsum('a,aij->ij', omega.ravel(), self.d)
                rotation_error = max(rotation_error, opnorm(actual-expected))
            assert rotation_error < 3e-12
        return dict(spatial_dimension=self.size, log_coordinates=self.modes,
                    generators=self.size**2, cutoff=self.cutoff, quadrature_order=self.order,
                    quadrature_nodes=self.order**self.modes, oscillator_scale=self.scale,
                    block_dimension=self.dim, input_cutoff=input_cutoff,
                    input_dimension=len(inputs), full_output_dimension=self.dim,
                    gram_error=opnorm(self.gram-np.eye(self.dim)),
                    minimum_b_eigenvalue=float(eigenvalues[0]),
                    maximum_b_eigenvalue=float(eigenvalues[-1]),
                    maximum_lie_algebra_defect=lie_error, worst_generator_pair=worst_pair,
                    full_block_collective_rotation_error=rotation_error,
                    maximum_b_component_commutator=component_error,
                    maximum_b_covariance_defect=covariance_error)

    def transported_vacuum(self, a, time, order):
        """Independent exact congruence flow, including its half-density Jacobian."""
        nodes, weights = roots_hermite(order)
        weights /= np.sqrt(np.pi)
        indices = np.array(list(itertools.product(range(order), repeat=self.modes)))
        x = nodes[indices]
        weight = np.prod(weights[indices], axis=1)
        polynomials = [np.ones(order), np.sqrt(2)*nodes]
        for n in range(1, self.cutoff):
            polynomials.append(np.sqrt(2/(n+1))*nodes*polynomials[n]-np.sqrt(n/(n+1))*polynomials[n-1])
        polynomials = np.array(polynomials[:self.cutoff+1])
        u = np.ones((len(x), self.dim))
        for axis in range(self.modes):
            degrees = np.array([state[axis] for state in self.states])
            u *= polynomials[degrees[None, :], indices[:, axis, None]]
        h = self.scale*np.einsum('pa,aij->pij', x, self.basis)
        values, vectors = np.linalg.eigh(h)
        q = (vectors*np.exp(values)[:, None, :])@vectors.swapaxes(-1, -2)
        inverse_frame = la.expm(-time*a)
        prior_q = inverse_frame@q@inverse_frame.T
        prior_values, prior_vectors = np.linalg.eigh(prior_q)
        assert np.min(prior_values) > 0
        prior_logs = np.log(prior_values)
        prior_h = (prior_vectors*prior_logs[:, None, :])@prior_vectors.swapaxes(-1, -2)
        prior_x = np.einsum('pij,aij->pa', prior_h, self.basis)/self.scale
        def log_exp_jacobian(eigenvalues):
            result = np.sum(eigenvalues, axis=1)
            for i in range(self.size):
                for j in range(i+1, self.size):
                    midpoint = (eigenvalues[:, i]+eigenvalues[:, j])/2
                    difference = (eigenvalues[:, i]-eigenvalues[:, j])/2
                    ratio = np.ones_like(difference)
                    np.divide(np.sinh(difference), difference, out=ratio, where=abs(difference) > 1e-12)
                    result += midpoint+np.log(ratio)
            return result
        log_jacobian = (-(self.size+1)*time*np.trace(a)+log_exp_jacobian(values)
                        -log_exp_jacobian(prior_logs))
        ratio = np.exp((log_jacobian+np.sum(x*x-prior_x*prior_x, axis=1))/2)
        coefficients = u.T@(weight*ratio)
        quadrature_norm = float(np.sum(weight*ratio**2))
        assert abs(quadrature_norm-1) < 3e-11
        return coefficients, quadrature_norm


def finite_block_checks():
    rows, refinement, shear_rows = [], [], []
    for size, cutoffs in [(3, [1, 2, 3, 4]), (2, [2, 4, 6, 8])]:
        for cutoff in cutoffs:
            orders = [8, 9] if size == 3 and cutoff == 4 else [7, 8] if size == 3 else [12, 16]
            low = Galerkin(size, cutoff, orders[0])
            high = Galerkin(size, cutoff, orders[1])
            row = high.measure()
            rows.append(row)
            d_error = max(opnorm(a-b) for a, b in zip(low.d, high.d))
            b_error = opnorm(low.big_b-high.big_b)
            assert d_error < 5e-6 and b_error < 5e-7
            refinement.append(dict(spatial_dimension=size, cutoff=cutoff,
                                   lower_quadrature_order=orders[0], higher_quadrature_order=orders[1],
                                   full_generator_matrix_change=d_error,
                                   full_b_matrix_change=b_error))
            print(json.dumps(row), flush=True)
            if size == 2:
                a = np.array([[0., .2], [0., 0.]])
                time = .8
                generator = np.einsum('a,aij->ij', a.ravel(), high.d)
                finite = la.expm(-1j*time*generator)@np.eye(high.dim)[:, 0]
                low_generator = np.einsum('a,aij->ij', a.ravel(), low.d)
                low_finite = la.expm(-1j*time*low_generator)@np.eye(low.dim)[:, 0]
                coarse, _ = high.transported_vacuum(a, time, 20)
                fine, norm = high.transported_vacuum(a, time, 24)
                overlap = float(np.vdot(finite, fine).real)
                error_squared = 2-2*overlap
                assert error_squared > 0
                coefficient_change = float(la.norm(fine-coarse))
                assert coefficient_change < 2e-12
                shear_rows.append(dict(spatial_dimension=size, cutoff=cutoff,
                                       shear_coefficient=.2, time=time,
                                       full_hilbert_space_error=math.sqrt(error_squared),
                                       finite_state_generator_quadrature_change=float(la.norm(finite-low_finite)),
                                       exact_flow_quadrature_norm=norm,
                                       exact_flow_coefficient_refinement=coefficient_change,
                                       norm_error_squared_quadrature_change=2*abs(float(np.vdot(finite, coarse-fine).real))))
    for size in [2, 3]:
        selected = [r for r in rows if r['spatial_dimension'] == size]
        for key in ['maximum_lie_algebra_defect', 'maximum_b_component_commutator', 'maximum_b_covariance_defect']:
            assert selected[-1][key] < selected[0][key]/5
    assert shear_rows[-1]['full_hilbert_space_error'] < shear_rows[0]['full_hilbert_space_error']/100
    return dict(cases=rows, quadrature_refinement=refinement,
                nonlinear_shear_evolution=shear_rows,
                scope="All GL(3) generators and all six metric components at cutoffs 1,2,3,4; GL(2) illustration and independent finite-shear transport to cutoff 8. Norms retain every output row. Quadrature refinement is measured separately and is not a rigorous integration certificate.")


def dilation_evolution():
    # A scalar GL(3) generator translates the trace log-coordinate by v*t.
    # Its exact evolved oscillator vacuum is a coherent displacement.
    rows = []
    speed, time = .8, .9
    displacement = speed*time/np.sqrt(2)
    for cutoff in [2, 4, 8, 16]:
        creation = np.diag(np.sqrt(np.arange(1, cutoff+1)), -1)
        momentum = (creation.T-creation)/(1j*np.sqrt(2))
        vacuum = np.eye(cutoff+1)[:, 0]
        finite = la.expm(-1j*time*speed*momentum)@vacuum
        exact = np.array([np.exp(-displacement**2/2)*displacement**n/math.sqrt(math.factorial(n))
                          for n in range(cutoff+1)])
        # Positive tail sum avoids cancellation against one at high cutoff.
        tail = sum(np.exp(-displacement**2)*displacement**(2*n)/math.factorial(n)
                   for n in range(cutoff+1, cutoff+100))
        error = float(np.sqrt(la.norm(finite-exact)**2+tail))
        assert abs(la.norm(finite)-1) < 2e-14
        rows.append(dict(cutoff=cutoff, speed=speed, time=time,
                         full_hilbert_space_error=error, continuum_tail_norm=math.sqrt(tail)))
    assert rows[-1]['full_hilbert_space_error'] < 1e-9
    return dict(cases=rows, scope="Finite-time numerical control for the central dilation subgroup only. The general affine finite-time result is the analytical Schwartz-domain estimate in the note.")


def main():
    root = Path(__file__).resolve().parents[1]
    exact, encoding = exact_algebra(), spin_encoding()
    finite = finite_block_checks()
    shear = dict(cases=finite.pop('nonlinear_shear_evolution'),
                 scope="GL(2) finite-shear evolution compared with independent exact nonlinear log-congruence transport and its half-density Jacobian; full continuum-state error inferred using exact unit normalization and numerical overlap quadrature.")
    report = dict(exact_algebra=exact, microscopic_encoding=encoding,
                  finite_metric_algebra=finite, shear_time_evolution=shear,
                  dilation_time_evolution=dilation_evolution())
    sources = ['AFFINE_SPIN_METRIC.md', 'scripts/affine_spin_metric_audit.py',
               'SPIN_CLOCK_BRACKET.md', 'scripts/spin_clock_bracket_audit.py',
               'MICROSCOPIC_SPIN_TWO_SEED.md', 'scripts/microscopic_spin_two_audit.py',
               'CANONICAL_METRIC_RECONSTRUCTION.md', 'EMBEDDING_VERSUS_GRAVITY.md',
               'COMPACT_CONSTRAINT_NORMALIZER.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Full onsite positive-metric affine kinematics can be represented on growing '
                       'finite symmetric spin blocks with fixed-input Galerkin convergence. '
                       'The analytical theorem controls bounded metric functions, Lie brackets and '
                       'finite affine transformations, not unbounded inverse-metric moments, spatial '
                       'constraints, a uniformly local parent or an Einstein phase. Affine '
                       'quantization is established prior work; no physical TOE is proved.')
    target = root/'data/affine_spin_metric_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), cases=counts, total_cases=sum(counts.values()),
                         quadrature_refinements=len(report['finite_metric_algebra']['quadrature_refinement']),
                         source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
