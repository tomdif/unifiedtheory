#!/usr/bin/env python3
"""Nonlinear cotangent metric reconstruction and its scoped continuum tests."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from tensor_packet_self_gravity_audit import Packet


def norm(a):
    return float(la.norm(np.asarray(a).ravel()))


def traceless(a):
    return (a+a.T)/2-np.eye(3)*np.trace(a)/3


def shape_basis():
    result = [np.diag([1., -1., 0.])/np.sqrt(2),
              np.diag([1., 1., -2.])/np.sqrt(6)]
    for i, j in [(0, 1), (1, 2), (2, 0)]:
        value = np.zeros((3, 3))
        value[i, j] = value[j, i] = 1/np.sqrt(2)
        result.append(value)
    return np.array(result)


class ExpGeometry:
    def __init__(self, h):
        values, self.vectors = np.linalg.eigh(h)
        midpoint = (values[..., :, None]+values[..., None, :])/2
        difference = (values[..., :, None]-values[..., None, :])/2
        ratio = np.ones_like(difference)
        np.divide(np.sinh(difference), difference, out=ratio, where=abs(difference) > 1e-12)
        self.factors = np.exp(midpoint)*ratio
        self.transpose = np.swapaxes(self.vectors, -1, -2)
        self.metric = (self.vectors*np.exp(values)[..., None, :]) @ self.transpose

    def apply(self, value, inverse=False):
        transformed = self.transpose @ value @ self.vectors
        transformed = transformed/self.factors if inverse else transformed*self.factors
        return self.vectors @ transformed @ self.transpose


def exact_algebra():
    psi, dpsi = sy.symbols('psi dpsi', positive=True)
    trace, pairing = sy.symbols('trace pairing')
    expression = psi**-4*(4*psi**3*dpsi*trace+psi**4*pairing)
    assert sy.simplify(expression.subs(trace, 0)-pairing) == 0
    h = sy.Matrix(3, 3, lambda i, j: sy.Symbol('h'+str(min(i, j))+str(max(i, j))))
    p = sy.Matrix(3, 3, lambda i, j: sy.Symbol('p'+str(min(i, j))+str(max(i, j))))
    parameter = sy.Symbol('epsilon')
    linear_t = p-parameter*(h*p+p*h)/2
    tg = (linear_t*(sy.eye(3)+parameter*h)).applyfunc(
        lambda x: sy.series(x, parameter, 0, 2).removeO().expand())
    assert (tg-p-parameter*(p*h-h*p)/2).applyfunc(sy.expand) == sy.zeros(3)
    radius, potential = sy.Rational(1, 4), sy.Rational(1, 256)
    invariant_bound = potential*(1-radius)**-7+potential*(1+radius)
    contraction_bound = 7*potential*(1-radius)**-8+potential
    assert invariant_bound < radius and contraction_bound < 1
    return dict(conformal_factor_cancels_canonical_one_form=True,
                momentum_only_family_one_form_zero=True,
                first_nonlinear_momentum_density_commutator=True,
                scalar_example_invariant_bound=str(invariant_bound),
                scalar_example_contraction_bound=str(contraction_bound),
                scope="Exact algebra. Existence of the full reconstruction uses the separate small-field and scalar Green bounds in the note.")


def pointwise_cotangent():
    basis, rng, rows = shape_basis(), np.random.default_rng(9112651), []
    step = 1e-5
    for size, case in itertools.product([0., .1, .4], range(4)):
        coordinates = np.r_[size*rng.normal(size=5), .3*rng.normal(size=5)]
        def evaluate(z):
            h = np.einsum('i,ijk->jk', z[:5], basis)
            p = np.einsum('i,ijk->jk', z[5:], basis)
            geometry = ExpGeometry(h)
            psi = 1+.04*(z[:5] @ z[:5])+.03*(z[5:] @ z[5:])+.01*np.sin(z[:5] @ z[5:])
            return psi**4*geometry.metric, psi**-4*geometry.apply(p, inverse=True), geometry, psi, p
        q, pi, geometry, psi, p = evaluate(coordinates)
        dh = traceless(rng.normal(size=(3, 3)))
        dpsi = float(rng.normal())
        dq = psi**4*geometry.apply(dh)+4*psi**3*dpsi*geometry.metric
        one_form = abs(float(np.sum(pi*dq)-np.sum(p*dh)))
        assert one_form < 2e-12
        assert abs(np.trace(pi @ q)) < 2e-12
        q_derivatives, pi_derivatives = [], []
        for axis in range(10):
            displacement = step*np.eye(10)[axis]
            qp, pp, *_ = evaluate(coordinates+displacement)
            qm, pm, *_ = evaluate(coordinates-displacement)
            q_derivatives.append(((qp-qm)/(2*step)).ravel())
            pi_derivatives.append(((pp-pm)/(2*step)).ravel())
        dq_matrix, dp_matrix = np.array(q_derivatives).T, np.array(pi_derivatives).T
        pulled = dp_matrix.T @ dq_matrix-dq_matrix.T @ dp_matrix
        expected = np.block([[np.zeros((5, 5)), -np.eye(5)], [np.eye(5), np.zeros((5, 5))]])
        symplectic_error = norm(pulled-expected)
        assert symplectic_error < 3e-8
        # At fixed h=0, only the momentum coordinates remain: the two-form vanishes.
        if size == 0:
            assert norm(pulled[5:, 5:]) < 2e-10
        frechet_error = norm(geometry.apply(dh)-la.expm_frechet(
            np.einsum('i,ijk->jk', coordinates[:5], basis), dh, compute_expm=False))
        assert frechet_error < 3e-12
        rows.append(dict(log_metric_size=size, case=case, one_form_error=one_form,
                         symplectic_finite_difference_error=symplectic_error,
                         independent_frechet_error=frechet_error,
                         minimum_metric_eigenvalue=float(min(la.eigvalsh(q)))))
    return dict(cases=rows, scope="Five pointwise shape pairs before spatial reduction. Full canonical two-form is checked while the conformal factor depends on both coordinates and momenta. This alone is not the two-polarization gravitational field.")


def polarization(momentum, cross=False):
    n = np.array(momentum, float)
    n /= la.norm(n)
    axis = np.eye(3)[int(np.argmin(abs(n)))]
    a = np.cross(n, axis)
    a /= la.norm(a)
    b = np.cross(n, a)
    return (np.outer(a, b)+np.outer(b, a) if cross else np.outer(a, a)-np.outer(b, b))/np.sqrt(2)


class SpectralMomentum:
    def __init__(self, length, amplitude):
        self.length, self.amplitude = length, amplitude
        x = np.meshgrid(*(2*np.pi*np.arange(length)/length for _ in range(3)), indexing='ij')
        frequencies = np.fft.fftfreq(length)*length
        self.k = np.stack(np.meshgrid(*(frequencies for _ in range(3)), indexing='ij'), axis=-1)
        self.k2 = np.sum(self.k**2, axis=-1)
        self.h = np.zeros((length, length, length, 3, 3))
        self.s = np.zeros_like(self.h)
        modes, coefficients = [(0, 0, 1), (1, 0, 0), (1, 1, 0)], [1., .6, .4]
        for momentum, coefficient, pcoefficient in zip(modes, coefficients, [.7, .9, .4]):
            phase = sum(k*coordinate for k, coordinate in zip(momentum, x))
            self.h += amplitude*coefficient*np.cos(phase)[..., None, None]*polarization(momentum)
            self.s += .2*pcoefficient*np.cos(phase)[..., None, None]*polarization(momentum, cross=True)
        self.geometry = ExpGeometry(self.h)
        self.dh = [self.derivative(self.h, i) for i in range(3)]
        h_bound = amplitude*sum(coefficients)/np.sqrt(2)
        grad_bound = amplitude*sum(c*la.norm(k) for c, k in zip(coefficients, modes))
        # Mean-zero periodic vectors have ||v||_2 <= ||grad v||_2 here.
        self.coercivity_error_bound = (2*np.expm1(2*h_bound)+grad_bound)/np.sqrt(2)
        assert self.coercivity_error_bound < 1
        assert norm(self.divergence(self.s)) < 1e-12
        assert norm(self.divergence(self.h)) < 1e-12

    def derivative(self, value, axis):
        shape = self.k.shape[:-1]+(1,)*(value.ndim-3)
        multiplier = self.k[..., axis].reshape(shape)
        return np.fft.ifftn(1j*multiplier*np.fft.fftn(value, axes=(0, 1, 2)),
                           axes=(0, 1, 2)).real

    def divergence(self, matrix):
        return sum(self.derivative(matrix[..., i, :], i) for i in range(3))

    def longitudinal(self, vector):
        gradient = np.stack([self.derivative(vector, i) for i in range(3)], axis=-2)
        return gradient+gradient.swapaxes(-1, -2)-(2/3)*np.trace(
            gradient, axis1=-2, axis2=-1)[..., None, None]*np.eye(3)

    def constraint(self, p):
        t = self.geometry.apply(p, inverse=True)
        transport = np.stack([np.sum(p*derivative, axis=(-2, -1)) for derivative in self.dh], axis=-1)
        return transport-2*self.divergence(t @ self.geometry.metric)

    def gauge_action(self, vector):
        gradient = np.stack([self.derivative(vector, i) for i in range(3)], axis=-2)
        transport = sum(vector[..., i, None, None]*self.dh[i] for i in range(3))
        matrix_change = gradient @ self.geometry.metric+self.geometry.metric @ gradient.swapaxes(-1, -2)
        return (transport+self.geometry.apply(matrix_change, inverse=True)-
                (2/3)*np.trace(gradient, axis1=-2, axis2=-1)[..., None, None]*np.eye(3))

    def inverse_flat(self, vector):
        transformed = np.fft.fftn(vector, axes=(0, 1, 2))
        k2 = self.k2.copy()
        k2[0, 0, 0] = 1
        projected = transformed-.25*self.k*np.sum(self.k*transformed, axis=-1)[..., None]/k2[..., None]
        projected /= 2*k2[..., None]
        projected[0, 0, 0] = 0
        return np.fft.ifftn(projected, axes=(0, 1, 2)).real

    def solve(self):
        w = np.zeros(self.h.shape[:-1])
        initial = self.constraint(self.s)
        # Reflection-even tensor seeds make the translation source vanish.
        assert norm(np.mean(initial, axis=(0, 1, 2))) < 2e-13
        for iteration in range(150):
            p = self.s+self.longitudinal(w)
            residual = self.constraint(p)
            if norm(residual)/self.length**1.5 < 2e-13:
                break
            w -= self.inverse_flat(residual)
        else:
            raise AssertionError("Nonlinear momentum correction did not converge")
        correction = p-self.s
        bound = self.coercivity_error_bound/(1-self.coercivity_error_bound)*norm(self.s)
        assert norm(correction) <= bound+2e-12
        rng = np.random.default_rng(9112652+self.length)
        vector = rng.normal(size=w.shape)
        vector -= np.mean(vector, axis=(0, 1, 2))
        gauge, flat = self.gauge_action(vector), self.longitudinal(vector)
        adjoint_error = abs(float(np.sum(p*gauge)-np.sum(self.constraint(p)*vector)))/self.length**3
        assert adjoint_error < 3e-12
        relative_gauge_error = norm(gauge-flat)/norm(flat)
        assert relative_gauge_error <= self.coercivity_error_bound+2e-13
        coercivity_ratio = float(np.sum(gauge*flat)/np.sum(flat*flat))
        assert coercivity_ratio >= 1-self.coercivity_error_bound-2e-13
        dh = self.s/.2
        one_form_error = abs(float(np.sum(correction*dh)))/self.length**3
        assert one_form_error < 3e-13
        commutator = self.s @ self.h-self.h @ self.s
        first_source = np.stack([np.sum(self.s*derivative, axis=(-2, -1))
                                 for derivative in self.dh], axis=-1)-self.divergence(commutator)
        first_w = -self.inverse_flat(first_source)
        first_correction_error = norm(correction-self.longitudinal(first_w))/self.length**1.5
        source_error = norm(initial-first_source)/self.length**1.5
        assert source_error < 2*self.amplitude**2
        assert first_correction_error < 2*self.amplitude**2
        # The full pointwise metric pullback agrees with the reduced TT pairing.
        psi = 1+.03*np.sum(self.h**2, axis=(-2, -1))+.02*np.sum(p**2, axis=(-2, -1))
        dpsi = .03*np.sum(p*dh, axis=(-2, -1))
        pi = psi[..., None, None]**-4*self.geometry.apply(p, inverse=True)
        dq = psi[..., None, None]**4*self.geometry.apply(dh)+4*psi[..., None, None]**3*dpsi[..., None, None]*self.geometry.metric
        full_pairing_error = abs(float(np.sum(pi*dq)-np.sum(self.s*dh)))/self.length**3
        assert full_pairing_error < 5e-13
        return dict(grid_per_axis=self.length, shape_amplitude=self.amplitude,
                    coercivity_relative_error_bound=self.coercivity_error_bound,
                    iterations=iteration+1, initial_momentum_residual=norm(initial)/self.length**1.5,
                    final_momentum_residual=norm(residual)/self.length**1.5,
                    longitudinal_correction_norm=norm(correction)/self.length**1.5,
                    proved_correction_norm_bound=bound/self.length**1.5,
                    first_source_remainder=source_error, first_correction_remainder=first_correction_error,
                    TT_one_form_error=one_form_error, full_metric_pairing_error=full_pairing_error,
                    momentum_adjoint_identity_error=adjoint_error,
                    sampled_relative_gauge_error=relative_gauge_error,
                    sampled_coercivity_ratio=coercivity_ratio)


def momentum_checks():
    rows = [SpectralMomentum(n, amplitude).solve()
            for n, amplitude in itertools.product([5, 7, 9], [.025, .05, .1])]
    for n in [5, 7, 9]:
        selected = [row for row in rows if row['grid_per_axis'] == n]
        ratios = [b['first_source_remainder']/a['first_source_remainder'] for a, b in zip(selected, selected[1:])]
        assert all(3.8 < ratio < 4.2 for ratio in ratios)
    return dict(cases=rows, scope="Spectral discrete momentum constraints on periodic even seeds, with mean-zero vector correction. Checks exact discrete adjoint structure, the correction estimate and nonlinear TT pairing. This does not solve a periodic scalar constraint or prove quantum spatial covariance.")


def energy_velocity_checks():
    rows = []
    for nr, na in [(32, 10), (64, 14), (96, 18)]:
        packet = Packet(nr, na)
        for amplitude in [.12, .2, .32]:
            psi, mass, _ = packet.solve(amplitude)
            source = amplitude**2*packet.source
            w = np.ones_like(psi)
            for _ in range(100):
                updated = 1-7*packet.green(source*psi**-8*w)
                if np.max(abs(updated-w)) < 2e-15:
                    w = updated
                    break
                w = updated
            response_residual = float(np.max(abs(w-1+7*packet.green(source*psi**-8*w))))
            lapse = w/psi
            assert min(lapse.ravel()) > 0 and max(lapse.ravel()) <= 1+1e-13
            assert response_residual < 2e-13
            # The imported packet solver uses G=1, hence kappa=16*pi.
            velocity_pairing = float(2*amplitude*np.sum(w*psi**-7*packet.source*packet.volume)/(16*np.pi))
            step = 1e-4
            numerical_gradient = (packet.solve(amplitude+step)[1]-packet.solve(amplitude-step)[1])/(2*step)
            gradient_error = abs(velocity_pairing-numerical_gradient)
            assert gradient_error < 2e-10
            chi = packet.susceptibility(amplitude, psi)
            scaling_identity = abs(4*amplitude*velocity_pairing-mass-chi)
            assert scaling_identity < 3e-13
            rows.append(dict(radial_points=nr, angular_points=na, amplitude=amplitude,
                             ADM_energy=mass, canonical_velocity_pairing=velocity_pairing,
                             finite_difference_energy_gradient=numerical_gradient,
                             gradient_error=gradient_error, lapse_equation_integral_residual=response_residual,
                             minimum_lapse=float(min(lapse.ravel())),
                             charge_scaling_derivative_identity_error=scaling_identity))
    return dict(cases=rows, scope="Boundary-energy variation on the conformal momentum slice agrees with the weak TT metric velocity and maximal lapse. The pairing uses a TT amplitude variation. No finite-time evolution or packet-center force law is computed.")


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_algebra(), pointwise_cotangent=pointwise_cotangent(),
                  nonlinear_momentum=momentum_checks(), initial_metric_velocity=energy_velocity_checks())
    sources = ['CANONICAL_METRIC_RECONSTRUCTION.md', 'scripts/canonical_metric_reconstruction_audit.py',
               'TENSOR_PACKET_SELF_GRAVITY.md', 'scripts/tensor_packet_self_gravity_audit.py',
               'PREPOTENTIAL_LATTICE_BRIDGE.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'SPIN_CLOCK_BRACKET.md', 'NONLINEAR_TENSOR_BACKREACTION.md',
               'EMBEDDING_VERSUS_GRAVITY.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A small-data classical reconstruction under supplied Einstein constraints restores '
                       'the nonlinear metric and momentum constraints while preserving the TT canonical '
                       'one-form. The momentum-only packet family is isotropic; the extension supplies '
                       'its missing partners. A boundary-energy derivative matches the initial metric '
                       'velocity on that slice. No microscopic phase, complete quantum clock algebra, '
                       'finite-time gravitational evolution, Standard Model, or TOE is proved.')
    target = root/'data/canonical_metric_reconstruction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
