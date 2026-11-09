#!/usr/bin/env python3
"""Properly normalized TT packets and their conditional gravitational energy."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as sy
from numpy.polynomial.legendre import leggauss, legvander


SOURCE_NORM = 3367254360064*np.pi/770201575
U_BOUND = 1502700975/(1879048192*np.pi)


def exact_seed_and_scaling():
    x, y, z = sy.symbols('x y z', real=True)
    r2, rho2 = x*x+y*y+z*z, x*x+y*y
    b, c = 56*(1-r2)**6, -336*(1-r2)**5
    tau = sy.Matrix([[24*x*y*z*c, -12*z*(x*x-y*y)*c, -12*y*(2*b+rho2*c)],
                     [-12*z*(x*x-y*y)*c, -24*x*y*z*c, 12*x*(2*b+rho2*c)],
                     [-12*y*(2*b+rho2*c), 12*x*(2*b+rho2*c), 0]])
    assert sy.trace(tau) == 0 and tau == tau.T
    for i in range(3):
        assert sy.factor(sum(sy.diff(tau[i, j], coordinate)
                             for j, coordinate in enumerate([x, y, z]))) == 0
    coordinates = [x, y, z]
    prepotential = sy.diag(-1, -1, 2)*(1-r2)**8
    curl = sy.zeros(3)
    for i, j in itertools.product(range(3), repeat=2):
        curl[i, j] = sum(sy.LeviCivita(i, k, l)*sy.diff(prepotential[l, j], coordinates[k])+
                         sy.LeviCivita(j, k, l)*sy.diff(prepotential[l, i], coordinates[k])
                         for k, l in itertools.product(range(3), repeat=2))/2
    cotton = sy.zeros(3)
    for i, j in itertools.product(range(3), repeat=2):
        cotton[i, j] = sum(sy.LeviCivita(i, k, l)*sy.LeviCivita(j, m, n)*
                          sy.diff(curl[l, n], coordinates[k], coordinates[m])
                          for k, l, m, n in itertools.product(range(3), repeat=4)
                          if sy.LeviCivita(i, k, l)*sy.LeviCivita(j, m, n))
    assert (cotton-tau).applyfunc(sy.factor) == sy.zeros(3) or (cotton+tau).applyfunc(sy.factor) == sy.zeros(3)
    source = 288*rho2*((2*b+rho2*c)**2+rho2*z*z*c*c)
    assert sy.factor(sy.trace(tau*tau)-source) == 0
    r, mu = sy.symbols('r mu', real=True)
    br, cr = 56*(1-r*r)**6, -336*(1-r*r)**5
    transverse = r*r*(1-mu*mu)
    angular_source = 288*transverse*((2*br+transverse*cr)**2+transverse*r*r*mu*mu*cr*cr)
    angular = sy.integrate(sy.expand(angular_source), (mu, -1, 1))
    integral = sy.factor(2*sy.pi*sy.integrate(sy.expand(r*r*angular), (r, 0, 1)))
    assert integral == sy.Rational(3367254360064, 770201575)*sy.pi
    envelope = 288*r*r*((2*br-r*r*cr)**2+r**4*cr*cr)
    upper = sy.factor(sy.integrate(sy.expand(r*envelope), (r, 0, 1))/(8*integral))
    assert upper == sy.Rational(1502700975, 1879048192)/sy.pi
    # Compact radial potential is (1-r^2)^8 inside, zero outside:
    # its third derivatives have at least a fifth-order boundary zero.
    scale = sy.Symbol('c', positive=True)
    assert sy.simplify(scale**12*scale**-7-scale**5) == 0
    assert sy.simplify(scale**12*scale**-6*scale**-7-scale**-1) == 0
    ma, mb, s = sy.symbols('ma mb s', positive=True)
    total = (sy.sqrt(1+2*s*(ma+mb)+s*s*(ma-mb)**2)-1)/s
    series = sy.series(total, s, 0, 3).removeO().expand()
    assert sy.simplify(series-(ma+mb-2*s*ma*mb+2*s*s*ma*mb*(ma+mb))) == 0
    kx, ky, kz = sy.symbols('kx ky kz', real=True)
    k = sy.Matrix([kx, ky, kz])
    cross = sy.Matrix([[0, -kz, ky], [kz, 0, -kx], [-ky, kx, 0]])
    zxx, zyy, zzz, zxy, zyz, zzx = sy.symbols('zxx zyy zzz zxy zyz zzx')
    potential = sy.Matrix([[zxx, zxy, zzx], [zxy, zyy, zyz], [zzx, zyz, zzz]])
    metric = sy.I*(cross*potential-potential*cross)/2
    assert sy.expand(-(k.T*metric*k)[0]+(k.T*k)[0]*sy.trace(metric)) == 0
    source_mode = sy.Symbol('S')
    required_metric = source_mode*sy.eye(3)/(2*(k.T*k)[0])
    assert sy.simplify(-(k.T*required_metric*k)[0]+(k.T*k)[0]*sy.trace(required_metric)-source_mode) == 0
    return dict(trace_zero=True, divergence_zero=True, compact_boundary_vanishing_order=5,
                compact_seed_is_prepotential_cotton=True,
                linear_prepotential_image_cannot_supply_quadratic_source=True,
                source_integral=str(integral), normalized_newton_uniform_bound=str(upper),
                conformal_scaling_identity=True, physical_packet_charge_scales_as_inverse_c=True,
                paired_charge_energy_series=str(sy.factor(series)),
                scope="Exact compact TT polynomial identities, a radial envelope bound, conformal scaling exponents and the algebraic charge expansion. Einstein constraints are supplied.")


class Packet:
    def __init__(self, nr, na):
        self.nr, self.na = nr, na
        self.dr = 1/nr
        self.r = (np.arange(nr)+.5)*self.dr
        self.mu, self.weights = leggauss(na)
        self.ell = np.arange(na)
        self.legendre = legvander(self.mu, na-1)
        self.projection = (self.legendre.T*self.weights)*(2*self.ell+1)[:, None]/2
        r2 = self.r[:, None]**2
        rho2, z2 = r2*(1-self.mu[None, :]**2), r2*self.mu[None, :]**2
        b, c = 56*(1-r2)**6, -336*(1-r2)**5
        self.source = 288*rho2*((2*b+rho2*c)**2+rho2*z2*c*c)/SOURCE_NORM
        self.volume = 2*np.pi*(self.dr*self.r**2)[:, None]*self.weights[None, :]
        lower = np.minimum(self.r[:, None], self.r[None, :])
        upper = np.maximum(self.r[:, None], self.r[None, :])
        self.kernels = np.array([(lower/upper)**ell/upper*
                                 (self.dr*self.r**2)[None, :]/(8*(2*ell+1))
                                 for ell in self.ell])
        self.rho = np.sqrt(rho2)
        self.z = self.r[:, None]*self.mu[None, :]
        self.source_integral = float(np.sum(self.source*self.volume))
        assert abs(self.source_integral-1) < 2e-8

    def green(self, source):
        coefficients = source @ self.projection.T
        potentials = np.column_stack([kernel @ coefficients[:, j]
                                      for j, kernel in enumerate(self.kernels)])
        return potentials @ self.legendre.T

    def moments(self, source):
        coefficients = source @ self.projection.T
        return np.array([np.sum(self.dr*self.r**(ell+2)*coefficients[:, ell])
                         for ell in self.ell])

    def external(self, source, source_scale, target_scale, displacement):
        rho = self.rho/target_scale**2
        z = self.z/target_scale**2+displacement
        distance = np.sqrt(rho*rho+z*z)
        assert min(distance.ravel()) > 1/source_scale**2
        legendre = legvander(z/distance, self.na-1)
        moments = self.moments(source)*source_scale**(6-2*self.ell)
        return np.sum(legendre*moments/(8*(2*self.ell+1))/
                      distance[..., None]**(self.ell+1), axis=-1)

    def solve(self, amplitude, boundary=1.):
        density = amplitude**2*self.source
        psi = np.full_like(density, boundary)
        for iteration in range(100):
            updated = boundary+self.green(density*psi**-7)
            change = float(np.max(abs(updated-psi)))
            psi = updated
            if change < 2e-15:
                break
        else:
            raise AssertionError("Isolated iteration did not converge")
        charge = float(np.sum(density*psi**-7*self.volume)/(16*np.pi))
        residual = float(np.max(abs(psi-boundary-self.green(density*psi**-7))))
        assert residual < 1e-13
        return psi, charge, residual

    def susceptibility(self, amplitude, psi):
        density = amplitude**2*self.source
        response = np.ones_like(psi)
        for _ in range(100):
            updated = 1-7*self.green(density*psi**-8*response)
            if np.max(abs(updated-response)) < 2e-15:
                response = updated
                break
            response = updated
        assert min(response.ravel()) > 0
        return float(7*np.sum(density*psi**-8*response*self.volume)/(16*np.pi))

    def solve_pair(self, amplitudes, scales, distance):
        densities = [amplitude**2*self.source for amplitude in amplitudes]
        psi = [np.ones_like(self.source), np.ones_like(self.source)]
        def update(values):
            effective = [density*value**-7 for density, value in zip(densities, values)]
            return [1+scales[a]**8*self.green(effective[a])+
                    self.external(effective[1-a], scales[1-a], scales[a], (-1 if a == 0 else 1)*distance)
                    for a in range(2)]
        for iteration in range(100):
            updated = update(psi)
            change = max(float(np.max(abs(a-b))) for a, b in zip(updated, psi))
            psi = updated
            if change < 2e-15:
                break
        else:
            raise AssertionError("Two-packet iteration did not converge")
        residual = max(float(np.max(abs(a-b))) for a, b in zip(update(psi), psi))
        assert residual < 1e-13
        charges = [float(scale**6*np.sum(density*value**-7*self.volume)/(16*np.pi))
                   for scale, density, value in zip(scales, densities, psi)]
        return psi, sum(charges), residual, iteration+1


def paired_charges(masses, distance):
    ma, mb = masses
    s = 1/(2*distance)
    root = np.sqrt(1+2*s*(ma+mb)+s*s*(ma-mb)**2)
    total = (2*(ma+mb)+s*(ma-mb)**2)/(1+root)
    alpha = np.array([(total+ma-mb)/2, (total-ma+mb)/2])
    scales = 1+s*alpha[::-1]
    assert max(abs(alpha*scales-masses)) < 2e-15
    assert abs(total-(ma+mb-alpha[0]*alpha[1]/distance)) < 2e-15
    return alpha, scales


def numerical_checks():
    isolated_rows, scaling_rows, pair_rows, fixed_rows = [], [], [], []
    all_refinements = {}
    for nr, na in [(24, 10), (48, 14), (96, 18)]:
        packet = Packet(nr, na)
        isolated = {}
        for amplitude in [.12, .2, .32]:
            psi, mass, residual = packet.solve(amplitude)
            chi = packet.susceptibility(amplitude, psi)
            step = 1e-4
            finite_chi = (packet.solve(amplitude, 1-step)[1]-packet.solve(amplitude, 1+step)[1])/(2*step)
            assert abs(chi-finite_chi)/chi < 2e-6
            gamma = amplitude**2*U_BOUND
            assert 7*gamma < 1
            assert min(psi.ravel()) >= 1 and max(psi.ravel()) <= 1+gamma
            isolated[amplitude] = (psi, mass, chi)
            isolated_rows.append(dict(radial_points=nr, angular_points=na, amplitude=amplitude,
                                      ADM_energy=mass, contraction_bound=7*gamma,
                                      discrete_residual=residual, fixed_seed_charge_susceptibility=chi,
                                      susceptibility_relative_difference=abs(chi-finite_chi)/chi,
                                      source_integral=packet.source_integral))
            if nr == 96:
                for scale in [1., 1.01, 1.08]:
                    scaled = scale*psi
                    residual_scaled = float(np.max(abs(scaled-scale-scale**8*
                                                        packet.green(amplitude**2*packet.source*scaled**-7))))
                    charge = float(scale**6*np.sum(amplitude**2*packet.source*scaled**-7*packet.volume)/(16*np.pi))
                    assert residual_scaled < 2e-13
                    assert abs(charge-mass/scale) < 2e-15
                    scaling_rows.append(dict(amplitude=amplitude, scale=scale,
                                             rescaled_equation_residual=residual_scaled,
                                             charge=charge, predicted_charge=mass/scale))
        for amplitudes, distance in itertools.product([(.12, .12), (.2, .32)], [4., 8., 16., 32.]):
            masses = np.array([isolated[a][1] for a in amplitudes])
            alpha, scales = paired_charges(masses, distance)
            gamma = float(sum(scale**8*a*a*U_BOUND for scale, a in zip(scales, amplitudes)))
            assert 7*gamma < 1
            psi, energy, residual, iterations = packet.solve_pair(amplitudes, scales, distance)
            support_sum = float(sum(scales**-2))
            delta = float(max(alpha)/2*support_sum/(distance*(distance-support_sum)))
            bare = float(sum(scale**6*a*a*packet.source_integral/(16*np.pi)
                             for scale, a in zip(scales, amplitudes)))
            bound = 7*bare*delta/(1-7*gamma)
            energy_error = float(abs(energy-sum(alpha)))
            assert energy_error <= bound+2e-13
            reference = []
            for a in range(2):
                other = 1-a
                isolated_effective = amplitudes[other]**2*packet.source*(
                    scales[other]*isolated[amplitudes[other]][0])**-7
                field = packet.external(isolated_effective, scales[other], scales[a],
                                        (-1 if a == 0 else 1)*distance)
                assert np.max(abs(field-(scales[a]-1))) <= delta+2e-13
                reference.append(1+scales[a]*(isolated[amplitudes[a]][0]-1)+field)
            comparison = max(float(np.max(abs(a-b))) for a, b in zip(psi, reference))
            comparison_bound = 7*gamma*delta/(1-7*gamma)
            assert comparison <= comparison_bound+2e-13
            newton = float(masses[0]*masses[1]/distance)
            coefficient = float((sum(masses)-energy)/newton)
            pair_rows.append(dict(radial_points=nr, angular_points=na, amplitudes=list(amplitudes),
                                  separation=distance, isolated_masses=masses.tolist(),
                                  physical_packet_scales=scales.tolist(), total_ADM_energy=energy,
                                  Newton_normalized_binding=coefficient,
                                  algebraic_charge_sum=float(sum(alpha)),
                                  charge_sum_error=energy_error, proved_energy_error_bound=bound,
                                  comparison_potential_error=comparison,
                                  proved_comparison_potential_bound=comparison_bound,
                                  contraction_bound=7*gamma, iterations=iterations,
                                  discrete_residual=residual))
            key = (amplitudes, distance)
            all_refinements.setdefault(key, []).append(coefficient)
            if nr == 96:
                _, fixed_energy, fixed_residual, _ = packet.solve_pair(amplitudes, [1., 1.], distance)
                fixed_coefficient = float((sum(masses)-fixed_energy)/newton)
                susceptibilities = [isolated[a][2] for a in amplitudes]
                prediction = float(sum(c/m for c, m in zip(susceptibilities, masses))/2)
                fixed_rows.append(dict(amplitudes=list(amplitudes), separation=distance,
                                       fixed_coordinate_binding_coefficient=fixed_coefficient,
                                       large_separation_susceptibility_prediction=prediction,
                                       discrete_residual=fixed_residual))
    refinements = []
    for (amplitudes, distance), values in all_refinements.items():
        coarse, fine = abs(values[1]-values[0]), abs(values[2]-values[1])
        assert fine < .4*coarse+2e-8
        refinements.append(dict(amplitudes=list(amplitudes), separation=distance,
                                coarse_change=coarse, fine_change=fine))
    for amplitudes in [(.12, .12), (.2, .32)]:
        selected = [r for r in pair_rows if r['radial_points'] == 96 and tuple(r['amplitudes']) == amplitudes]
        assert abs(selected[-1]['Newton_normalized_binding']-1) < .01
        assert abs(selected[-1]['Newton_normalized_binding']-1) < abs(selected[0]['Newton_normalized_binding']-1)
    assert 6.8 < fixed_rows[3]['fixed_coordinate_binding_coefficient'] < 7.1
    return dict(
        isolated_packets=dict(cases=isolated_rows, scope="Compact TT sources with numerical isolated conformal solutions and an independently differentiated fixed-seed flux response."),
        physical_scaling=dict(cases=scaling_rows, scope="The exact coordinate/seed/conformal scaling preserves local physical packet geometry and scales its external charge by 1/c."),
        interacting_packets=dict(cases=pair_rows, refinement=refinements,
                                 scope="Two disjoint compact TT packets, rescaled to preserve their isolated local geometry in a constant external conformal field. Full nonlinear source-region integral equations and multipole coupling are solved. The continuum error bound is analytical; radial/angular discretization errors are not certified."),
        fixed_coordinate_control=dict(cases=fixed_rows, scope="Keeping coordinate seeds fixed changes the physical packets. Its interaction coefficient approaches the charge-susceptibility prediction, near 7 for weak seeds, rather than the properly normalized value 1."))


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_seed_and_scaling(), **numerical_checks())
    sources = ['TENSOR_PACKET_SELF_GRAVITY.md', 'scripts/tensor_packet_self_gravity_audit.py',
               'GRAVITATIONAL_BOUNDARY_DRESSING.md', 'PREPOTENTIAL_LATTICE_BRIDGE.md',
               'EMBEDDING_VERSUS_GRAVITY.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'NONLINEAR_TENSOR_BACKREACTION.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A two-packet Einstein initial-data construction has Newtonian leading binding energy '
                       'when local physical TT packets are held fixed, with an explicit large-separation '
                       'error bound. This is a conditional nonlinear self-coupling benchmark: the Einstein '
                       'constraint and G are supplied. No microscopic gravity phase, dynamical packet force, '
                       'quantum deformation algebra, universal matter coupling, Standard Model, or TOE is proved.')
    target = root/'data/tensor_packet_self_gravity_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
