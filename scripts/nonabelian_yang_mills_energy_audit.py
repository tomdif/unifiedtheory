#!/usr/bin/env python3
"""Curvature, energy defects, and the projected Yang--Mills gradient flow.

All products are evaluated on sufficiently padded Fourier grids. No projection
of curvature is used in the energy. Floating-point diagnostics do not constitute
a certified time integration or a proof of a global continuum limit.
"""
from __future__ import annotations

import json
import random
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

import nonabelian_yang_mills_local_audit as local


def exact_algebra_checks():
    def add(*vs):
        return tuple(sum(v[j] for v in vs) for j in range(3))
    def scale(t, v):
        return tuple(t*x for x in v)
    def bracket(u, v):
        return (2*(u[1]*v[2]-u[2]*v[1]), 2*(u[2]*v[0]-u[0]*v[2]),
                2*(u[0]*v[1]-u[1]*v[0]))
    def dot(u, v):
        return sum(x*y for x, y in zip(u, v))
    def second(a, da, f, df, ddf):
        return add(ddf, bracket(da, f), scale(2, bracket(a, df)), bracket(a, bracket(a, f)))
    rng = random.Random(902611)
    count = 0
    for _ in range(20):
        a, b, ax, by, f, fx, fy, fxx, fyy, phi, l, c = [
            tuple(Q(rng.randint(-5, 5), 7) for _ in range(3)) for _ in range(12)]
        df1, df2 = add(fx, bracket(a, f)), add(fy, bracket(b, f))
        heat = add(second(a, ax, f, fx, fxx), second(b, by, f, fy, fyy), bracket(f, phi))
        assert 2*dot(f, heat)-2*(dot(fx, fx)+dot(f, fxx)+dot(fy, fy)+dot(f, fyy)) == (
            -2*(dot(df1, df1)+dot(df2, df2)))
        assert dot(bracket(a, f), l) == -dot(f, bracket(a, l))
        assert dot(f, bracket(f, phi)) == 0
        t = Q(3, 11)
        ft = add(f, scale(t, l), scale(t*t, c))
        assert dot(ft, ft)/2 == (dot(f, f)/2+t*dot(f, l)
            +t*t*(dot(l, l)/2+dot(f, c))+t**3*dot(l, c)+t**4*dot(c, c)/2)
        count += 4
    return count


def physical(a, m):
    value = np.fft.ifft2(local.pad_coeff(a, m), axes=(0, 1))*m*m
    assert np.max(abs(value.imag)) < 1e-9
    return value.real


def project_grid(value, n):
    m = len(value)
    coeff = np.fft.fft2(value, axes=(0, 1))/(m*m)
    k = local.modes(n) % m
    return coeff[k[:, None], k[None, :]]


def derivative_grid(value, j):
    m = len(value)
    k = np.fft.fftfreq(m)*m
    multiplier = k[:, None] if j == 0 else k[None, :]
    multiplier = multiplier.reshape((m, 1) if j == 0 else (1, m))
    multiplier = multiplier.reshape(multiplier.shape+(1,)*(value.ndim-2))
    out = np.fft.ifft2(2j*np.pi*multiplier*np.fft.fft2(value, axes=(0, 1)), axes=(0, 1))
    assert np.max(abs(out.imag)) < 1e-8
    return out.real


def pair(u, v):
    return float(np.mean(np.sum(u*v, axis=tuple(range(2, u.ndim)))))


def geometry(a, extra_padding=False):
    n = (len(a)-1)//2
    # M>6N gives exact integrals of products of full gradients (degree 3N).
    # M>8N additionally resolves the degree-4N scalar needed for Bochner.
    m = (8 if extra_padding else 6)*n+1
    field = physical(a, m)
    da = [physical(local.derivative(a, j), m) for j in range(2)]
    f = da[0][:, :, 1]-da[1][:, :, 0]+2*np.cross(field[:, :, 0], field[:, :, 1])
    df = [derivative_grid(f, j)+2*np.cross(field[:, :, j], f) for j in range(2)]
    gradient = np.stack((-df[1], df[0]), axis=2)  # Negative YM gradient G.
    phi = da[0][:, :, 0]+da[1][:, :, 1]
    gauge = np.stack([derivative_grid(phi, j)+2*np.cross(field[:, :, j], phi)
                      for j in range(2)], axis=2)
    return {'field': field, 'F': f, 'DF': df, 'G': gradient, 'phi': phi,
            'gauge': gauge, 'deturck': gradient+gauge, 'energy': .5*pair(f, f)}


def curvature_variation(field, velocity):
    return (derivative_grid(velocity[:, :, 1], 0)-derivative_grid(velocity[:, :, 0], 1)
            +2*np.cross(velocity[:, :, 0], field[:, :, 1])
            +2*np.cross(field[:, :, 0], velocity[:, :, 1]))


def random_field(n, rng, scale=.02):
    a = rng.normal(size=(2*n+1, 2*n+1, 2, 3))+1j*rng.normal(size=(2*n+1, 2*n+1, 2, 3))
    return scale*(a+np.conj(a[::-1, ::-1]))/2


def identity_checks():
    rng = np.random.default_rng(54382)
    rows = []
    for n in (1, 2, 3):
        a = random_field(n, rng)
        v = random_field(n, rng)
        d = geometry(a, extra_padding=True)
        m = len(d['F'])
        projected_g = project_grid(d['G'], n)
        projected_z = project_grid(d['deturck'], n)
        pg = physical(projected_g, m)
        pz = physical(projected_z, m)
        residual = pz-d['deturck']
        gauge_work = pair(d['G'], d['gauge'])
        full_speed = pair(d['G'], d['G'])
        projected_speed = pair(pg, pg)
        energy_rate = -pair(d['G'], pz)
        defect_error = abs(energy_rate+full_speed+pair(d['G'], residual))
        projection_error = abs(pair(d['G'], pg)-projected_speed)
        assert abs(gauge_work) < 2e-10
        assert defect_error < 2e-10
        assert projection_error < 2e-10
        assert energy_rate+.5*full_speed <= .5*pair(residual, residual)+2e-10
        old_rhs_error = float(np.max(abs(projected_z-local.diffusion(a)-local.nonlinear(a))))
        assert old_rhs_error < 2e-11
        fdot = curvature_variation(d['field'], d['deturck'])
        covlap = sum(derivative_grid(d['DF'][j], j)+2*np.cross(d['field'][:, :, j], d['DF'][j])
                     for j in range(2))
        curvature_error = float(np.max(abs(fdot-covlap-2*np.cross(d['F'], d['phi']))))
        f2 = np.sum(d['F']**2, axis=-1)
        lap_f2 = sum(derivative_grid(derivative_grid(f2, j), j) for j in range(2))
        bochner = (2*np.sum(d['F']*fdot, axis=-1)-lap_f2
                   +2*sum(np.sum(x*x, axis=-1) for x in d['DF']))
        bochner_error = float(np.max(abs(bochner)))
        assert curvature_error < 2e-9
        assert bochner_error < 2e-8
        vphysical = physical(v, m)
        linear_f = curvature_variation(d['field'], vphysical)
        quadratic_f = 2*np.cross(vphysical[:, :, 0], vphysical[:, :, 1])
        directional = pair(d['F'], linear_f)
        gradient_error = abs(directional+pair(d['G'], vphysical))
        assert gradient_error < 2e-11
        step = .13
        expanded = (d['energy']+step*directional
                    +step**2*(.5*pair(linear_f, linear_f)+pair(d['F'], quadratic_f))
                    +step**3*pair(linear_f, quadratic_f)+.5*step**4*pair(quadratic_f, quadratic_f))
        quartic_error = abs(geometry(a+step*v)['energy']-expanded)
        assert quartic_error < 2e-11
        eps = 1e-6
        fd_directional = (geometry(a+eps*v)['energy']-geometry(a-eps*v)['energy'])/(2*eps)
        fd_error = abs(fd_directional-directional)
        assert fd_error < 2e-7
        rows.append({'cutoff': n, 'gauge_work_abs': abs(gauge_work),
                     'energy_defect_identity_error': defect_error,
                     'projected_gradient_identity_error': projection_error,
                     'agreement_with_existing_DeTurck_rhs': old_rhs_error,
                     'curvature_evolution_max_error': curvature_error,
                     'pointwise_bochner_max_error': bochner_error,
                     'energy_gradient_pairing_error': gradient_error,
                     'quartic_energy_expansion_error': quartic_error,
                     'centered_energy_difference_error': fd_error,
                     'nonzero_projection_residual_L2': float(np.sqrt(pair(residual, residual)))})
    return rows


def integrate_gradient(init, tmax, tight=False):
    n = (len(init)-1)//2
    shape = init.shape
    def rhs(_, state):
        a = state[:-1].reshape(shape)
        pg = project_grid(geometry(a)['G'], n)
        speed = float(np.sum(abs(pg)**2))
        return np.concatenate((pg.ravel(), np.array([speed])))
    sol = solve_ivp(rhs, (0, tmax), np.concatenate((init.ravel(), np.zeros(1))),
                    method='DOP853', t_eval=np.linspace(0, tmax, 41),
                    rtol=2e-12 if tight else 2e-10,
                    atol=2e-14 if tight else 2e-12,
                    max_step=tmax/(64 if tight else 32))
    assert sol.success, sol.message
    fields = [x[:-1].reshape(shape) for x in sol.y.T]
    energies = [geometry(a)['energy'] for a in fields]
    accumulated = sol.y[-1].real
    balance_error = float(np.max(abs(np.asarray(energies)+accumulated-energies[0])))
    distances = [float(np.sum(abs(a-init)**2)) for a in fields]
    assert balance_error < 2e-8
    assert all(b <= a+2e-11 for a, b in zip(energies, energies[1:]))
    assert all(d <= t*energies[0]+2e-10 for t, d in zip(sol.t, distances))
    return fields, {'cutoff': n, 'end_time': tmax, 'samples': len(sol.t),
                    'initial_energy': energies[0], 'final_energy': energies[-1],
                    'max_energy_balance_error': balance_error,
                    'accumulated_squared_speed': float(accumulated[-1]),
                    'final_excursion_L2': float(np.sqrt(distances[-1])),
                    'analytic_excursion_bound': float(np.sqrt(tmax*energies[0])),
                    'rhs_evaluations': sol.nfev}


def armijo_steps(init, tmax):
    a = init.copy()
    n = (len(a)-1)//2
    t = 0.
    energies = [geometry(a)['energy']]
    accepted, rejected = 0, 0
    min_margin = float('inf')
    while t < tmax-1e-14:
        d = geometry(a)
        h = project_grid(d['G'], n)
        speed = float(np.sum(abs(h)**2))
        assert speed > 1e-20
        step = min(.05, tmax-t)
        for _ in range(60):
            candidate = a+step*h
            new_energy = geometry(candidate)['energy']
            margin = d['energy']-.5*step*speed-new_energy
            if margin >= 0:
                break
            rejected += 1
            step /= 2
        else:
            raise AssertionError('Line search did not accept a step')
        a = candidate
        t += step
        accepted += 1
        energies.append(new_energy)
        min_margin = min(min_margin, margin)
        assert accepted < 10000
    assert all(b < a for a, b in zip(energies, energies[1:]))
    return {'cutoff': n, 'end_time': t, 'accepted_steps': accepted,
            'rejected_trial_steps': rejected, 'initial_energy': energies[0],
            'final_energy': energies[-1], 'minimum_Armijo_margin': min_margin,
            'energy_decreases_at_every_accepted_step': True,
            'qualification': 'Ordinary floating-point line search, not interval-certified. '
                             'Accepted steps approximate a different finite ODE from the DeTurck cutoff.'}


def main():
    rational = exact_algebra_checks()
    identities = identity_checks()
    init = 15*local.project(local.initial_data(8), 2)
    fields, evolution = integrate_gradient(init, .4)
    refined, refined_info = integrate_gradient(init, .4, tight=True)
    refinement_error = max(float(np.sqrt(np.sum(abs(a-b)**2))) for a, b in zip(fields, refined))
    assert refinement_error < 2e-8
    evolution['tighter_integration_max_L2_difference'] = refinement_error
    evolution['tighter_integration_energy_balance_error'] = refined_info['max_energy_balance_error']
    evolution['qualification'] = ('Finite-N experiment supported by the global finite-ODE theorem. '
                                  'No global continuum convergence or rigorous ODE error enclosure claimed.')
    report = {'status': 'PASS', 'exact_rational_checks': rational,
              'nonconstant_field_identity_checks': identities,
              'global_finite_ODE_experiment': evolution,
              'energy_decreasing_time_steps': armijo_steps(init, .4),
              'scope': 'Continuum identities, existing DeTurck cutoff energy defect, '
                       'and distinct projected-gradient finite model.',
              'padding': '6N+1 for exact gradient-energy integrals; 8N+1 for scalar Bochner derivatives.'}
    out = Path(__file__).resolve().parents[1]/'data/nonabelian_yang_mills_energy_audit.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'rational_checks': rational,
                      'energy_balance_error': evolution['max_energy_balance_error'],
                      'initial_energy': evolution['initial_energy'],
                      'final_energy': evolution['final_energy'],
                      'Armijo_steps': report['energy_decreasing_time_steps']['accepted_steps'],
                      'output': str(out)}, indent=2))


if __name__ == '__main__':
    main()
