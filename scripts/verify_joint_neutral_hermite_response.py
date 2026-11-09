#!/usr/bin/env python3
"""Independent high-precision checks of finite neutral-Hermite witnesses.

The producer uses differentiated Gaussian moment recurrences. This verifier
instead integrates the saved polynomial with Gauss-Hermite quadrature at
complex-scaled nodes and differentiates through a fresh complex clock solve.
Both quadrature orders integrate the finite polynomial exactly in exact
arithmetic. The computation uses floating arithmetic, not interval bounds;
it verifies a candidate Rayleigh quotient, not a uniform response theorem.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(value):
    return mp.mpf(str(value))


def unpack(value):
    return np.asarray(value['real'])+1j*np.asarray(value['imag'])


def clock(eps, h, s):
    target = mp.exp(s)+eps*s-mp.j*h/2
    guess = s-mp.j*h/(2*(mp.exp(s)+eps))
    z = mp.findroot(lambda t: mp.exp(t)+eps*t-target, guess)
    assert abs(mp.exp(z)+eps*z-target) < mp.mpf('1e-65')
    return mp.exp((z-s)/2)


def polynomial(coefficients, z):
    previous = mp.mpf(1)
    value = coefficients[0]
    if len(coefficients) == 1:
        return value
    current = z
    value += coefficients[1]*current
    for n in range(1, len(coefficients)-1):
        previous, current = current, (z*current-mp.sqrt(n)*previous)/mp.sqrt(n+1)
        value += coefficients[n+1]*current
    return value


def energy_function(witness, order):
    p = witness['parameters']
    eps, h = map(number, [p['epsilon'], p['h']])
    alpha, beta = map(number, [p['alpha'], p['beta']])
    widths = list(map(number, witness['widths']))
    size = p['max_degree']+1
    saved = witness['coefficients']
    c = [mp.mpc(number(a), number(b)) for a, b in zip(saved['real'], saved['imag'])]
    groups = [c[i*size:(i+1)*size] for i in range(len(widths))]
    conjugated = [[mp.conj(a) for a in group] for group in groups]
    nodes, weights = mp.gauss_quadrature(order, 'hermite')

    def energy(t):
        r = clock(eps, h, t)
        eta, L = 2*mp.im(r), 3-2*mp.re(r)
        total = mp.mpf(0)
        for i, wi in enumerate(widths):
            for j in range(i, len(widths)):
                wj = widths[j]
                A = alpha*(mp.conj(r)**2/wi+r*r/wj)/2
                B = alpha*(mp.conj(r)**2*wi+r*r*wj)/2
                C = B-8*beta*mp.im(r)**2
                assert min(mp.re(A), mp.re(B), mp.re(C)) > 0
                value = mp.mpc(0)
                for ix, x in enumerate(nodes):
                    X = x/mp.sqrt(2*beta)
                    for iy, y in enumerate(nodes):
                        # Complex contour rescaling removes the complex Gaussian.
                        # Conjugate coefficients, NOT the complex-scaled argument.
                        Y = y/mp.sqrt(C)
                        left = polynomial(conjugated[i], 2*mp.sqrt(beta)*(X-mp.j*eta*Y))
                        right = polynomial(groups[j], 2*mp.sqrt(beta)*(X+mp.j*eta*Y))
                        field = X+L*Y
                        value += weights[ix]*weights[iy]*left*right*(1+field**2/2+field**4/4)
                value *= mp.pi/(4*A)*mp.sqrt(mp.pi/B)/mp.sqrt(2*beta*C)
                if i == j:
                    assert abs(mp.im(value)) < mp.mpf('1e-65')*max(1, abs(value))
                    total += mp.re(value)
                else:
                    total += 2*mp.re(value)
        return total

    return energy


def verify_candidate(witness, roles):
    p = witness['parameters']
    n = p['dimension']
    K, D, c = map(unpack, [witness['gram'], witness['derivative'], witness['coefficients']])
    assert K.shape == D.shape == (n, n) and c.shape == (n,)
    assert len(witness['widths']) == p['width_count']
    assert all(w >= 1 for w in witness['widths'])
    E = float(np.vdot(c, K@c).real)
    slope = float(np.vdot(c, D@c).real)/E
    assert E > 0 and abs(slope-witness['result']['max_slope']) < 2e-8
    s = number(p['s'])
    results = []
    for order in [p['max_degree']+3, p['max_degree']+5]:
        f = energy_function(witness, order)
        energy = f(s)
        derivative = mp.diff(f, s)
        assert energy > 0
        ratio = derivative/energy
        results.append((energy, ratio))
        print('Verified quadrature order', order, 'slope', mp.nstr(ratio, 24), flush=True)
    e, ratio = results[0]
    quadrature_energy_error = abs(e-results[1][0])/e
    quadrature_slope_error = abs(ratio-results[1][1])
    assert max(quadrature_energy_error, quadrature_slope_error) < mp.mpf('1e-60')
    energy_error = float(abs(e-number(E))/e)
    slope_error = float(abs(ratio-number(witness['result']['max_slope'])))
    assert energy_error < 2e-7 and slope_error < 2e-8
    normalized = number(p['epsilon'])/(mp.exp(s)+number(p['epsilon']))*ratio
    return dict(roles=roles, parameters=p, quadrature_orders=[p['max_degree']+3, p['max_degree']+5],
                energy=mp.nstr(e, 50), slope=mp.nstr(ratio, 50),
                normalized_slope=mp.nstr(normalized, 50), energy_relative_error=energy_error,
                slope_absolute_error=slope_error,
                quadrature_energy_relative_difference=mp.nstr(quadrature_energy_error, 10),
                quadrature_slope_absolute_difference=mp.nstr(quadrature_slope_error, 10))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads(args.report.read_text())
    assert all(digest(root/path) == sha for path, sha in report['source_sha256'].items())
    parent = report['parent_report']
    assert parent['sha256'] == '66969ec1f3595c57cca7a83ea8381bb100f0995f54798b54391b7aba0f6307f5'
    assert digest(root/parent['path']) == parent['sha256']
    assert report['rank_truncation'] is False and report['conditioning_floor'] == 1e-9
    assert report['neutral_sources_zero'] is True
    records = report['records']
    grid = report['grid']
    expected = set(itertools.product(grid['h'], grid['clock_offset'], grid['width_count'], grid['max_degree']))
    actual = {(v['h'], v['clock_offset'], v['width_count'], v['max_degree']) for v in records}
    assert actual == expected and report['test_count'] == len(records) == len(expected)
    valid = [v for v in records if not v.get('rejected_condition')]
    assert report['rejected_cases'] == len(records)-len(valid)
    for v in records:
        assert v['h'] > 0 and v['epsilon'] == v['h']
        assert v['alpha'] == 1/(2*v['h']) and v['beta'] == v['alpha']/32
        assert v['h'] <= math.pi*v['epsilon']/3
        assert abs(v['s']-math.log(v['epsilon'])-v['clock_offset']) < 1e-14
        assert v['dimension'] == v['width_count']*(v['max_degree']+1)
    for v in valid:
        assert v['condition'] < 1e9 and v['hermitian_error'] < 1e-10 and v['eigen_residual'] < 1e-10
        assert abs(v['normalized_max_slope']-v['epsilon']/(math.exp(v['s'])+v['epsilon'])*v['max_slope']) < 1e-14
    mp.mp.dps = 80
    selected = {}
    for role, field in [('largest_observed', 'max_slope'), ('largest_normalized_observed', 'normalized_max_slope')]:
        witness = report[role]
        assert witness['result'][field] == max(v[field] for v in valid)
        assert dict(**witness['parameters'], **witness['result']) in records
        key = json.dumps(witness, sort_keys=True)
        if key not in selected:
            selected[key] = (witness, [])
        selected[key][1].append(role)
    checks = [verify_candidate(witness, roles) for witness, roles in selected.values()]
    result = dict(scope=__doc__, report_sha256=digest(args.report), parent_report=parent,
                  source_sha256=report['source_sha256'], verifier_sha256=digest(Path(__file__)),
                  mpmath_version=mp.__version__, mpmath_precision=80,
                  test_count=report['test_count'], rejected_cases=report['rejected_cases'],
                  candidates=checks, passed=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print('Independent finite polynomial verification passed; uniform estimate remains open.', flush=True)


if __name__ == '__main__':
    main()
