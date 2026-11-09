#!/usr/bin/env python3
"""Independent high-precision quadrature of clustered-width witnesses.

This verifier does not import the producer or its moment recurrence.
It evaluates the saved finite polynomial through complex-contour Gaussian
quadrature and differentiates through a fresh inverse-clock solve with all
coefficients frozen. Both orders integrate the finite polynomial exactly
in exact arithmetic. All width pairs are included. Decimal floating
arithmetic supplies reproducibility, not an interval-error certificate.
The two selected Rayleigh quotients, not every scan extremum, receive this
independent integral check. No uniform estimate or divergent limit follows.
"""
import argparse
import hashlib
import json
from pathlib import Path
import mpmath as mp

PARENT = 'data/quantum_joint_angular_clock_obstruction_audit.json'
PARENT_SHA = 'b980893bfaf538b30cc5c8896e71099f5ccd5d63fa6a27504749c5a863aff0c3'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unpack(saved):
    assert len(saved['real']) == len(saved['imag'])
    return mp.matrix([[mp.mpc(a, b) for a, b in zip(ra, rb)]
                      for ra, rb in zip(saved['real'], saved['imag'])])


def clock(eps, h, s):
    target = mp.exp(s)+eps*s-mp.j*h/2
    guess = s-mp.j*h/(2*(mp.exp(s)+eps))
    z = mp.findroot(lambda t: mp.exp(t)+eps*t-target, guess)
    assert abs(mp.exp(z)+eps*z-target) < mp.mpf('1e-140')
    return mp.exp((z-s)/2)


def polynomial(coefficients, z):
    previous = mp.mpf(1)
    result = coefficients[0]
    if len(coefficients) == 1:
        return result
    current = z
    result += coefficients[1]*current
    for n in range(1, len(coefficients)-1):
        previous, current = current, (z*current-mp.sqrt(n)*previous)/mp.sqrt(n+1)
        result += coefficients[n+1]*current
    return result


def energy_function(witness, order):
    p = witness['parameters']
    eps, h, alpha, beta = map(mp.mpf, [p['epsilon'], p['h'], p['alpha'], p['beta']])
    widths = list(map(mp.mpf, witness['widths']))
    size = p['max_degree']+1
    c = list(unpack(witness['coefficients']))
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
                        Y = y/mp.sqrt(C)
                        left = polynomial(conjugated[i], 2*mp.sqrt(beta)*(X-mp.j*eta*Y))
                        right = polynomial(groups[j], 2*mp.sqrt(beta)*(X+mp.j*eta*Y))
                        field = X+L*Y
                        value += weights[ix]*weights[iy]*left*right*(1+field**2/2+field**4/4)
                value *= mp.pi/(4*A)*mp.sqrt(mp.pi/B)/mp.sqrt(2*beta*C)
                if i == j:
                    assert abs(mp.im(value)) < mp.mpf('1e-140')*max(1, abs(value))
                    total += mp.re(value)
                else:
                    total += 2*mp.re(value)
        return total

    return energy


def verify_witness(witness, role):
    p = witness['parameters']
    n = p['dimension']
    K, D, c = [unpack(witness[k]) for k in ['gram', 'derivative', 'coefficients']]
    assert K.rows == K.cols == D.rows == D.cols == c.rows == n and c.cols == 1
    assert len(witness['widths']) == p['width_count']
    assert all(mp.mpf(w) == 1+i*mp.mpf(p['width_spacing']) for i, w in enumerate(witness['widths']))
    herr = max(mp.norm(K-K.H)/mp.norm(K), mp.norm(D-D.H)/mp.norm(D))
    assert herr < mp.mpf('1e-105')
    mp.cholesky((K+K.H)/2)
    E = mp.re((c.H*K*c)[0])
    slope = mp.re((c.H*D*c)[0])/E
    assert E > 0
    assert abs(E-1) < mp.mpf('1e-60')
    assert abs(slope-mp.mpf(witness['result']['max_slope'])) < mp.mpf('1e-60')
    residual = mp.norm(D*c-slope*K*c)/(mp.norm(D)*mp.norm(c)+abs(slope)*mp.norm(K)*mp.norm(c))
    assert residual < mp.mpf('1e-60')
    s = mp.mpf(p['s'])
    checks = []
    results = []
    for order in [p['max_degree']+3, p['max_degree']+5]:
        f = energy_function(witness, order)
        energy = f(s)
        derivative = mp.diff(f, s)
        assert energy > 0
        ratio = derivative/energy
        energy_error = abs(energy-E)/energy
        slope_error = abs(ratio-slope)
        assert max(energy_error, slope_error) < mp.mpf('1e-60')
        checks.append(dict(order=order, energy=mp.nstr(energy, 100), slope=mp.nstr(ratio, 100),
                           energy_relative_error=mp.nstr(energy_error, 12),
                           slope_absolute_error=mp.nstr(slope_error, 12)))
        results.append((energy, ratio))
        print(role, 'order', order, 'slope', mp.nstr(ratio, 35), flush=True)
    order_error = max(abs(results[0][0]-results[1][0])/results[0][0],
                      abs(results[0][1]-results[1][1]))
    assert order_error < mp.mpf('1e-100')
    normalized = mp.mpf(p['epsilon'])/(mp.exp(s)+mp.mpf(p['epsilon']))*results[0][1]
    return dict(role=role, parameters=p, quadrature=checks,
                normalized_slope=mp.nstr(normalized, 100),
                quadrature_order_difference=mp.nstr(order_error, 12),
                saved_matrix_eigen_residual=mp.nstr(residual, 12))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads(args.report.read_text())
    assert report['parent_report'] == dict(path=PARENT, sha256=PARENT_SHA)
    assert digest(root/PARENT) == PARENT_SHA
    parent = json.loads((root/PARENT).read_text())
    assert all(digest(root/p) == sha for p, sha in parent['source_sha256'].items())
    assert report['root_sha256'] == parent['root_check']['source_sha256'] == digest(root/'UnifiedTheory.lean')
    assert all(digest(root/p) == sha for p, sha in report['source_sha256'].items())
    assert report['precision'] == 120 and report['rank_truncation'] is False
    assert report['neutral_sources_zero'] is True and report['minimum_precision_margin_digits'] == 65
    assert report['test_count'] == len(report['records']) == 44 and report['rejected_cases'] == 0
    expected = {(d, 1, '0.01') for d in [0, 2, 4, 8]}
    expected |= {(d, n, s) for d in [0, 2, 4, 8] for n in [3, 5, 7] for s in ['0.1', '0.01', '0.001']}
    expected |= {(2, 15, '0.01'), (4, 11, '0.01'), (8, 9, '0.01'), (8, 11, '0.01')}
    actual = {(r['parameters']['max_degree'], r['parameters']['width_count'], r['parameters']['width_spacing']) for r in report['records']}
    assert actual == expected
    mp.mp.dps = 160
    for record in report['records']:
        p, v = record['parameters'], record['result']
        assert mp.mpf(p['h']) == mp.mpf(p['epsilon']) == 100
        assert mp.mpf(p['alpha']) == mp.mpf('0.005') and mp.mpf(p['beta']) == mp.mpf('0.00015625')
        assert mp.mpf(p['h']) < mp.pi*mp.mpf(p['epsilon'])/3
        assert p['clock_offset'] == '1' and abs(mp.mpf(p['s'])-mp.log(100)-1) < mp.mpf('1e-115')
        assert p['dimension'] == p['width_count']*(p['max_degree']+1)
        assert mp.mpf(v['gram_min_eigenvalue']) > 0
        assert mp.mpf(v['log10_condition']) < 55
        assert abs(mp.log10(mp.mpf(v['condition']))-mp.mpf(v['log10_condition'])) < mp.mpf('1e-115')
        assert abs(mp.mpf(v['energy'])-1) < mp.mpf('1e-60')
        for key in ['hermitian_error', 'whitened_hermitian_error', 'whitened_eigen_residual', 'eigen_residual', 'reconstruction_error']:
            assert 0 <= mp.mpf(v[key]) < mp.mpf('1e-60')
        assert abs(mp.mpf(v['normalized_max_slope'])-mp.mpf(v['max_slope'])/(mp.e+1)) < mp.mpf('1e-115')
    assert set(report['witnesses']) == {'largest_observed', 'closest_widths'}
    for role, witness in report['witnesses'].items():
        assert dict(parameters=witness['parameters'], result=witness['result']) in report['records']
        records = [r for r in report['records'] if role == 'largest_observed' or r['parameters']['width_spacing'] == '0.001']
        assert mp.mpf(witness['result']['max_slope']) == max(mp.mpf(r['result']['max_slope']) for r in records)
    checks = [verify_witness(w, role) for role, w in report['witnesses'].items()]
    result = dict(scope=__doc__, report_sha256=digest(args.report), parent_report=report['parent_report'],
                  root_sha256=report['root_sha256'], source_sha256=report['source_sha256'],
                  verifier_sha256=digest(Path(__file__)), mpmath_precision=160,
                  test_count=44, independently_integrated_witness_count=len(checks),
                  rejected_cases=0, rank_truncation=False, candidates=checks, passed=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print('Independent clustered-width verification passed; no uniform estimate is asserted.', flush=True)


if __name__ == '__main__':
    main()
