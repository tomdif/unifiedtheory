#!/usr/bin/env python3
"""Independent quadrature of saved correlated polynomial-limit witnesses.

No producer, generating-moment recurrence or clock jet is imported.
Generalized Laguerre rules integrate u^2 and Y; Hermite rules integrate v
and x. The saved complex polynomial is summed before its norm is squared.
Two sufficient quadrature orders are compared. Clock differentiation uses
fresh inverse-clock solves with all saved coefficients frozen. This checks
selected Rayleigh quotients, not every scanned extremum, and is decimal
floating verification rather than interval certification or a Lean proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import mpmath as mp

PARENT = 'data/quantum_correlated_clustered_response_limit_audit.json'
PARENT_SHA = 'f83d4c044b1381e4a0c0231f1e252f5d7a735a16363fa8226991e075b1a176d7'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unpack(saved):
    assert len(saved['real']) == len(saved['imag'])
    return mp.matrix([[mp.mpc(a, b) for a, b in zip(ra, rb)]
                      for ra, rb in zip(saved['real'], saved['imag'])])


def clock(eps, h, s):
    target = mp.exp(s)+eps*s-mp.j*h/2
    z = mp.findroot(lambda t: mp.exp(t)+eps*t-target,
                    s-mp.j*h/(2*(mp.exp(s)+eps)))
    assert abs(mp.exp(z)+eps*z-target) < mp.mpf('1e-140')
    return mp.exp((z-s)/2)


def laguerre_basis(z, degree):
    result = [mp.mpc(1)]
    previous, current = mp.mpc(1), 2-z
    if degree:
        result.append(current/mp.sqrt(2))
    for n in range(1, degree):
        previous, current = current, ((2*n+2-z)*current-(n+1)*previous)/(n+1)
        result.append(current/mp.sqrt(n+2))
    return result


def hermite_basis(z, degree):
    result = [mp.mpc(1)]
    if degree:
        result.append(z)
    for n in range(1, degree):
        result.append((z*result[-1]-mp.sqrt(n)*result[-2])/mp.sqrt(n+1))
    return result


def energy_function(witness, extra):
    p = witness['parameters']
    eps, h, alpha, beta = map(mp.mpf, [p['epsilon'], p['h'], p['alpha'], p['beta']])
    n, d = p['charged_degree'], p['neutral_degree']
    coefficients = list(unpack(witness['coefficients']))
    C = mp.matrix([[coefficients[i*(d+1)+j] for j in range(d+1)] for i in range(n+1)])
    orders = dict(u_squared=n+1+extra, laplace=n+1+extra, v=2*n+d+3+extra, x=d+3+extra)
    U, UW = mp.gauss_quadrature(orders['u_squared'], 'glaguerre', alpha=-mp.mpf('0.5'))
    Y, YW = mp.gauss_quadrature(orders['laplace'], 'laguerre')
    V, VW = mp.gauss_quadrature(orders['v'], 'hermite')
    X, XW = mp.gauss_quadrature(orders['x'], 'hermite')

    def energy(t):
        r = clock(eps, h, t)
        a = alpha*mp.re(r*r)
        c = a-8*beta*mp.im(r)**2
        assert a > 0 and c > 0
        gamma, eta, L = alpha*r*r/2, 2*mp.im(r), 3-2*mp.re(r)
        x_values = [x/mp.sqrt(2*beta) for x in X]
        total = mp.mpf(0)
        for iv, node in enumerate(V):
            v = node/mp.sqrt(c)
            H = mp.matrix([[mp.mpc(0) for _ in X] for _ in range(d+1)])
            for ix, x in enumerate(x_values):
                column = hermite_basis(2*mp.sqrt(beta)*(x+mp.j*eta*v), d)
                for j, value in enumerate(column):
                    H[j, ix] = value
            neutral = C*H
            B = mp.matrix(len(U)*len(Y), n+1)
            for iu, u in enumerate(U):
                for iy, y in enumerate(Y):
                    z = gamma*(u/a+v*v)+mp.conj(gamma)*y/a
                    row = laguerre_basis(2*z, n)
                    for i, value in enumerate(row):
                        B[iu*len(Y)+iy, i] = value
            amplitudes = B*neutral
            x_weights = [XW[ix]*(1+(x+L*v)**2/2+(x+L*v)**4/4) for ix, x in enumerate(x_values)]
            subtotal = mp.mpf(0)
            for iu in range(len(U)):
                for iy in range(len(Y)):
                    row = iu*len(Y)+iy
                    subtotal += UW[iu]*YW[iy]*sum((x_weights[ix]*abs(amplitudes[row, ix])**2
                                                 for ix in range(len(X))), mp.mpf(0))
            total += VW[iv]*subtotal
        return mp.pi/(4*a*mp.sqrt(a*c*2*beta))*total

    return energy, orders


def verify_witness(witness, role):
    p = witness['parameters']
    size = p['dimension']
    K, D, c = [unpack(witness[key]) for key in ['gram', 'derivative', 'coefficients']]
    assert K.rows == K.cols == D.rows == D.cols == c.rows == size and c.cols == 1
    assert size == (p['charged_degree']+1)*(p['neutral_degree']+1)
    assert max(mp.norm(K-K.H)/mp.norm(K), mp.norm(D-D.H)/mp.norm(D)) < mp.mpf('1e-100')
    mp.cholesky((K+K.H)/2)
    E, R = (c.H*K*c)[0], (c.H*D*c)[0]
    assert max(abs(mp.im(E)), abs(mp.im(R))) < mp.mpf('1e-60')
    E, R = mp.re(E), mp.re(R)/mp.re(E)
    assert E > 0 and abs(E-1) < mp.mpf('1e-60')
    assert abs(R-mp.mpf(witness['result']['max_slope'])) < mp.mpf('1e-60')
    residual = mp.norm(D*c-R*K*c)/(mp.norm(D)*mp.norm(c)+abs(R)*mp.norm(K)*mp.norm(c))
    assert residual < mp.mpf('1e-60')
    s = mp.mpf(p['s'])
    checks, results = [], []
    for extra in [0, 1]:
        started = time.monotonic()
        energy, orders = energy_function(witness, extra)
        observed_E = energy(s)
        observed_R = mp.diff(energy, s)/observed_E
        energy_error = abs(observed_E-E)/observed_E
        slope_error = abs(observed_R-R)
        assert max(energy_error, slope_error) < mp.mpf('1e-60')
        checks.append(dict(orders=orders, energy=mp.nstr(observed_E, 100), slope=mp.nstr(observed_R, 100),
                           energy_relative_error=mp.nstr(energy_error, 12), slope_absolute_error=mp.nstr(slope_error, 12)))
        results.append((observed_E, observed_R))
        print(role, orders, 'slope', mp.nstr(observed_R, 35),
              'seconds', round(time.monotonic()-started, 2), flush=True)
    order_error = max(abs(results[0][0]-results[1][0])/results[0][0], abs(results[0][1]-results[1][1]))
    assert order_error < mp.mpf('1e-100')
    normalized = mp.mpf(p['epsilon'])/(mp.exp(s)+mp.mpf(p['epsilon']))*results[0][1]
    return dict(role=role, parameters=p, quadrature=checks, normalized_slope=mp.nstr(normalized, 100),
                quadrature_order_difference=mp.nstr(order_error, 12), saved_matrix_eigen_residual=mp.nstr(residual, 12))


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
    assert len(parent['source_sha256']) == 2562 and len(report['source_sha256']) == 2564
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(digest(root/p) == h for p, h in report['source_sha256'].items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256'] == parent['root_check']['source_sha256']
    assert report['precision'] == 120 and report['rank_truncation'] is False
    assert report['neutral_sources_zero'] is True and report['minimum_precision_margin_digits'] == 65
    assert report['test_count'] == len(report['records']) == 24 and report['rejected_cases'] == 0
    assert {(r['parameters']['charged_degree'], r['parameters']['neutral_degree']) for r in report['records']} == {
        (n, d) for n in [0, 2, 4, 8, 12, 16] for d in [0, 2, 4, 8]}
    mp.mp.dps = 160
    for record in report['records']:
        p, v = record['parameters'], record['result']
        assert mp.mpf(p['epsilon']) == mp.mpf(p['h']) == 100
        assert mp.mpf(p['alpha']) == mp.mpf('0.005') and mp.mpf(p['beta']) == mp.mpf('0.00015625')
        assert p['clock_offset'] == '1' and abs(mp.mpf(p['s'])-mp.log(100)-1) < mp.mpf('1e-115')
        assert p['dimension'] == (p['charged_degree']+1)*(p['neutral_degree']+1)
        assert mp.mpf(v['gram_min_eigenvalue']) > 0 and mp.mpf(v['log10_condition']) < 55
        assert abs(mp.log10(mp.mpf(v['condition']))-mp.mpf(v['log10_condition'])) < mp.mpf('1e-115')
        assert abs(mp.mpf(v['energy'])-1) < mp.mpf('1e-60')
        for key in ['hermitian_error', 'whitened_hermitian_error', 'whitened_eigen_residual', 'eigen_residual', 'reconstruction_error']:
            assert 0 <= mp.mpf(v[key]) < mp.mpf('1e-60')
        assert abs(mp.mpf(v['normalized_max_slope'])-mp.mpf(v['max_slope'])/(mp.e+1)) < mp.mpf('1e-115')
    assert set(report['witnesses']) == {'largest_observed', 'moderate_degree'}
    for role, witness in report['witnesses'].items():
        assert dict(parameters=witness['parameters'], result=witness['result']) in report['records']
        if role == 'largest_observed':
            assert mp.mpf(witness['result']['max_slope']) == max(mp.mpf(r['result']['max_slope']) for r in report['records'])
        else:
            assert witness['parameters']['charged_degree'] == 8 and witness['parameters']['neutral_degree'] == 4
    checks = [verify_witness(w, role) for role, w in report['witnesses'].items()]
    assert all(digest(root/p) == h for p, h in report['source_sha256'].items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256']
    result = dict(scope=__doc__, parent_report=report['parent_report'], report_sha256=digest(args.report),
                  root_sha256=report['root_sha256'], source_sha256=report['source_sha256'],
                  verifier_sha256=digest(Path(__file__)), precision=160, test_count=24,
                  independently_integrated_witness_count=len(checks), candidates=checks,
                  rank_truncation=False, rejected_cases=0, passed=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print('Independent polynomial-limit quadrature verification passed.', flush=True)


if __name__ == '__main__':
    main()
