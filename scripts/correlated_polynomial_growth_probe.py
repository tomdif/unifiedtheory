#!/usr/bin/env python3
"""Degree-growth diagnostic for fixed correlated polynomial clock states.

Full moment matrices use 160-digit arithmetic. A full double-precision
generalized Hermitian eigensolve only SEARCHES for trial coefficients.
Every reported Rayleigh quotient is reevaluated at 160 digits with those
coefficients fixed. No modes are removed. These are finite trial-state
values, not certified maxima, interval bounds, or an unbounded sequence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import mpmath as mp
import numpy as np
import scipy
from scipy.linalg import eigh, eigvalsh
from correlated_polynomial_response_probe import matrices
from joint_neutral_clustered_response_probe import decimal, pack

PARENT = 'data/correlated_polynomial_response_probe.json'
PARENT_SHA = '9de058e5d6ccf4f28e4f61df41f83958a4654c52a5371c4498fd2d4624e8956b'
VERIFICATION = 'data/correlated_polynomial_response_verification.json'
VERIFICATION_SHA = '5ba7bdc44d4b78ab341f9487f603c55df7769c0039189563fa9a7ac3dd436619'
SCRIPTS = ['scripts/correlated_polynomial_growth_probe.py',
           'scripts/verify_correlated_polynomial_growth.py']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cases():
    return [(16, 8), (20, 8), (24, 8), (32, 8),
            (8, 12), (16, 12), (8, 16), (16, 16)]


def candidate(K, D):
    """Search all directions in double; evaluate one fixed vector in mp."""
    n = K.rows
    hermitian_error = max(mp.norm(K-K.H)/mp.norm(K), mp.norm(D-D.H)/mp.norm(D))
    assert hermitian_error < mp.mpf('1e-110')
    assert all(mp.re(K[i, i]) > 0 for i in range(n))
    scale = [mp.sqrt(mp.re(K[i, i])) for i in range(n)]
    G = np.array([[complex(K[i, j]/(scale[i]*scale[j])) for j in range(n)] for i in range(n)])
    T = np.array([[complex(D[i, j]/(scale[i]*scale[j])) for j in range(n)] for i in range(n)])
    double_hermitian = max(np.linalg.norm(G-G.conj().T)/np.linalg.norm(G),
                           np.linalg.norm(T-T.conj().T)/np.linalg.norm(T))
    assert np.isfinite(G).all() and np.isfinite(T).all() and double_hermitian < 1e-13
    # Averaging only removes roundoff skew after checking it; all modes remain.
    G, T = (G+G.conj().T)/2, (T+T.conj().T)/2
    gram_values = eigvalsh(G)
    condition = float(gram_values[-1]/gram_values[0])
    assert gram_values[0] > 0 and np.isfinite(condition) and condition < 1e8
    values, vectors = eigh(T, G, driver='gvd')
    assert len(values) == n and vectors.shape == (n, n)
    lam, v = values[-1], vectors[:, -1]
    double_residual = np.linalg.norm(T@v-lam*(G@v))/(
        (np.linalg.norm(T)+abs(lam)*np.linalg.norm(G))*np.linalg.norm(v))
    assert double_residual < 1e-12
    # mp.mpf(float) preserves the actual binary float, not a rounded display.
    c = mp.matrix([mp.mpc(float(z.real), float(z.imag))/a for z, a in zip(v, scale)])
    energy = (c.H*K*c)[0]
    assert mp.re(energy) > 0 and abs(mp.im(energy)) < mp.mpf('1e-100')*mp.re(energy)
    c /= mp.sqrt(mp.re(energy))
    E, R = (c.H*K*c)[0], (c.H*D*c)[0]
    assert max(abs(mp.im(E)), abs(mp.im(R))) < mp.mpf('1e-100')
    E, R = mp.re(E), mp.re(R)/mp.re(E)
    residual = mp.norm(D*c-R*K*c)/((mp.norm(D)+abs(R)*mp.norm(K))*mp.norm(c))
    discrepancy = abs(R-mp.mpf(float(lam)))
    assert abs(E-1) < mp.mpf('1e-140') and residual < mp.mpf('1e-12')
    assert discrepancy < mp.mpf('1e-9')
    result = dict(rayleigh_slope=decimal(R), energy=decimal(E),
                  hermitian_error=decimal(hermitian_error), eigen_residual=decimal(residual),
                  search_max_slope=float(lam), search_gram_min=float(gram_values[0]),
                  search_gram_max=float(gram_values[-1]), search_condition=condition,
                  search_hermitian_error=float(double_hermitian),
                  search_eigen_residual=float(double_residual), search_rayleigh_difference=decimal(discrepancy))
    return result, c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    assert not args.output.exists(), 'Use a new output path; frozen reports must not be replaced.'
    assert digest(root/PARENT) == PARENT_SHA and digest(root/VERIFICATION) == VERIFICATION_SHA
    parent = json.loads((root/PARENT).read_text())
    old_verification = json.loads((root/VERIFICATION).read_text())
    assert old_verification['passed'] and old_verification['report_sha256'] == PARENT_SHA
    sources = dict(parent['source_sha256'])
    for p in SCRIPTS:
        assert p not in sources
        sources[p] = digest(root/p)
    assert len(sources) == 2566 and all(digest(root/p) == h for p, h in sources.items())
    assert digest(root/'UnifiedTheory.lean') == parent['root_sha256']
    formal = parent['parent_report']
    assert digest(root/formal['path']) == formal['sha256']
    formal_report = json.loads((root/formal['path']).read_text())
    preserved_evidence = {v['path']: v['sha256'] for v in formal_report['numerical_evidence'].values()
                          if isinstance(v, dict) and 'path' in v and 'sha256' in v}
    preserved_evidence.update({PARENT: PARENT_SHA, VERIFICATION: VERIFICATION_SHA})
    assert all(digest(root/p) == h for p, h in preserved_evidence.items())
    mp.mp.dps = 160
    eps = h = mp.mpf(100)
    alpha, beta, s = 1/(2*h), 1/(64*h), mp.log(eps)+1
    records, witnesses = [], {}
    baseline = None
    for max_n, max_d, selected in [(32, 8, cases()[:4]), (16, 16, cases()[4:])]:
        started = time.monotonic()
        print('Assembling full matrix', max_n, max_d, flush=True)
        KF, DF = matrices(alpha, beta, max_n, max_d, eps, h, s)
        print('Matrix ready', max_n, max_d, 'seconds', round(time.monotonic()-started, 2), flush=True)
        for n, d in selected:
            indices = [i*(max_d+1)+j for i in range(n+1) for j in range(d+1)]
            K = mp.matrix([[KF[i, j] for j in indices] for i in indices])
            D = mp.matrix([[DF[i, j] for j in indices] for i in indices])
            result, c = candidate(K, D)
            result['normalized_rayleigh_slope'] = decimal(eps/(mp.exp(s)+eps)*mp.mpf(result['rayleigh_slope']))
            p = dict(h=decimal(h), epsilon=decimal(eps), alpha=decimal(alpha), beta=decimal(beta),
                     s=decimal(s), clock_offset='1', charged_degree=n, neutral_degree=d, dimension=len(indices))
            records.append(dict(parameters=p, result=result))
            if (n, d) == (16, 8):
                old = parent['witnesses']['largest_observed']
                difference = abs(mp.mpf(result['rayleigh_slope'])-mp.mpf(old['result']['max_slope']))
                assert difference < mp.mpf('1e-10')
                baseline = dict(charged_degree=n, neutral_degree=d,
                                previous_high_precision_max=old['result']['max_slope'],
                                candidate_absolute_difference=decimal(difference))
            if not witnesses or mp.mpf(result['rayleigh_slope']) > mp.mpf(witnesses['largest_observed']['result']['rayleigh_slope']):
                witnesses['largest_observed'] = dict(parameters=p, result=result, coefficients=pack(c),
                                                       gram=pack(K), derivative=pack(D))
            print(n, d, 'trial slope', mp.nstr(mp.mpf(result['rayleigh_slope']), 20),
                  'normalized', mp.nstr(mp.mpf(result['normalized_rayleigh_slope']), 16),
                  'double condition', result['search_condition'], flush=True)
    report = dict(scope=__doc__, parent_report=dict(path=PARENT, sha256=PARENT_SHA),
                  parent_verification=dict(path=VERIFICATION, sha256=VERIFICATION_SHA),
                  formal_parent=formal, preserved_numerical_evidence=preserved_evidence,
                  root_sha256=parent['root_sha256'], source_sha256=sources,
                  versions=dict(mpmath=mp.__version__, numpy=np.__version__, scipy=scipy.__version__),
                  moment_precision_digits=160, search_arithmetic='IEEE complex128; full generalized eigensolve',
                  rayleigh_precision_digits=160, rank_truncation=False, certified_maxima=False,
                  neutral_sources_zero=True, basis=parent['basis'], baseline_comparison=baseline,
                  test_count=len(records), rejected_cases=0, records=records, witnesses=witnesses,
                  conclusion='Finite fixed-state Rayleigh values only. No arbitrary-degree upper bound, divergent sequence, Hamiltonian graph limit or physical TOE is established.')
    assert all(digest(root/p) == h for p, h in sources.items())
    assert all(digest(root/p) == h for p, h in preserved_evidence.items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256']
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print('Saved', len(records), 'full-space candidate evaluations.', flush=True)


if __name__ == '__main__':
    main()
