#!/usr/bin/env python3
"""Finite high-precision response diagnostic in the proved polynomial limit.

The basis is L_n^1(2Z)/sqrt(n+1) times He_m(2sqrt(beta)N)/sqrt(m!).
Every charged/neutral cross term is retained. Gaussian/Laplace generating
moments and first-order clock jets form the full energy and derivative
matrices. No width difference, numerical rank truncation or mode cutoff
is used. All coherent sources are zero in this finite scan. This is not
an interval certificate, a Lean inequality, an arbitrary-degree bound,
a divergent sequence, or a full-Hamiltonian/evolution result.
"""
import argparse
import hashlib
import json
from pathlib import Path
import mpmath as mp
from joint_neutral_clustered_response_probe import geometry, spectral, pack, decimal

PARENT = 'data/quantum_correlated_clustered_response_limit_audit.json'
PARENT_SHA = 'f83d4c044b1381e4a0c0231f1e252f5d7a735a16363fa8226991e075b1a176d7'


class Jet:
    """Value and exact first-order derivative arithmetic (up to mp rounding)."""
    __slots__ = ('value', 'slope')

    def __init__(self, value=0, slope=0):
        self.value, self.slope = mp.mpc(value), mp.mpc(slope)

    @staticmethod
    def of(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __add__(self, other):
        other = Jet.of(other)
        return Jet(self.value+other.value, self.slope+other.slope)
    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, -self.slope)

    def __sub__(self, other):
        return self+-Jet.of(other)

    def __rsub__(self, other):
        return Jet.of(other)+-self

    def __mul__(self, other):
        other = Jet.of(other)
        return Jet(self.value*other.value, self.slope*other.value+self.value*other.slope)
    __rmul__ = __mul__

    def __pow__(self, n):
        if n == 0:
            return Jet(1)
        return Jet(self.value**n, n*self.value**(n-1)*self.slope)

    def __truediv__(self, other):
        return self*Jet.of(other)**-1

    def conjugate(self):
        return Jet(mp.conj(self.value), mp.conj(self.slope))


def polyadd(*parts):
    result = [Jet() for _ in range(max(map(len, parts)))]
    for part in parts:
        for i, coefficient in enumerate(part):
            result[i] = result[i]+coefficient
    # Remove only algebraically zero trailing coefficients, never small ones.
    while len(result) > 1 and result[-1].value == result[-1].slope == 0:
        result.pop()
    return result


def polyscale(P, a):
    return [a*x for x in P]


def polymul(P, Q):
    result = [Jet() for _ in range(len(P)+len(Q)-1)]
    for i, a in enumerate(P):
        for j, b in enumerate(Q):
            result[i+j] = result[i+j]+a*b
    return result


def neutral_polynomials(beta, degree, r, rp):
    """Normalized Gaussian Hermite/field moments as polynomials in 1/C.

    C is the v-coordinate Gaussian width. Clock jets in these coefficients
    differentiate eta=2Im(r) and field slope L=3-2Re(r); C motion is handled
    independently by the charged generating moments.
    """
    eta, L = Jet(2*mp.im(r), 2*mp.im(rp)), Jet(3-2*mp.re(r), -2*mp.re(rp))
    vx = 1/(4*beta)
    diagonal = [Jet(), -2*beta*eta**2]
    mixed = [Jet(1), 2*beta*eta**2]
    uf = [Jet(2*mp.sqrt(beta)*vx), -mp.j*mp.sqrt(beta)*eta*L]
    vf = [a.conjugate() for a in uf]
    ff = [Jet(vx), L**2/2]
    M = {(0, 0, 0): [Jet(1)]}

    def fill(key, terms):
        M[key] = polyadd(*[polyscale(polymul(c, M[k]), a) for a, c, k in terms]) if terms else [Jet()]

    for k in range(1, 5):
        fill((0, 0, k), [(k-1, ff, (0, 0, k-2))] if k >= 2 else [])
    for n in range(1, degree+1):
        for k in range(5):
            terms = []
            if n >= 2:
                terms.append((mp.sqrt(mp.mpf(n-1)/n), diagonal, (0, n-2, k)))
            if k:
                terms.append((k/mp.sqrt(n), vf, (0, n-1, k-1)))
            fill((0, n, k), terms)
    for m in range(1, degree+1):
        for n in range(degree+1):
            for k in range(5):
                terms = []
                if m >= 2:
                    terms.append((mp.sqrt(mp.mpf(m-1)/m), diagonal, (m-2, n, k)))
                if n:
                    terms.append((mp.sqrt(mp.mpf(n)/m), mixed, (m-1, n-1, k)))
                if k:
                    terms.append((k/mp.sqrt(m), uf, (m-1, n, k-1)))
                fill((m, n, k), terms)
    return {(m, n): polyadd(M[m, n, 0], polyscale(M[m, n, 2], mp.mpf('0.5')),
                            polyscale(M[m, n, 4], mp.mpf('0.25')))
            for m in range(degree+1) for n in range(degree+1)}


def charged_moments(alpha, beta, degree, max_inverse_power, r, rp):
    """Taylor coefficients of A^-1 B^-1/2 C^(-p-1/2), with clock jets.

    A=a-gamma*t-conj(gamma)*u; B=a-conj(gamma)*t-gamma*u;
    C=B-8beta Im(r)^2. Coefficient t^i u^j integrates Zbar^i Z^j/(i!j!).
    The fixed triangular Laguerre transformation is applied after forming
    every generating coefficient, and is also applied to the derivative.
    """
    gamma = Jet(alpha*r*r/2, alpha*r*rp)
    gc = gamma.conjugate()
    a = Jet(alpha*mp.re(r*r), 2*alpha*mp.re(r*rp))
    c = a-8*beta*Jet(mp.im(r), mp.im(rp))**2
    assert mp.re(a.value) > 0 and mp.re(c.value) > 0
    length = 2*degree+1
    B = [mp.rf(mp.mpf('0.5'), k)/mp.factorial(k)*a**(-k-mp.mpf('0.5')) for k in range(length)]
    A = [[mp.binomial(i+j, i)*gamma**i*gc**j*a**(-i-j-1)
          for j in range(degree+1)] for i in range(degree+1)]
    laguerre = mp.matrix(degree+1)
    for i in range(degree+1):
        for j in range(i+1):
            laguerre[i, j] = (-2)**j*mp.binomial(i+1, i-j)/mp.sqrt(i+1)
    result = []
    for p in range(max_inverse_power+1):
        C = [mp.rf(p+mp.mpf('0.5'), k)/mp.factorial(k)*c**(-k-p-mp.mpf('0.5')) for k in range(length)]
        J = [sum((B[k]*C[l-k] for k in range(l+1)), Jet()) for l in range(length)]
        BC = [[mp.binomial(i+j, i)*gc**i*gamma**j*J[i+j]
               for j in range(degree+1)] for i in range(degree+1)]
        values, slopes = mp.matrix(degree+1), mp.matrix(degree+1)
        for i in range(degree+1):
            for j in range(degree+1):
                x = sum((A[k][l]*BC[i-k][j-l] for k in range(i+1) for l in range(j+1)), Jet())
                values[i, j], slopes[i, j] = x.value, x.slope
        values = laguerre*values*laguerre.T
        slopes = laguerre*slopes*laguerre.T
        result.append((values, slopes))
    return result


def matrices(alpha, beta, charged, neutral, eps, h, s):
    r, rp = geometry(eps, h, s)
    H = neutral_polynomials(beta, neutral, r, rp)
    G = charged_moments(alpha, beta, charged, max(len(P)-1 for P in H.values()), r, rp)
    size, stride = (charged+1)*(neutral+1), neutral+1
    K, D = mp.matrix(size), mp.matrix(size)
    prefactor = mp.pi**mp.mpf('2.5')/(4*mp.sqrt(2*beta))
    for i in range(charged+1):
        for j in range(charged+1):
            for m in range(neutral+1):
                for n in range(neutral+1):
                    value = sum((coefficient.value*G[p][0][i, j] for p, coefficient in enumerate(H[m, n])), mp.mpc(0))
                    slope = sum((coefficient.slope*G[p][0][i, j]+coefficient.value*G[p][1][i, j]
                                 for p, coefficient in enumerate(H[m, n])), mp.mpc(0))
                    K[i*stride+m, j*stride+n] = prefactor*value
                    D[i*stride+m, j*stride+n] = prefactor*slope
    return K, D


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validation():
    from joint_neutral_clustered_response_probe import pair
    eps, h, s = mp.mpf(100), mp.mpf(100), mp.log(100)+1
    alpha, beta = 1/(2*h), 1/(64*h)
    K, D = matrices(alpha, beta, 3, 3, eps, h, s)
    r, rp = geometry(eps, h, s)
    oldK, oldD = pair(alpha, beta, 1, 1, 3, r, rp)
    baseline = max(mp.norm(K[:4, :4]-oldK)/mp.norm(oldK), mp.norm(D[:4, :4]-oldD)/mp.norm(oldD))
    assert baseline < mp.mpf('1e-105')
    checks = []
    for i, j in [(0, 0), (1, 7), (6, 11), (15, 15)]:
        derivative = mp.diff(lambda t: matrices(alpha, beta, 3, 3, eps, h, t)[0][i, j], s)
        error = abs(derivative-D[i, j])/max(1, abs(derivative))
        assert error < mp.mpf('1e-100')
        checks.append(dict(row=i, column=j, derivative_relative_error=decimal(error)))
    return dict(common_width_degree_zero_relative_error=decimal(baseline), clock_derivative_checks=checks)


def cases():
    return [(n, d) for d in [0, 2, 4, 8] for n in [0, 2, 4, 8, 12, 16]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    assert digest(root/PARENT) == PARENT_SHA
    parent = json.loads((root/PARENT).read_text())
    sources = dict(parent['source_sha256'])
    for path in ['scripts/correlated_polynomial_response_probe.py', 'scripts/verify_correlated_polynomial_response.py']:
        assert path not in sources
        sources[path] = digest(root/path)
    assert all(digest(root/p) == sha for p, sha in sources.items())
    assert digest(root/'UnifiedTheory.lean') == parent['root_check']['source_sha256']
    mp.mp.dps = 120
    checks = validation()
    eps = h = mp.mpf(100)
    alpha, beta, s = 1/(2*h), 1/(64*h), mp.log(eps)+1
    records, witnesses = [], {}
    # The largest matrix is assembled once; every smaller case is its exact
    # principal submatrix in the fixed, clock-independent polynomial basis.
    Kfull, Dfull = matrices(alpha, beta, 16, 8, eps, h, s)
    for charged, neutral in cases():
        indices = [i*9+j for i in range(charged+1) for j in range(neutral+1)]
        K = mp.matrix([[Kfull[i, j] for j in indices] for i in indices])
        D = mp.matrix([[Dfull[i, j] for j in indices] for i in indices])
        result, c = spectral(K, D)
        result['normalized_max_slope'] = eps/(mp.exp(s)+eps)*result['max_slope']
        params = dict(h=decimal(h), epsilon=decimal(eps), alpha=decimal(alpha), beta=decimal(beta),
                      s=decimal(s), clock_offset='1', charged_degree=charged, neutral_degree=neutral,
                      dimension=len(indices))
        values = {k: decimal(v) for k, v in result.items()}
        records.append(dict(parameters=params, result=values))
        if 'largest_observed' not in witnesses or result['max_slope'] > mp.mpf(witnesses['largest_observed']['result']['max_slope']):
            witnesses['largest_observed'] = dict(parameters=params, result=values, coefficients=pack(c), gram=pack(K), derivative=pack(D))
        if charged == 8 and neutral == 4:
            witnesses['moderate_degree'] = dict(parameters=params, result=values, coefficients=pack(c), gram=pack(K), derivative=pack(D))
        print(charged, neutral, 'slope', mp.nstr(result['max_slope'], 20),
              'normalized', mp.nstr(result['normalized_max_slope'], 16),
              'log10(condition)', mp.nstr(result['log10_condition'], 10), flush=True)
    report = dict(scope=__doc__, parent_report=dict(path=PARENT, sha256=PARENT_SHA),
                  root_sha256=parent['root_check']['source_sha256'], source_sha256=sources,
                  mpmath_version=mp.__version__, precision=120, rank_truncation=False,
                  minimum_precision_margin_digits=65, neutral_sources_zero=True,
                  basis='L_n^1(2Z)/sqrt(n+1) * He_m(2sqrt(beta)N)/sqrt(m!), charged-major then neutral',
                  validation=checks, test_count=len(records), rejected_cases=0, records=records, witnesses=witnesses,
                  conclusion='Finite polynomial-limit evidence only. The Lean confluence theorem links proved strict inequalities to finite widths, but this floating scan is not such a proof, an unbounded sequence, or a state-uniform estimate.')
    assert all(digest(root/p) == sha for p, sha in sources.items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256']
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print('Completed', len(records), 'full-matrix cases; no modes discarded.', flush=True)


if __name__ == '__main__':
    main()
