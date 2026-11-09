#!/usr/bin/env python3
"""High-precision finite diagnostic for nearly coincident charged widths.

Evaluate every cross term of the actual transverse potential kernel and
its frozen-coefficient clock derivative. The neutral basis is
He_n(2*sqrt(beta)*z)/sqrt(n!), with zero exponential source. Closely spaced
widths retain all directions through high-precision Cholesky whitening;
there is no rank truncation or eigenvalue cutoff. These are finite floating
computations, not an interval certificate, a Lean theorem, a uniform bound,
a full-clock response calculation, or an evolution statement.
"""
import argparse
import hashlib
import json
from pathlib import Path
import mpmath as mp

PARENT = 'data/quantum_joint_angular_clock_obstruction_audit.json'
PARENT_SHA = 'b980893bfaf538b30cc5c8896e71099f5ccd5d63fa6a27504749c5a863aff0c3'

def geometry(eps,h,s):
    target=mp.exp(s)+eps*s-mp.j*h/2
    z=mp.findroot(lambda z:mp.exp(z)+eps*z-target,s-mp.j*h/(2*(mp.exp(s)+eps)))
    r=mp.exp((z-s)/2)
    rp=mp.exp(s)*r*(1-r*r)/(2*(eps+mp.exp(s)*r*r))
    return r,rp


def pair(alpha,beta,wi,wj,degree,r,rp,b=0):
    A=alpha/2*(mp.conj(r)**2/wi+r*r/wj)
    B=alpha/2*(mp.conj(r)**2*wi+r*r*wj)
    C=B-8*beta*mp.im(r)**2
    Ap=alpha*(mp.conj(r*rp)/wi+r*rp/wj)
    Bp=alpha*(mp.conj(r*rp)*wi+r*rp*wj)
    Cp=Bp-16*beta*mp.im(r)*mp.im(rp)
    assert min(mp.re(A),mp.re(B),mp.re(C))>0
    eta,etap=2*mp.im(r),2*mp.im(rp)
    L,Lp=3-2*mp.re(r),-2*mp.re(rp)
    vx,vy=1/(4*beta),1/(2*C)
    vyp=-Cp/(2*C*C)
    diagonal=-4*beta*eta*eta*vy
    diagonalp=-4*beta*(2*eta*etap*vy+eta*eta*vyp)
    mixed,mixedp=1-diagonal,-diagonalp
    uf=2*mp.sqrt(beta)*(vx-mp.j*eta*L*vy)
    ufp=-2*mp.j*mp.sqrt(beta)*(etap*L*vy+eta*Lp*vy+eta*L*vyp)
    vf=2*mp.sqrt(beta)*(vx+mp.j*eta*L*vy)
    vfp=-ufp
    ff=vx+L*L*vy
    ffp=2*L*Lp*vy+L*L*vyp
    dx=mp.conj(b)+b
    dy=mp.j*eta*(b-mp.conj(b))
    dyp=mp.j*etap*(b-mp.conj(b))
    mx,my=dx/(4*beta),dy/(2*C)
    myp=dyp/(2*C)-dy*Cp/(2*C*C)
    mu=2*mp.sqrt(beta)*(mx-mp.j*eta*my)
    mup=-2*mp.j*mp.sqrt(beta)*(etap*my+eta*myp)
    mv=2*mp.sqrt(beta)*(mx+mp.j*eta*my)
    mvp=-mup
    mf,mfp=mx+L*my,Lp*my+L*myp
    M={(0,0,0):mp.mpc(1)}
    S={(0,0,0):mp.mpc(0)}
    def fill(key,terms):
        M[key]=sum(a*c*M[k] for a,c,cp,k in terms)
        S[key]=sum(a*(cp*M[k]+c*S[k]) for a,c,cp,k in terms)
    for k in range(1,5):
        terms=[(1,mf,mfp,(0,0,k-1))]
        if k>=2:terms.append((k-1,ff,ffp,(0,0,k-2)))
        fill((0,0,k),terms)
    for n in range(1,degree+1):
        for k in range(5):
            terms=[(1/mp.sqrt(n),mv,mvp,(0,n-1,k))]
            if n>=2:terms.append((mp.sqrt(mp.mpf(n-1)/n),diagonal,diagonalp,(0,n-2,k)))
            if k:terms.append((k/mp.sqrt(n),vf,vfp,(0,n-1,k-1)))
            fill((0,n,k),terms)
    for m in range(1,degree+1):
        for n in range(degree+1):
            for k in range(5):
                terms=[(1/mp.sqrt(m),mu,mup,(m-1,n,k))]
                if m>=2:terms.append((mp.sqrt(mp.mpf(m-1)/m),diagonal,diagonalp,(m-2,n,k)))
                if n:terms.append((mp.sqrt(mp.mpf(n)/m),mixed,mixedp,(m-1,n-1,k)))
                if k:terms.append((k/mp.sqrt(m),uf,ufp,(m-1,n,k-1)))
                fill((m,n,k),terms)
    pref=mp.pi/(4*A)*mp.sqrt(mp.pi/B)*mp.sqrt(mp.pi/C)*mp.sqrt(mp.pi/(2*beta))
    pref*=mp.exp(dx*dx/(8*beta)+dy*dy/(4*C)-mp.re(b)**2/(2*beta))
    score=-Ap/A-Bp/(2*B)-Cp/(2*C)+dy*dyp/(2*C)-dy*dy*Cp/(4*C*C)
    K,D=mp.matrix(degree+1),mp.matrix(degree+1)
    for m in range(degree+1):
        for n in range(degree+1):
            poly=M[m,n,0]+M[m,n,2]/2+M[m,n,4]/4
            polyp=S[m,n,0]+S[m,n,2]/2+S[m,n,4]/4
            K[m,n]=pref*poly
            D[m,n]=pref*(score*poly+polyp)
    return K,D


def spectral(K, D):
    """Full generalized eigensolve, with a precision margin, never a cutoff."""
    n = K.rows
    assert n == K.cols == D.rows == D.cols
    assert all(mp.re(K[i, i]) > 0 for i in range(n))
    scales = [mp.sqrt(mp.re(K[i, i])) for i in range(n)]
    G = mp.matrix(n)
    T = mp.matrix(n)
    for i in range(n):
        for j in range(n):
            G[i, j] = K[i, j]/(scales[i]*scales[j])
            T[i, j] = D[i, j]/(scales[i]*scales[j])
    hermitian_error = max(mp.norm(G-G.H)/mp.norm(G), mp.norm(T-T.H)/mp.norm(T))
    assert hermitian_error < mp.mpf('1e-105')
    G, T = (G+G.H)/2, (T+T.H)/2
    ev = mp.eighe(G, eigvals_only=True)
    assert ev[0] > 0
    condition = ev[n-1]/ev[0]
    # Failing this assertion rejects the whole solve; no mode is removed.
    assert mp.log10(condition) < mp.mp.dps-65
    L = mp.cholesky(G)
    invL = L**-1
    W = invL*T*invL.H
    whitened_hermitian_error = mp.norm(W-W.H)/mp.norm(W)
    assert whitened_hermitian_error < mp.mpf('1e-60')
    W = (W+W.H)/2
    vals, vec = mp.eighe(W)
    v = vec[:, n-1]
    whitened_residual = mp.norm(W*v-vals[n-1]*v)/mp.norm(W)
    c = invL.H*v
    for i in range(n):
        c[i] /= scales[i]
    raw_energy = (c.H*K*c)[0]
    raw_response = (c.H*D*c)[0]
    assert abs(mp.im(raw_energy)) < mp.mpf('1e-60')
    assert abs(mp.im(raw_response)) < mp.mpf('1e-60')
    E = mp.re(raw_energy)
    R = mp.re(raw_response)/E
    reconstruction_error = max(abs(E-1), abs(R-vals[n-1]))
    assert reconstruction_error < mp.mpf('1e-60')
    eigen_residual = mp.norm(D*c-R*K*c)/(mp.norm(D)*mp.norm(c)+abs(R)*mp.norm(K)*mp.norm(c))
    result = dict(max_slope=R, min_slope=vals[0], energy=E,
                  gram_min_eigenvalue=ev[0], gram_max_eigenvalue=ev[n-1],
                  condition=condition, log10_condition=mp.log10(condition),
                  hermitian_error=hermitian_error,
                  whitened_hermitian_error=whitened_hermitian_error,
                  whitened_eigen_residual=whitened_residual,
                  eigen_residual=eigen_residual,
                  reconstruction_error=reconstruction_error)
    assert max(whitened_residual, eigen_residual) < mp.mpf('1e-60')
    return result, c


def decimal(x):
    return mp.nstr(x, mp.mp.dps)


def pack(M):
    return dict(real=[[decimal(mp.re(M[i, j])) for j in range(M.cols)] for i in range(M.rows)],
                imag=[[decimal(mp.im(M[i, j])) for j in range(M.cols)] for i in range(M.rows)])


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validation():
    """Compare against old double precision and fresh arbitrary-precision derivatives."""
    import numpy as np
    from joint_neutral_hermite_response_probe import matrices as old_matrices
    eps = h = mp.mpf(1)
    s = mp.mpf(0)
    alpha, beta = mp.mpf('0.5'), mp.mpf(1)/64
    widths = list(map(mp.mpf, [1, 2, 10]))
    K, D = matrices(alpha, beta, widths, 4, eps, h, s)
    oldK, oldD = old_matrices(float(alpha), float(beta), [1., 2., 10.], 4, 1., 1., 0.)
    errors = []
    for M, old in [(K, oldK), (D, oldD)]:
        fresh = np.asarray([[complex(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])
        error = float(np.linalg.norm(fresh-old)/np.linalg.norm(fresh))
        assert error < 1e-12
        errors.append(error)
    checks = []
    for i, j, m, n in [(0, 0, 0, 0), (0, 1, 1, 3), (1, 2, 4, 4), (2, 0, 3, 1)]:
        def entry(t):
            r, rp = geometry(eps, h, t)
            return pair(alpha, beta, widths[i], widths[j], 4, r, rp)[0][m, n]
        exact = mp.diff(entry, s)
        stored = D[i*5+m, j*5+n]
        error = abs(exact-stored)/max(1, abs(exact))
        assert error < mp.mpf('1e-105')
        checks.append(dict(width_i=i, width_j=j, degree_i=m, degree_j=n,
                           derivative_relative_error=decimal(error)))
    # Evaluate reverse pairs independently; the scan fills lower blocks by symmetry.
    r, rp = geometry(eps, h, s)
    left = pair(alpha, beta, widths[0], widths[2], 4, r, rp)
    right = pair(alpha, beta, widths[2], widths[0], 4, r, rp)
    symmetry = [mp.norm(a-b.H)/mp.norm(a) for a, b in zip(left, right)]
    assert max(symmetry) < mp.mpf('1e-105')
    return dict(old_separated_width_relative_errors=errors, clock_derivative_checks=checks,
                independently_computed_pair_symmetry_errors=list(map(decimal, symmetry)))


def cases():
    result = []
    for degree in [0, 2, 4, 8]:
        result.append((degree, 1, '0.01'))
        for count in [3, 5, 7]:
            for spacing in ['0.1', '0.01', '0.001']:
                result.append((degree, count, spacing))
    result += [(2, 15, '0.01'), (4, 11, '0.01'), (8, 9, '0.01'), (8, 11, '0.01')]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    assert digest(root/PARENT) == PARENT_SHA
    parent = json.loads((root/PARENT).read_text())
    assert all(digest(root/p) == sha for p, sha in parent['source_sha256'].items())
    assert digest(root/'UnifiedTheory.lean') == parent['root_check']['source_sha256']
    mp.mp.dps = 120
    checks = validation()
    h = eps = mp.mpf(100)
    alpha, beta = 1/(2*h), 1/(64*h)
    s = mp.log(eps)+1
    records, witnesses = [], {}
    for degree, count, spacing in cases():
        widths = [1+mp.mpf(spacing)*i for i in range(count)]
        K, D = matrices(alpha, beta, widths, degree, eps, h, s)
        result, c = spectral(K, D)
        result['normalized_max_slope'] = eps/(mp.exp(s)+eps)*result['max_slope']
        meta = dict(h=decimal(h), epsilon=decimal(eps), alpha=decimal(alpha), beta=decimal(beta),
                    s=decimal(s), clock_offset='1', width_count=count, max_degree=degree,
                    width_spacing=spacing, dimension=count*(degree+1))
        values = {key:decimal(value) for key, value in result.items()}
        record = dict(parameters=meta, result=values)
        records.append(record)
        roles = []
        if 'largest_observed' not in witnesses or result['max_slope'] > mp.mpf(witnesses['largest_observed']['result']['max_slope']):
            roles.append('largest_observed')
        if spacing == '0.001' and ('closest_widths' not in witnesses or result['max_slope'] > mp.mpf(witnesses['closest_widths']['result']['max_slope'])):
            roles.append('closest_widths')
        if roles:
            witness = dict(parameters=meta, result=values, widths=list(map(decimal, widths)),
                           coefficients=pack(c), gram=pack(K), derivative=pack(D))
            for role in roles:
                witnesses[role] = witness
        print(degree, count, spacing, 'slope', mp.nstr(result['max_slope'], 18),
              'log10(condition)', mp.nstr(result['log10_condition'], 9), flush=True)
    sources = ['scripts/joint_neutral_clustered_response_probe.py',
               'scripts/verify_joint_neutral_clustered_response.py',
               'scripts/joint_neutral_hermite_response_probe.py',
               'scripts/joint_neutral_coherent_response_probe.py',
               'scripts/matter_energy_gram_probe.py',
               'UnifiedTheory/Audit/KFCausalReciprocalNeutralKernel.lean',
               'UnifiedTheory/Audit/KFCausalReciprocalCrossGeometry.lean',
               'UnifiedTheory/Audit/KFCausalReciprocalNeutralWholeClock.lean']
    report = dict(scope=__doc__, parent_report=dict(path=PARENT, sha256=PARENT_SHA),
                  root_sha256=parent['root_check']['source_sha256'],
                  source_sha256={p:digest(root/p) for p in sources},
                  mpmath_version=mp.__version__, precision=120, rank_truncation=False,
                  minimum_precision_margin_digits=65, neutral_sources_zero=True,
                  basis='He_n(2*sqrt(beta)*z)/sqrt(n!), width-major then degree',
                  validation=checks, test_count=len(records), rejected_cases=0,
                  records=records, witnesses=witnesses,
                  conclusion='Finite clustered-width evidence only. A larger positive transverse logarithmic derivative is not an unbounded sequence, a violation of an unspecified uniform constant, or a counterexample to the full-clock or full-Hamiltonian response estimate. No continuous confluent-width limit or arbitrary-degree statement is certified.')
    assert all(digest(root/p) == sha for p, sha in parent['source_sha256'].items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256']
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print('Completed', len(records), 'full-matrix cases; no modes discarded.', flush=True)


def matrices(alpha,beta,widths,degree,eps,h,s,b=0):
    r,rp=geometry(eps,h,s)
    size=degree+1
    K,D=mp.matrix(len(widths)*size),mp.matrix(len(widths)*size)
    for i,wi in enumerate(widths):
        for j in range(i,len(widths)):
            block,slope=pair(alpha,beta,wi,widths[j],degree,r,rp,b)
            for m in range(size):
                for n in range(size):
                    K[i*size+m,j*size+n]=block[m,n]
                    D[i*size+m,j*size+n]=slope[m,n]
                    if i!=j:
                        K[j*size+n,i*size+m]=mp.conj(block[m,n])
                        D[j*size+n,i*size+m]=mp.conj(slope[m,n])
    return K,D



if __name__ == '__main__':
    main()
