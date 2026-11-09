"""Lowest neutral energies from a 3x3 GEVP of the Polyakov observables (numerics, not a proof).

Reanalysis of stored runs of yang_mills_slow_polyakov.py: the three neutral observables sum P_m^2 (m = 1, 2, 3) are
measured on the same configurations, so C_ab(t) = <A_a(t0+t) A_b(t0)>_c is a 3x3 correlator matrix. The generalized
eigenvalue problem C(t) v = lambda C(t_r) v (t_r = 1) gives effective energies E_k(t) = -log(lambda_k(t+1)/lambda_k(t));
n E_0 at the largest usable t estimates n times the lowest neutral gap that these observables see. Free twisted field:
n * 2 omega_min, with 2 cosh omega - 2 = 4 sin^2(pi/(2n)), the value the upper half of NeutralWindow must bound below.
Written before any run: n E_0 lies within 25% of the free value at every beta_std >= 8 and n = 6, 8, and drops below
it at beta_std = 3-4 (strong coupling: the gap in units of 1/L is not protected there).
Usage: out data_files...
"""
import sys, json, numpy as np, scipy.linalg as sl
out=sys.argv[1]; res=[]
def corr(X):           # X: cfgs x 3 x Lt
    Y=X-X.mean((0,2),keepdims=True); Lt=X.shape[2]
    return np.array([np.einsum('cat,cbt->ab',np.roll(Y,-s,2),Y)/(Y.shape[0]*Lt) for s in range(Lt//2+1)])
def energies(C,tr=1):
    Cs=(C+np.transpose(C,(0,2,1)))/2; L=[]
    for t in range(tr+1,len(C)):
        try: w=np.sort(sl.eigh(Cs[t],Cs[tr],eigvals_only=True))[::-1]
        except Exception: w=np.full(3,np.nan)
        L.append(w)
    L=np.array(L); E=-np.log(np.clip(L[1:]/L[:-1],1e-300,None)); return E   # E[t-(tr+1)] for step t->t+1
for f in sys.argv[2:]:
    for r in json.load(open(f)):
        if 'raw' not in r['P1sq']: continue
        N=r['N']; X=np.stack([np.array(r[k]['raw']) for k in ('P1sq','P2sq','P3sq')],1)
        free=N*2*np.arccosh(1+2*np.sin(np.pi/(2*N))**2)
        E=energies(corr(X)); nc=len(X)
        jk=np.array([energies(corr(np.delete(X,i,0))) for i in range(nc)])
        err=np.sqrt((nc-1)*np.nanmean((jk-jk.mean(0))**2,0))
        rows=[dict(t=int(i+2),nE0=float(N*E[i,0]),err=float(N*err[i,0]),nE1=float(N*E[i,1])) for i in range(len(E))]
        row=dict(file=f.split('/')[-1],N=N,beta_std=r['beta_std'],adm=r.get('adm',0),cfgs=nc,free=free,steps=rows)
        res.append(row)
        print(f.split('/')[-1][22:-5],'N',N,'b',r['beta_std'],'adm',r.get('adm',0),'free',round(free,2),
              ' '.join(f"t{s['t']}:{s['nE0']:.2f}±{s['err']:.2f}" for s in rows[:4]),flush=True)
json.dump(res,open(out,'w'))
