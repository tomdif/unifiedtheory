"""First renormalization step as a block Schur complement (numerics, not a proof).

Same exact inequality as yang_mills_schur_coarse.py, Hess U_eff(y) >= E[S_H(y) | y] with S_H the Schur complement over
the fine variables, but with a real block split. In background-gauge coordinates around the flat twisted vacuum V,
eta_e = Ad(W_x)^{-1} eps_e with W the adjoint parallel transport of V from the block corner (path independent: V is flat
up to center elements, and Ad(-1) = 1). Coarse = eta constant on each block of side 2 (per direction and color), fine =
eta with zero block mean. The fine space is spanned by sparse differences, so H_ff is sparse and factored directly.
H = Hess(beta_std) + K beta_std D_V D_V^T (background-gauge slice), optionally + 2 I (Ricci of SU(2) per link).
Normalized by the same Schur complement at U = V, S_free:
  sig_av = lowest generalized eigenvalue of E[S] against S_free (free field = 1),
  sig_pt = the same for single configurations, mu_f = lowest eigenvalue of H_ff against the free H_ff.
Written before any run: sig_av >= 0.7 and flat from n = 4 to n = 6 at beta_std = 16, 32. sig_av falling with n kills
the averaged one-step route itself, not only the crude split.
Usage: out ns beta_stds n_cfg [ric 0/1]
"""
import os, sys, json
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='1'
sys.path.insert(0, os.path.dirname(__file__))
import numpy as np, scipy.sparse as sp, scipy.linalg as sl
from scipy.sparse.linalg import splu, eigsh
from yang_mills_preconditioned_hessian import hessian, gauge_D, cool, gauge_fix, rot, idx
from yang_mills_twisted_step_scaling import twist, heat, over, qmul, qc

def frames(V,l):
    """Ad(W_x) for every site: transport from the corner of its block, W_{x+nu} = V_{x,nu}^{-1} W_x."""
    N=V.shape[1]; W=np.zeros((N,)*4+(4,)); W[...,0]=1
    for nu in range(4):
        for k in range(1,l):
            sl_to=[slice(None)]*4; sl_from=[slice(None)]*4
            sl_to[nu]=slice(k,N,l); sl_from[nu]=slice(k-1,N,l)
            W[tuple(sl_to)]=qmul(qc(V[nu][tuple(sl_from)]),W[tuple(sl_from)])
    return rot(W)   # (N,N,N,N,3,3)

def split(N,l,R):
    """T (eps = T eta), coarse C (orthonormal block means), fine B (sparse differences) in eta coordinates."""
    I=idx(N); d=4*N**4*3
    # T: block diagonal rotations per link (link (mu,x) uses R_x)
    rows=[];cols=[];vals=[]
    for m in range(4):
        e=I[m].ravel(); Rf=R.reshape(-1,3,3)
        for p in range(3):
            for q in range(3):
                rows.append(3*e+p); cols.append(3*e+q); vals.append(Rf[:,p,q])
    T=sp.csr_matrix((np.concatenate(vals),(np.concatenate(rows),np.concatenate(cols))),shape=(d,d))
    x=np.indices((N,)*4); blk=((x[0]//l)*(N//l)**3+(x[1]//l)*(N//l)**2+(x[2]//l)*(N//l)+x[3]//l).ravel()
    nb=(N//l)**4; L=l**4
    crow=[];ccol=[];brow=[];bcol=[];bval=[]; nc=0; nf=0
    order=np.argsort(blk,kind='stable')
    for m in range(4):
        e=I[m].ravel()
        for b in range(nb):
            links=e[order[b*L:(b+1)*L]]
            for a in range(3):
                crow+= list(3*links+a); ccol+=[nc]*L; nc+=1
                for j in range(1,L):
                    brow+=[3*links[j]+a,3*links[0]+a]; bcol+=[nf,nf]; bval+=[1.,-1.]; nf+=1
    C=sp.csr_matrix((np.full(len(crow),1/np.sqrt(L)),(crow,ccol)),shape=(d,nc))
    B=sp.csr_matrix((bval,(brow,bcol)),shape=(d,nf))
    return T,C,B

def schur(Ht,C,B):
    Hff=(B.T@Ht@B).tocsc(); lu=splu(Hff,permc_spec='COLAMD')
    HC=(Ht@C); Hcc=(C.T@HC).toarray(); Hfc=(B.T@HC).toarray()
    X=lu.solve(Hfc); S=Hcc-Hfc.T@X
    return (S+S.T)/2, Hff

out=sys.argv[1]; ns=[int(x) for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
ncfg=int(sys.argv[4]); ric=len(sys.argv)>5 and sys.argv[5]=='1'; K=float(os.environ.get('KPEN','100')); l=int(os.environ.get('LBLK','2')); res=[]
for N in ns:
    rng=np.random.default_rng(11+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    V=np.zeros((4,)+(N,)*4+(4,)); V[...,0]=1
    for _ in range(100): heat(V,z,30.,rng,par); over(V,z,par)
    cool(V,z,par); D0=gauge_D(V); d=4*N**4*3
    T,C,B=split(N,l,frames(V,l)); G=(K*D0@D0.T).tocsr()
    cov=bool(os.environ.get('COV'))
    def Hfull(U,b):
        H=hessian(U,z,b)+b*G
        if ric: H=H+2*sp.identity(d,format='csr')
        # COV: block frames from the configuration's own transport (covariant block variables), else from V
        Tu=split(N,l,frames(U,l))[0] if cov else T
        return (Tu.T@H@Tu).tocsr()
    for b in bs:
        Sf,Hff0=schur(Hfull(V,b),C,B)
        wS,QS=np.linalg.eigh(Sf); Ninv=QS@np.diag(1/np.sqrt(wS))@QS.T
        print('N',N,'bstd',b,'free Schur eig range',float(wS.min()),float(wS.max()),'coarse dim',Sf.shape[0],flush=True)
        U=V.copy()
        for _ in range(300): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
        Ss=[]; spt=[]; muf=[]
        for c in range(ncfg):
            for _ in range(20): heat(U,z,b/2,rng,par); over(U,z,par); over(U,z,par)
            best=None
            for c0 in (1,-1):
                for c3 in (1,-1):
                    W=U.copy(); W[0][0]*=c0; W[3][:,:,:,0]*=c3; Wg,F=gauge_fix(W,V,par)
                    if best is None or F>best[1]: best=(Wg,F)
            S,Hff=schur(Hfull(best[0],b),C,B)
            # fine convexity relative to the free fine block (generalized, few lowest)
            try:
                w=eigsh(Hff,k=1,M=Hff0,sigma=0,which='LM',return_eigenvectors=False); mu=float(w.min())
            except Exception as ex: mu=float('nan')
            muf.append(mu); Ss.append(S); spt.append(float(np.linalg.eigvalsh(Ninv@S@Ninv)[0]))
            print(json.dumps(dict(N=N,bstd=b,cfg=c,mu_f=mu,sig_pt=spt[-1])),flush=True)
        Sav=np.mean(Ss,0); ev=np.linalg.eigvalsh(Ninv@Sav@Ninv)
        # lambda_min of a finite-sample mean is biased low, more so in higher dimension: record it vs sample count
        run=[float(np.linalg.eigvalsh(Ninv@np.mean(Ss[:k],0)@Ninv)[0]) for k in range(1,len(Ss)+1)]
        # long-wavelength subspace of fixed size (12 lowest free-Schur modes): little finite-sample bias, jackknife error
        Qi=QS[:,:12]@np.diag(1/np.sqrt(wS[:12]))
        def ir(Sm): return float(np.linalg.eigvalsh(Qi.T@Sm@Qi)[0])
        sig_ir=ir(Sav); jk=np.array([ir(np.mean(Ss[:i]+Ss[i+1:],0)) for i in range(len(Ss))])
        sig_ir_err=float(np.sqrt((len(Ss)-1)*((jk-jk.mean())**2).mean()))
        row=dict(N=N,bstd=b,ric=ric,cov=cov,K=K,l=l,coarse_dim=int(Sf.shape[0]),sig_av=float(ev[0]),sig_av_low5=ev[:5].tolist(),
                 sig_pt=spt,mu_f=muf,sig_pt_mean=float(np.mean(spt)),sig_av_running=run,sig_ir=sig_ir,sig_ir_err=sig_ir_err)
        res.append(row); print(json.dumps({k:v for k,v in row.items() if k not in ('sig_pt','mu_f','sig_av_running')}),flush=True)
        json.dump(res,open(out,'w'))
