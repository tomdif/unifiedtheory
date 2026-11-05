"""Is stochastic localization sharp for twisted 4D SU(2) lattice YM once the long-wavelength window opens? (GPU numerics)

Background (README, "Self-consistency bound"). In the Gaussian picture the lowest-momentum field strength F_k forces
C_P >= ~ n^2/(4 pi^2 beta), and the localization learns that mode for t in [beta k_min^2, 1], a window that is empty
at n <= 8 and opens for n > 2 pi sqrt(beta). By the localization identity d/dt E Var_{mu_t} f = -E |Cov_{mu_t}(f,U)|^2
and Cauchy-Schwarz, the required covariance satisfies  int_0^T alpha_t dt >= log( Var_mu f / E Var_{mu_T} f ).
Measured, for each (n, beta):
- R = Var_mu F / E_mu |grad F|^2 for the gauge-invariant observables F = sum_x cos/sin(2 pi x_d / n) (1/2) tr P_{mn}(x),
  d not in {m,n} (24 observables): a direct lower bound on the Poincare constant of mu (link gradient).
- V(t) = E_y Var_{mu_t} F on a log grid of t (Nishimori start at U*, independent chains per y).
- alpha_struct(t): out-of-sample top variance in a 216-dim span of low-momentum tangent directions at U*
  (right frame U* e_a phi(x) and left frame e_a U* phi(x); phi in {1, cos, sin of lowest k}), two chains.
Written before any run: (1) R grows like n^2 at fixed beta once n > 2 pi sqrt(beta) (beta = 2.5: factor >= 4 from
n = 8 to 24). (2) log(V(0)/V(T)) grows like 2 log n. (3) alpha_struct stays O(1) at every t, so the required
int alpha is carried by directions outside the structured span (the estimator, not the theorem, is what misses them).
Added 2026-11-04 after the beta = 2.5 run: Re P is ~ 1 - |F|^2/2, a composite whose variance is UV-dominated, so the
plaquette modes cannot see a slow mode (R fell from 0.043 at beta 2.5 to 0.020 at beta 4, N = 8). Added Polyakov-loop
observables along the untwisted directions 0, 3 with weights 1, cos/sin(2 pi x_e/N): poly2 = ((1/2)tr L)^2 (center
neutral, the target sector) and poly1 = (1/2)tr L (center charged: electric flux / tunnelling, outside the target).
Written before this run: if a slow neutral mode exists at beta 4, R_poly2 grows >= 2x from N = 8 to 24.
Usage: out ns betas ts n_y S [stride]
"""
import os, sys, json, math, time
import torch
dev='cuda' if torch.cuda.is_available() else 'cpu'; DT=torch.float32
torch.backends.cuda.matmul.allow_tf32=False
def qmul(a,b):
    w1,x1,y1,z1=a.unbind(-1); w2,x2,y2,z2=b.unbind(-1)
    return torch.stack([w1*w2-x1*x2-y1*y2-z1*z2,w1*x2+x1*w2+y1*z2-z1*y2,w1*y2-x1*z2+y1*w2+z1*x2,w1*z2+x1*y2-y1*x2+z1*w2],-1)
CJ=None
def qc(a): return a*CJ
def S(f,m,k=1): return torch.roll(f,-k,dims=m)
def twist(N):
    z=torch.ones((N,)*4,device=dev,dtype=DT); z[:,0,0,:]=-1; return z
def staple(U,z,m):
    tot=0.
    for n in range(4):
        if n==m: continue
        up=qmul(qmul(S(U[n],m),qc(S(U[m],n))),qc(U[n]))
        bk=qmul(qmul(qc(S(U[n],m)),qc(U[m])),U[n])
        if {m,n}=={1,2}: up=up*z[...,None]; bk=bk*z[...,None]
        tot=tot+up+S(bk,n,-1)
    return tot
def kp(k):
    out=torch.empty_like(k); todo=torch.ones_like(k,dtype=torch.bool); it=0
    while bool(todo.any()):
        idx=todo.nonzero(as_tuple=True); ks=k[idx].double(); n=ks.numel()
        r=torch.rand((4,n),device=dev,dtype=torch.float64)
        lam2=-(torch.log1p(-r[0])+torch.cos(2*math.pi*r[1])**2*torch.log1p(-r[2]))/(2*ks)
        ok=r[3]**2<=1-lam2
        sel=tuple(i[ok] for i in idx); out[sel]=(1-2*lam2[ok]).to(DT); todo[sel]=False; it+=1
        if it>2000: raise RuntimeError('kp stuck')
    return out
def update(U,z,beta,y,par,heat):
    for m in range(4):
        for p in (0,1):
            K=2*beta*qc(staple(U,z,m))
            if y is not None: K=K+y[m]
            nrm=K.norm(dim=-1); mask=(par==p)&(nrm>1e-12); Kd=K[mask]/nrm[mask][:,None]
            if heat:
                a0=kp(nrm[mask]); v=torch.randn((a0.numel(),3),device=dev,dtype=DT); v=v/v.norm(dim=-1,keepdim=True)
                q=torch.cat([a0[:,None],torch.sqrt(torch.clamp(1-a0**2,min=0))[:,None]*v],-1)
                new=qmul(q,Kd)
            else:
                new=qmul(qmul(Kd,qc(U[m][mask])),Kd)
            U[m][mask]=new/new.norm(dim=-1,keepdim=True)
def sweep(U,z,beta,y,par):
    update(U,z,beta,y,par,True); update(U,z,beta,y,par,False); update(U,z,beta,y,par,False)
def gauge_random(U):
    g=torch.randn(U.shape[1:],device=dev,dtype=DT); g=g/g.norm(dim=-1,keepdim=True)
    for m in range(4): U[m]=qmul(qmul(g,U[m]),qc(S(g,m)))
def plaq_re(U,z):
    out={}
    for m in range(4):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],S(U[n],m)),qc(S(U[m],n))),qc(U[n]))[...,0]
            out[(m,n)]=P*z if {m,n}=={1,2} else P
    return out
GROUPS={'plaq':slice(0,24),'poly2':slice(24,38),'poly1':slice(38,52)}
def polyakov(U,d):
    """(1/2) tr of the Polyakov loop along untwisted direction d, as a field on the slice x_d = 0 (kept N^4 by broadcasting)."""
    L=U[d]
    for k in range(1,U.shape[1]): L=qmul(L,S(U[d],d,k))
    return L[...,0].select(d,0)
def observables(U,z,phis):
    pl=plaq_re(U,z); vals=[]
    for (m,n),P in pl.items():
        for d in range(4):
            if d in (m,n): continue
            vals.append((P*phis[d][0]).sum()); vals.append((P*phis[d][1]).sum())
    p1=[];p2=[]
    for d in (0,3):                                   # twist is in plane {1,2}: loops along 0 and 3 are gauge invariant
        l=polyakov(U,d); ws=[torch.ones_like(l)]
        for e in range(4):
            if e!=d: ws+=[phis[e][0].select(d,0),phis[e][1].select(d,0)]
        for w in ws: p2.append((w*l*l).sum()); p1.append((w*l).sum())
    return torch.stack(vals+p2+p1)
def grad_norm2(U,z,phis):
    Ug=U.clone().requires_grad_(True); F=observables(Ug,z,phis); out=[]
    for i in range(F.numel()):
        g,=torch.autograd.grad(F[i],Ug,retain_graph=True)
        gt=g-(g*U).sum(-1,keepdim=True)*U; out.append((gt**2).sum())
    return torch.stack(out).detach()
def struct_basis(Us,N):
    x=torch.stack(torch.meshgrid(*[torch.arange(N,device=dev,dtype=DT)]*4,indexing='ij'))
    fs=[torch.ones((N,)*4,device=dev,dtype=DT)]
    for d in range(4): fs+= [torch.cos(2*math.pi*x[d]/N),torch.sin(2*math.pi*x[d]/N)]
    B=[]
    for m in range(4):
        for a in range(1,4):
            e=torch.zeros(4,device=dev,dtype=DT); e[a]=1
            R=qmul(Us[m],e.expand_as(Us[m])); L=qmul(e.expand_as(Us[m]),Us[m])
            for f in fs:
                for T in (R,L):
                    v=torch.zeros_like(Us); v[m]=T*f[...,None]; B.append(v.flatten())
    B=torch.stack(B,1); Q,_=torch.linalg.qr(B); return Q
def main():
    global CJ
    CJ=torch.tensor([1.,-1,-1,-1],device=dev,dtype=DT)
    out=sys.argv[1]; ns=[int(v) for v in sys.argv[2].split(',')]; bs=[float(v) for v in sys.argv[3].split(',')]
    ts=[float(v) for v in sys.argv[4].split(',')]; ny=int(sys.argv[5]); Ssamp=int(sys.argv[6])
    stride=int(sys.argv[7]) if len(sys.argv)>7 else 2; res=[]
    torch.manual_seed(0)
    for N in ns:
        z=twist(N); xs=torch.stack(torch.meshgrid(*[torch.arange(N,device=dev)]*4,indexing='ij'))
        par=(xs.sum(0)%2); phis=[(torch.cos(2*math.pi*xs[d].to(DT)/N),torch.sin(2*math.pi*xs[d].to(DT)/N)) for d in range(4)]
        for b in bs:
            beta=b/2; t0=time.time()
            U=torch.zeros((4,)+(N,)*4+(4,),device=dev,dtype=DT); U[...,0]=1
            U[1][xs[1]==0]=torch.tensor([0.,1,0,0],device=dev); U[2][xs[2]==0]=torch.tensor([0.,0,1,0],device=dev)
            for _ in range(400): sweep(U,z,beta,None,par)
            # mu itself: Var F, E|grad F|^2, plaquette
            Fs=[];G=[];pm=[]
            for s_ in range(Ssamp):
                for _ in range(stride): sweep(U,z,beta,None,par)
                Fs.append(observables(U,z,phis)); pm.append(torch.stack(list(plaq_re(U,z).values())).mean())
                if s_%10==0: G.append(grad_norm2(U,z,phis))
            Fs=torch.stack(Fs); varF=Fs.var(0); G=torch.stack(G).mean(0)
            # autocorrelation proxy: variance of block means (blocks of 50)
            nb=Ssamp//50; bm=Fs[:nb*50].reshape(nb,50,-1).mean(1); tau=(bm.var(0)*50/varF).mean()
            row=dict(N=N,bstd=b,kind='mu',plaq=float(torch.stack(pm).mean()),varF=float(varF[GROUPS['plaq']].mean()),
                     grad2=float(G[GROUPS['plaq']].mean()),R=float((varF/G)[GROUPS['plaq']].mean()),
                     **{f'R_{g}':float((varF/G)[sl].mean()) for g,sl in GROUPS.items() if g!='plaq'},
                     **{f'tau_{g}':float((bm.var(0)*50/varF)[sl].mean()) for g,sl in GROUPS.items()},R_gauss_pred=N**2/(4*math.pi**2*b),tau_int_proxy=float(tau),sec=round(time.time()-t0,1))
            res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
            V0={g:float(varF[sl].mean()) for g,sl in GROUPS.items()}
            # localization path
            for iy in range(ny):
                Us=U.clone(); 
                for _ in range(20*stride): sweep(Us,z,beta,None,par)
                gauge_random(Us); Q=struct_basis(Us,N); xi=torch.randn_like(Us)
                for t in ts:
                    y=t*Us+math.sqrt(t)*xi
                    P=[];Fv=[]
                    for ch in range(2):
                        W=Us.clone(); PA=[];FA=[]
                        for _ in range(10): sweep(W,z,beta,y,par)
                        for s_ in range(Ssamp):
                            for _ in range(stride): sweep(W,z,beta,y,par)
                            PA.append(W.flatten()@Q); FA.append(observables(W,z,phis))
                        P.append(torch.stack(PA)); Fv.append(torch.stack(FA))
                    A=P[0]-P[0].mean(0); Bm=P[1]-P[1].mean(0)
                    C=A.T@A/(len(A)-1); w,E=torch.linalg.eigh(C.double()); v=E[:,-1].to(DT)
                    a_oos=float(((Bm@v)**2).sum()/(len(Bm)-1))
                    vv=0.5*(Fv[0].var(0)+Fv[1].var(0)); vF=float(vv[GROUPS['plaq']].mean())
                    row=dict(N=N,bstd=b,kind='path',iy=iy,t=t,V=vF,V_over_V0=vF/V0['plaq'],
                             **{f'V_over_V0_{g}':float(vv[sl].mean())/V0[g] for g,sl in GROUPS.items() if g!='plaq'},alpha_struct_oos=a_oos,
                             alpha_struct_in=float(w[-1]),sec=round(time.time()-t0,1))
                    res.append(row); print(json.dumps(row),flush=True); json.dump(res,open(out,'w'))
if __name__=='__main__': main()
