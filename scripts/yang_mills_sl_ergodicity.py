"""Is a single heat-bath chain of the twisted SU(2) measure ergodic for the Polyakov-loop observables? (GPU numerics)
Motivation (README, smeared Polyakov loops): on the localization path at beta 4, N 8, the measured E Var_{mu_t} F exceeds
the single-chain Var_mu F at t = 1 (x1.45 neutral, x12.8 center charged), which exact sampling forbids (Nishimori:
E_y Var_{mu_t} F <= Var_mu F). So the single chain under-samples. Here: C chains, half started center-flipped
(U_0 -> -U_0 on the slice x_0 = 0, which flips L_0), each run for `sweeps` sweeps; per chain, time series of the
smeared loop means m1_d = mean_x (1/2)tr L_d (charged) and m2 = mean (1/2 tr L)^2 (neutral), d = 0, 3.
Reports per-chain means/variances, between-chain spread, the number of sign changes of m1 (tunnelling), and the pooled
variance of the 80 observables against the single-chain one.
Written before the run: m1 is stuck at its starting sign in every chain (no tunnelling in 20000 sweeps); pooled
charged variance >> single-chain; neutral pooled/single within 1.5.
Usage: out N beta_std chains sweeps record_every
"""
import sys, json, math, time, torch
sys.path.insert(0, __file__.rsplit('/',1)[0])
import yang_mills_sl_gpu as G
dev=G.dev; DT=G.DT
G.CJ=torch.tensor([1.,-1,-1,-1],device=dev,dtype=DT)
out=sys.argv[1]; N=int(sys.argv[2]); b=float(sys.argv[3]); C=int(sys.argv[4]); SW=int(sys.argv[5]); RE=int(sys.argv[6])
beta=b/2; z=G.twist(N); xs=torch.stack(torch.meshgrid(*[torch.arange(N,device=dev)]*4,indexing='ij')); par=xs.sum(0)%2
phis=[(torch.cos(2*math.pi*xs[d].to(DT)/N),torch.sin(2*math.pi*xs[d].to(DT)/N)) for d in range(4)]
res=[]; allF=[]
for c in range(C):
    torch.manual_seed(100+c); t0=time.time()
    U=torch.zeros((4,)+(N,)*4+(4,),device=dev,dtype=DT); U[...,0]=1
    U[1][xs[1]==0]=torch.tensor([0.,1,0,0],device=dev); U[2][xs[2]==0]=torch.tensor([0.,0,1,0],device=dev)
    if c%2: U[0][xs[0]==0]*=-1
    if c%4>=2: U[3][xs[3]==0]*=-1
    for _ in range(400): G.sweep(U,z,beta,None,par)
    ts=[];F=[]
    for s in range(SW//RE):
        for _ in range(RE): G.sweep(U,z,beta,None,par)
        Us=G.smear(U,z,*G.SMEAR); row=[]
        for d in (0,3):
            l=G.polyakov(Us,d); row+=[float(l.mean()),float((l*l).mean())]
        ts.append(row); F.append(G.observables(U,z,phis))
    ts=torch.tensor(ts); F=torch.stack(F); allF.append(F)
    sgn=lambda v: int(((v[1:]*v[:-1])<0).sum())
    r=dict(chain=c,flip0=bool(c%2),flip3=bool(c%4>=2),m1_0=float(ts[:,0].mean()),m1_3=float(ts[:,2].mean()),
           m2_0=float(ts[:,1].mean()),m2_3=float(ts[:,3].mean()),sign_changes_0=sgn(ts[:,0]),sign_changes_3=sgn(ts[:,2]),
           var={g:float(F.var(0)[sl].mean()) for g,sl in G.GROUPS.items()},sec=round(time.time()-t0,1))
    res.append(r); print(json.dumps(r),flush=True)
P=torch.cat(allF); pooled={g:float(P.var(0)[sl].mean()) for g,sl in G.GROUPS.items()}
single={g:sum(r['var'][g] for r in res)/C for g in G.GROUPS}
summ=dict(kind='summary',N=N,bstd=b,chains=C,sweeps=SW,pooled=pooled,mean_single=single,ratio={g:pooled[g]/single[g] for g in pooled})
res.append(summ); print(json.dumps(summ),flush=True); json.dump(res,open(out,'w'))
