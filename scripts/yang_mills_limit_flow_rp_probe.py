"""Does the flowed neutral two-point function violate the two-point minor of reflection positivity? (numerics, not a proof)

Reflection positivity across the site plane t = 0 with translation invariance makes K(s + s') positive semidefinite
on nonnegative times, hence K(0) + K(2) - 2 K(1) >= 0. TwistedLimit.reflected_form proves this for the bare spatial
plaquette sum on one time slice, which is half-supported. A flowed observable is not half-supported, and
TwistedLimit.chain_minor_negative and chain_physical_times prove the opposite sign in the free flowed chain, which is a
free model and not this law. This script measures the actual twisted law: O_s(tau) = sum over x of z Re P_ij(tau, x), i<j
spatial, after Wilson flow to time s, with kernel exp(s Delta) on the linear part, which is the t of TwistedLimit.chain and
twice the time of TwistedFlow.wf.

Mode 'slice' flows each time slice in three dimensions only, which is half-supported, so TwistedLimit.static_upper already
forces K(0) + K(2) - 2 K(1) >= 0 for it. A positive slice result is therefore a check of the code and not a test of anything;
it is also dominated by K(0).
Mode 'polyakov' ignores the flow times and measures the winding loop in direction 3, r = Re W_3 (half the trace), the
observable of TwistedLimit.polyakov_os_tendsto: E[r] = 0 exactly at every size and coupling, and G(tau) = E[r(t,x,y) r(t+tau,x,y)].
The cold start lies in one flip sector and heatbath may not tunnel at large beta, so the sample mean of r is not its true
mean, which is zero; G is flip-even and does not need tunneling, and that is what is reported as the connected function.
Usage: out N:n_meas,N:n_meas beta_stds flow_times n_therm [full|slice|polyakov]. One heatbath plus three overrelaxation sweeps
between measurements, times two. Euler flow with step 0.02. Jackknife errors over 20 contiguous Monte Carlo blocks, which may
understate autocorrelation; with n_meas configurations each block holds n_meas/20. Also records the exact free-chain thresholds.
"""
import os, sys
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import json, math, numpy as np
from yang_mills_twisted_step_scaling import qmul,qc,S as sh,twist,zz,heat,over,staple

def qexp(v):
    r=np.linalg.norm(v,axis=-1,keepdims=True)
    return np.concatenate([np.cos(r),np.sinc(r/np.pi)*v],-1)

def flow_step(U,z,eps):
    new=np.empty_like(U)
    for m in range(4):
        A=qmul(U[m],staple(U,z,m))
        new[m]=qmul(qexp(-eps*A[...,1:]),U[m])
    return new/np.linalg.norm(new,axis=-1,keepdims=True)

def spatial_staple(U,z,m):
    tot=0.
    for n in (1,2,3):
        if n==m: continue
        s=zz(z,m,n)
        up=qmul(qmul(sh(U[n],m),qc(sh(U[m],n))),qc(U[n]))
        bk=qmul(qmul(qc(sh(U[n],m)),qc(U[m])),U[n])
        if not np.isscalar(s):
            up=up*s[...,None]; bk=bk*s[...,None]
        tot=tot+up+sh(bk,n,-1)
    return tot

def slice_flow_step(U,z,eps):
    """The Wilson flow of the static lift of each time slice is this three-dimensional flow, since a static field has
    no force on temporal links and no temporal contribution to the force on spatial links (hand computation)."""
    new=U.copy()
    for m in (1,2,3):
        A=qmul(U[m],spatial_staple(U,z,m))
        new[m]=qmul(qexp(-eps*A[...,1:]),U[m])
    return new/np.linalg.norm(new,axis=-1,keepdims=True)

def slices(U,z):
    tot=0.
    for m in (1,2,3):
        for n in range(m+1,4):
            P=qmul(qmul(qmul(U[m],sh(U[n],m)),qc(sh(U[m],n))),qc(U[n]))
            tot=tot+(zz(z,m,n)*P[...,0])
    return tot.sum(axis=(1,2,3))

def correlator(O):
    """Connected K(tau) from an array of shape (configs, T), averaged over the base slice."""
    T=O.shape[1]; d=O-O.mean()
    return np.array([(d*np.roll(d,-t,axis=1)).mean() for t in range(T//2+1)])

def chain_table():
    out=[]
    for n,k in [(4,1.),(4,.25),(8,.1),(16,.04),(32,.01),(64,.0025)]:
        E=math.pi/n; mu=2-2*math.cos(E); th=.5*math.log(8*n*(k+1)/(k*mu*math.cos(E)))
        def c(t,tau):
            return sum(math.cos(math.pi*j/n*tau)*math.exp(-2*t*(2-2*math.cos(math.pi*j/n)))/(k+2-2*math.cos(math.pi*j/n)) for j in range(2*n))/(2*n)
        def d(t): return c(t,0)+c(t,2)-2*c(t,1)
        # the actual sign change, scanned, against the proved sufficient threshold
        ts=[.01*1.2**i for i in range(60)]
        sign=next((t for t in ts if d(t)<0),None)
        out.append(dict(n=n,kappa=k,proved_threshold_t=th,scanned_first_negative_t=sign,d_at_0=d(0.),d_at_threshold=d(th)))
    return out

def chain_minor_scan():
    """Exact evaluation of the minor c(2a) + c(2b) - 2c(a+b) at b = 2a and t = c (2n)^2, for the statement TwistedLimit.chain_physical_times. Not a proof."""
    out=[]
    for c0 in (.005,.01,.02,.05):
        for n,k in [(16,1/16**2),(32,1/32**2),(64,1/64**2),(64,1.)]:
            t=c0*(2*n)**2
            def cc(tau):
                return sum(math.cos(math.pi*j/n*tau)*math.exp(-2*t*(2-2*math.cos(math.pi*j/n)))/(k+2-2*math.cos(math.pi*j/n)) for j in range(2*n))/(2*n)
            neg=[a for a in range(1,n//3+1) if cc(2*a)+cc(4*a)-2*cc(3*a)<0]
            first=next((a for a in range(1,n//3+1) if a not in neg),None)
            out.append(dict(c=c0,n=n,kappa=k,largest_a_with_all_smaller_negative=(first-1 if first else n//3),physical_q_at_that_a=((first-1 if first else n//3)/(2*n))))
    return out

def polyakov(U):
    W=U[3][:,:,:,0]
    for z in range(1,U.shape[4]):
        W=qmul(W,U[3][:,:,:,z])
    return W[...,0]

def polyakov_main(out,pairs,bs,nth):
    res=json.load(open(out)) if os.path.exists(out) else dict(kind='numerics, not a proof',chain=chain_table(),runs=[])
    res.setdefault('polyakov',[])
    for N,nm,b in [(int(a),int(c),b) for a,c in pairs for b in bs]:
        beta=b/2; rng=np.random.default_rng(int(b*100)+N+7); z=twist(N); par=np.indices((N,)*4).sum(0)%2
        U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
        U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
        for _ in range(nth):
            heat(U,z,beta,rng,par); over(U,z,par); over(U,z,par); over(U,z,par)
        rs=[]
        for c in range(nm):
            for _ in range(2):
                heat(U,z,beta,rng,par); over(U,z,par); over(U,z,par); over(U,z,par)
            rs.append(polyakov(U))
        rs=np.array(rs); nb=20; m=len(rs)//nb; rs=rs[:m*nb]
        def corr(a,mu):
            return np.array([(a*np.roll(a,-t,axis=mu)).mean() for t in range(N//2+1)])
        G_t=corr(rs,1); G_x=corr(rs,2)
        jk=np.array([corr(np.concatenate([rs[:i*m],rs[(i+1)*m:]]),1) for i in range(nb)])
        G_err=np.sqrt((nb-1)*((jk-jk.mean(0))**2).sum(0)/nb)
        r=dict(N=N,beta_std=b,n=int(len(rs)),sample_mean_r=float(rs.mean()),sector_mean_abs=float(np.abs(rs.mean(axis=(1,2,3))).mean()),
               G_time=G_t.tolist(),G_time_err=G_err.tolist(),G_space=G_x.tolist(),mean_r2=float((rs**2).mean()),mean_r4=float((rs**4).mean()),
               neutral_connected_time=[float(((rs**2)*np.roll(rs**2,-t,axis=1)).mean()-(rs**2).mean()**2) for t in range(N//2+1)])
        res['polyakov'].append(r); print(json.dumps(r),flush=True)
        json.dump(res,open(out,'w'),indent=1)

def main():
    if len(sys.argv)>6 and sys.argv[6]=='chainscan':
        res=json.load(open(sys.argv[1])); res['chain_minor_scan']=chain_minor_scan(); json.dump(res,open(sys.argv[1],'w'),indent=1); print(json.dumps(res['chain_minor_scan'])); return
    if len(sys.argv)>6 and sys.argv[6]=='polyakov':
        return polyakov_main(sys.argv[1],[x.split(':') for x in sys.argv[2].split(',')],[float(x) for x in sys.argv[3].split(',')],int(sys.argv[5]))
    out=sys.argv[1]; pairs=[x.split(':') for x in sys.argv[2].split(',')]; bs=[float(x) for x in sys.argv[3].split(',')]
    flows=[float(x) for x in sys.argv[4].split(',')]; nth=int(sys.argv[5])
    mode=sys.argv[6] if len(sys.argv)>6 else 'full'
    step=slice_flow_step if mode=='slice' else flow_step
    res=json.load(open(out)) if os.path.exists(out) else dict(kind='numerics, not a proof',chain=chain_table(),runs=[])
    print(json.dumps(res['chain']),flush=True)
    for N,nm,b in [(int(a),int(c),b) for a,c in pairs for b in bs]:
        beta=b/2; rng=np.random.default_rng(int(b*100)+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
        U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
        U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
        for _ in range(nth):
            heat(U,z,beta,rng,par); over(U,z,par); over(U,z,par); over(U,z,par)
        rec={s:[] for s in flows}
        for c in range(nm):
            for _ in range(2):
                heat(U,z,beta,rng,par); over(U,z,par); over(U,z,par); over(U,z,par)
            V=U.copy(); cur=0.
            for s in flows:
                while cur<s-1e-9:
                    V=step(V,z,0.02); cur+=0.02
                rec[s].append(slices(V,z))
        for s in flows:
            O=np.array(rec[s]); nb=20; m=len(O)//nb; O=O[:m*nb]
            K=correlator(O)
            jk=[]
            for i in range(nb):
                keep=np.concatenate([O[:i*m],O[(i+1)*m:]])
                jk.append(correlator(keep))
            jk=np.array(jk); err=np.sqrt((nb-1)*((jk-jk.mean(0))**2).sum(0)/nb)
            D=lambda K:K[0]+K[2]-2*K[1]
            dj=np.array([D(x) for x in jk]); derr=float(np.sqrt((nb-1)*((dj-dj.mean())**2).sum()/nb))
            r=dict(mode=mode,N=N,beta_std=b,flow_s=s,K=K.tolist(),K_err=err.tolist(),second_diff_at_1=float(D(K)),second_diff_err=derr,
                   z=float(D(K)/derr) if derr>0 else None,n=int(len(O)))
            res['runs'].append(r); print(json.dumps(r),flush=True)
        json.dump(res,open(out,'w'),indent=1)
main()
