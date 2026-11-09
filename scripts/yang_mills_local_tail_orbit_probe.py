"""Heatbath check of TwistedLocalTail (numerics, not a proof). Repo beta, beta_std = 2 beta.

Usage: yang_mills_local_tail_orbit_probe.py OUT.json Ns SWEEPS [--refresh] [--thermo]

runs: mean square defect d^2 = 2 - 2 z Re P by plane orientation, with binned errors, the twist-plane mean on the sheet column
against the mean off it, and the temporal-plane mean by time slice, which translation invariance (defect_law) says must agree.
bounds: the proved bounds of the module, evaluated with mass(s) by quadrature of the Haar density and cap(s) = 4 sqrt(pi) s^(3/2),
a hand evaluation of the constant in cap, not from Lean. existing_law_term_mean is the right side of TwistedFlow.law_term_mean;
previous_module_l0p2 is the bound this module proved before the product trial.
--refresh recomputes the derived fields from the runs already in OUT.json, without new sampling.
--thermo adds log_Z_check: log Z per vertex at N=4 by thermodynamic integration, against Zr_lower_trial and Elim.Zon_le.
gaussian_mode_count is the hand count for log Z per vertex at weak coupling, not proved.
"""
import os, sys
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS'): os.environ[v]='2'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import numpy as np, json
from scipy import integrate
from yang_mills_twisted_step_scaling import qmul,qc,S as sh,twist,zz,heat,over

def d2(U,z,m,n):
    P=qmul(qmul(qmul(U[m],sh(U[n],m)),qc(sh(U[m],n))),qc(U[n]))
    return 2-2*zz(z,m,n)*P[...,0]

def mass(s):
    f=lambda u:(2/np.pi)*np.sqrt(max(4-u,0.)/4)*np.sqrt(u)/2*np.exp(-s*u)  # u=|q-1|^2, Haar density in u
    return integrate.quad(f,0,4,limit=800,points=[min(4,1/max(s,1e-9))])[0]
nl=lambda s:-np.log(mass(s))
cap=lambda s:4*np.sqrt(np.pi)*s**1.5
LS=np.linspace(.05,.9,171)

def energy_const(b,n,l):
    return 4.5*np.log(6/l)-1.5*np.log(6)+9/(4*n)*np.log(6)+2/n*nl(6*b)

def bounds(b,n):
    en=[energy_const(b,n,l)/((1-l)*b) for l in LS]; i=int(np.argmin(en))
    x=1.5*np.log(4/3)+np.log(1-1/(16*b)) if b>=.25 else None
    return dict(plane_bound=(1.5*np.log(54)+1.5/n*np.log(4)+2/n*nl(6*b))/b,
                mixed_bound=(1.5*np.log(108)+1.5/n*np.log(2)+2/n*nl(6*b))/(2*b),
                log_form_bound=(3+1/(2*n))*nl(6*b)/b,
                energy_per_vertex_bound=en[i],energy_best_l=float(LS[i]),
                energy_per_vertex_lower=None if x is None else (3*(1-1/(2*n))*x+(1-3/(2*n))*1.5*np.log(6)-2/n*nl(6*b))/(7*b),
                existing_law_term_mean=4*np.log(cap(24*b))/b,
                previous_module_l0p2=(3*(np.log(4)+1.5*np.log(120))+2/n*np.log(cap(24*b)))/(.8*b))

def derive(r):
    N,b=r['N'],r['beta']; n=N/2; p=r['plane_mean']
    r['bounds']={k:(None if v is None else float(v)) for k,v in bounds(b,n).items()}
    r['beta_times_energy_per_vertex']=float(b*sum(v[0] for v in p.values()))
    z=lambda a,c:float((a[0]-c[0])/np.hypot(a[1],c[1]))
    r['sheet_vs_off_z']=z(r['sheet_12'],r['off_sheet_12']); r['plane12_vs_03_z']=z(p['12'],p['03'])
    return r

def start(N):
    U=np.zeros((4,N,N,N,N,4)); U[...,0]=1
    U[1][:,0,:,:]=np.array([0.,1,0,0]); U[2][:,:,0,:]=np.array([0.,0,1,0])
    return U

def sample(N,bstd,nsweep):
    beta=bstd/2; rng=np.random.default_rng(int(bstd)+N); z=twist(N); par=np.indices((N,)*4).sum(0)%2
    U=start(N); planes=[(0,1),(0,2),(1,3),(2,3),(0,3),(1,2)]
    for _ in range(300):
        heat(U,z,beta,rng,par); over(U,z,par)
    rec=[]
    for _ in range(nsweep):
        heat(U,z,beta,rng,par); over(U,z,par)
        row=[d2(U,z,m,n).mean() for m,n in planes]
        f=d2(U,z,1,2); sheet=f[:,0,0,:].mean(); off=(f.sum()-f[:,0,0,:].sum())/(f.size-N*N)
        g=d2(U,z,0,1); slices=[g[t].mean() for t in range(N)]
        rec.append(row+[sheet,off]+slices)
    a=np.array(rec); nb=20; bins=np.array([b.mean(0) for b in np.array_split(a,nb)])
    m=bins.mean(0); e=bins.std(0,ddof=1)/np.sqrt(nb)
    return dict(N=N,beta_std=bstd,beta=beta,sweeps=nsweep,bins=nb,
           plane_mean={f"{p[0]}{p[1]}":[float(m[i]),float(e[i])] for i,p in enumerate(planes)},
           sheet_12=[float(m[6]),float(e[6])],off_sheet_12=[float(m[7]),float(e[7])],
           time_slices_01=[[float(m[8+t]),float(e[8+t])] for t in range(N)])

def thermo(N=4,nsweep=400):
    # e(beta)=d(-log Z)/d beta per vertex; integrate on a grid from beta=0, where e=12.
    grid=[0.]+[float(x) for x in np.geomspace(.05,64,22)]; z=twist(N); par=np.indices((N,)*4).sum(0)%2
    rng=np.random.default_rng(4242); U=start(N); es=[12.]; errs=[0.]
    planes=[(0,1),(0,2),(1,3),(2,3),(0,3),(1,2)]
    for b in grid[1:]:
        for _ in range(100):
            heat(U,z,b,rng,par); over(U,z,par)
        rec=[]
        for _ in range(nsweep):
            heat(U,z,b,rng,par); over(U,z,par)
            rec.append(sum(d2(U,z,m,n).mean() for m,n in planes))
        a=np.array(rec); bins=np.array([c.mean() for c in np.array_split(a,10)])
        es.append(float(a.mean())); errs.append(float(bins.std(ddof=1)/np.sqrt(10)))
    logZ=-integrate.cumulative_trapezoid(es,grid,initial=0.)
    T=(N-1)*N**3; g=(N-1)**3*N; V=N**4; tc=T
    out=[]
    for b,e,er,lz in zip(grid,es,errs,logZ):
        if b==0: continue
        low=(4*V-tc)/V*(-nl(6*b))
        L=lambda s:-nl(s)
        up=(g*(L(b)+L(2*b)+L(3*b))+3*(T-g)*L(b))/V
        out.append(dict(beta=b,energy_per_vertex=e,err=er,log_Z_per_vertex_trapezoid=float(lz),proved_lower=float(low),proved_upper=float(up)))
    return out

def bad_density_coupling(n,f=.1,delta=1e-3,t=4.):
    # Smallest beta from measure_bad_density_free with #bad <= f N^4 at probability exp(-t N^4), by fixed point, best l.
    # t=4 matches the README's exp(-links). README value at L=1: 4 (log cap(24 beta)+1)/(f delta^2) = 1.6e9.
    b=1e9
    for _ in range(40):
        b=min((energy_const(b,n,l)+t)/((1-l)*f*delta**2) for l in LS)
    return float(b)

def gaussian_mode_count(m=64):
    k=2*np.pi*(np.arange(m)+.5)/m; s=2-2*np.cos(k)
    # <log K^2> in 4D, on a midpoint grid; the third mode has <log(2-2cos k0)> = 0.
    v=np.log(s[:,None,None,None]+s[None,:,None,None]+s[None,None,:,None]+s[None,None,None,:]).mean()
    return dict(mean_log_K2_4d=float(v),offset_from_3_log_mass_beta=float(-1.5*2*v),
                proved_lower_offset=float(-4.5*np.log(6)),proved_upper_offset=float(-1.5*np.log(6)))

if __name__=='__main__':
    out,Ns,nsweep=sys.argv[1],sys.argv[2],int(sys.argv[3]); flags=sys.argv[4:]
    if '--refresh' in flags:
        d=json.load(open(out)); runs=d['runs'] if isinstance(d,dict) else d
        res=dict(d) if isinstance(d,dict) else {}
    else:
        runs=[sample(int(k),b,nsweep) for k in Ns.split(',') for b in (2.,8.,32.,128.)]; res={}
    res['runs']=[derive(r) for r in runs]
    res['gaussian_mode_count']=gaussian_mode_count()
    res['bad_density_coupling_f0p1_delta1e-3']={str(n):bad_density_coupling(n) for n in (1,2,3,5,10,100,10000)}
    if '--thermo' in flags: res['log_Z_check']=thermo()
    json.dump(res,open(out,'w'),indent=1)
    for r in res['runs']:
        print(r['N'],r['beta_std'],{k:round(v,4) for k,v in r['plane_mean'].items() if 0} ,'m01 %.4f m12 %.4f m03 %.4f'%(r['plane_mean']['01'][0],r['plane_mean']['12'][0],r['plane_mean']['03'][0]),
              {k:(None if v is None else round(v,3)) for k,v in r['bounds'].items()},'zs %.2f z12 %.2f'%(r['sheet_vs_off_z'],r['plane12_vs_03_z']))
    print(res['gaussian_mode_count']); print(res['bad_density_coupling_f0p1_delta1e-3'])
    for q in res.get('log_Z_check',[]): print(q)
