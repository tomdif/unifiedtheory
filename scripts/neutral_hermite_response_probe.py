#!/usr/bin/env python3
"""Local ordered-response test on neutral Hermite-Gaussian trial profiles.

This is an exploratory floating calculation, not a Lean domain theorem or
an estimate along evolution. The charged coherent packet is projected to
zero charge; its neutral Gaussian is multiplied by normalized physicists'
Hermite polynomials H_n(sqrt(2*w)*(x4-B))/sqrt(2**n*n!). All complex modes
are retained. The ratio uses the positive ordered potential density, not
full Hamiltonian energy, and the clock coordinate is fixed.
"""
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh
from independent_neutral_moment_probe import Kernels
from matter_energy_gram_probe import inverse_shift, whitening
np.seterr(over='raise',invalid='raise',divide='raise')

def matrices(A,B,P,h,s,N,nt=64,nd=512):
 if not isinstance(N,int) or isinstance(N,bool) or N<0 or N>96:
  raise ValueError('Require an integer Hermite degree between 0 and 96.')
 if not np.isfinite([A,B,P,h,s]).all():
  raise ValueError('Nonfinite packet parameter.')
 k=Kernels([[A,B,P]],h=h,nt=nt,nd=nd)
 C=np.exp(s)+1; z=inverse_shift(s,1.,h); Cz=np.exp(z)+1
 r=np.exp((z-s)/2); rp=(C/Cz-1)*r/2
 L=np.eye(5,dtype=complex)*r; L[4,4]=1; L[4,2:4]=2*(r-1)
 Lp=np.eye(5,dtype=complex)*rp; Lp[4,4]=0; Lp[4,2:4]=2*rp
 H=2*(L.T@k.W@L).real; Hp=2*(Lp.T@k.W@L+L.T@k.W@Lp).real
 V=.5*np.linalg.inv(H); Vp=-2*V@Hp@V
 lin=(k.b[0]@L).conj()+k.c[0]@L; linp=(k.b[0]@Lp).conj()+k.c[0]@Lp
 mu=lin@V; mup=linp@V+lin@Vp
 K=np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+.5*np.sum(lin*mu,axis=-1)+k.la[0]+k.lc[0]-k.logbase)
 Kp=K*(-np.trace(V@Hp)+np.sum(linp*mu,axis=-1)+.5*np.sum(lin*(lin@Vp),axis=-1))
 F=np.array([0.,0.,1.,1.,1.]); scale=np.sqrt(2*k.widths[4])
 X=scale*L[4].conj(); Xp=scale*Lp[4].conj(); Y=scale*L[4]; Yp=scale*Lp[4]
 means=[mu@X-scale*B,mu@Y-scale*B,mu@F]
 meanps=[mup@X+mu@Xp,mup@Y+mu@Yp,mup@F]
 vec=[X,Y,F]; vecp=[Xp,Yp,np.zeros(5)]
 cov=np.array([[a@V@b for b in vec] for a in vec])
 covp=np.array([[vecp[i]@V@vec[j]+vec[i]@Vp@vec[j]+vec[i]@V@vecp[j] for j in range(3)] for i in range(3)])
 T=np.zeros((N+1,N+1),complex); Tp=T.copy()
 # Chunking limits memory while retaining the full angle quadrature.
 for lo in range(0,len(K),2048):
  sl=slice(lo,lo+2048); size=len(K[sl]); M=[m[sl] for m in means]; Mp=[m[sl] for m in meanps]
  G=np.zeros((N+1,N+1,5,size),complex); D=np.zeros_like(G)
  G[0,0,0]=1
  for p in range(1,5):
   G[0,0,p]=M[2]*G[0,0,p-1]; D[0,0,p]=Mp[2]*G[0,0,p-1]+M[2]*D[0,0,p-1]
   if p>1:
    G[0,0,p]+=(p-1)*cov[2,2]*G[0,0,p-2]
    D[0,0,p]+=(p-1)*(covp[2,2]*G[0,0,p-2]+cov[2,2]*D[0,0,p-2])
  for m in range(N):
   fac=np.sqrt(2/(m+1)); back=np.sqrt(m/(m+1))
   for p in range(5):
    G[0,m+1,p]=fac*M[1]*G[0,m,p]
    D[0,m+1,p]=fac*(Mp[1]*G[0,m,p]+M[1]*D[0,m,p])
    if m:
     G[0,m+1,p]+=(2*cov[1,1]-1)*back*G[0,m-1,p]
     D[0,m+1,p]+=back*(2*covp[1,1]*G[0,m-1,p]+(2*cov[1,1]-1)*D[0,m-1,p])
    if p:
     G[0,m+1,p]+=fac*p*cov[1,2]*G[0,m,p-1]
     D[0,m+1,p]+=fac*p*(covp[1,2]*G[0,m,p-1]+cov[1,2]*D[0,m,p-1])
  for n in range(N):
   fac=np.sqrt(2/(n+1)); back=np.sqrt(n/(n+1))
   for m in range(N+1):
    cross=2*np.sqrt(m/(n+1))
    for p in range(5):
     G[n+1,m,p]=fac*M[0]*G[n,m,p]
     D[n+1,m,p]=fac*(Mp[0]*G[n,m,p]+M[0]*D[n,m,p])
     if n:
      G[n+1,m,p]+=(2*cov[0,0]-1)*back*G[n-1,m,p]
      D[n+1,m,p]+=back*(2*covp[0,0]*G[n-1,m,p]+(2*cov[0,0]-1)*D[n-1,m,p])
     if m:
      G[n+1,m,p]+=cross*cov[0,1]*G[n,m-1,p]
      D[n+1,m,p]+=cross*(covp[0,1]*G[n,m-1,p]+cov[0,1]*D[n,m-1,p])
     if p:
      G[n+1,m,p]+=fac*p*cov[0,2]*G[n,m,p-1]
      D[n+1,m,p]+=fac*p*(covp[0,2]*G[n,m,p-1]+cov[0,2]*D[n,m,p-1])
  poly=G[:,:,0]+G[:,:,2]/2+G[:,:,4]/4
  polyp=D[:,:,0]+D[:,:,2]/2+D[:,:,4]/4
  T+=np.einsum('ijk,k->ij',poly,K[sl]*k.aw[sl])
  Tp+=np.einsum('ijk,k->ij',polyp,K[sl]*k.aw[sl])+np.einsum('ijk,k->ij',poly,Kp[sl]*k.aw[sl])
 err=max(np.linalg.norm(M-M.conj().T)/np.linalg.norm(M) for M in [T,Tp])
 if err>2e-9:raise ArithmeticError('nonhermitian '+str(err))
 T=(T+T.conj().T)/2; Tp=(Tp+Tp.conj().T)/2
 coeff=2/C-(1/Cz+1/Cz**2).real
 ref=k.at(s)
 assert abs(T[0,0]-ref[0][0,0])/abs(T[0,0])<2e-11
 assert abs(Tp[0,0]-ref[1][0,0])/max(1.,abs(Tp[0,0]))<2e-11
 return T,coeff*T-Tp/C,Tp,dict(hermitian_error=err,gram_error=k.oracle_error)


def record(M):
 return dict(real=M.real.tolist(),imag=M.imag.tolist())


def sha(path):
 return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 root=Path(__file__).resolve().parents[1]
 parent_path=root/'data/quantum_charge_conservation_audit.json'
 parent_sha='92d8a58152c531a2ef9c797d482650717bb8a448e3b1f76d4c1b8050e72174b0'
 assert sha(parent_path)==parent_sha
 parent=json.loads(parent_path.read_text())
 assert len(parent['source_sha256'])==2039
 assert all(sha(root/p)==h for p,h in parent['source_sha256'].items())
 assert sha(root/'UnifiedTheory.lean')==parent['root_check']['source_sha256']
 from verify_neutral_hermite_response import reference
 params=dict(A=2.,B=1.,P=-.2,h=.3,s=-.5,N=6,nt=48)
 ref=reference(**params)
 T,R,Tp,checks=matrices(**params,nd=192)
 dx=1e-3
 refp=(-reference(**{**params,'s':params['s']+2*dx})+8*reference(**{**params,'s':params['s']+dx})
       -8*reference(**{**params,'s':params['s']-dx})+reference(**{**params,'s':params['s']-2*dx}))/(12*dx)
 matrix_error=float(np.linalg.norm(T-ref)/max(1.,np.linalg.norm(ref)))
 derivative_error=float(np.linalg.norm(Tp-refp)/max(1.,np.linalg.norm(refp)))
 assert matrix_error<2e-9 and derivative_error<2e-7,(matrix_error,derivative_error)
 print('Independent direct Hermite quadrature and clock-derivative checks passed.',flush=True)
 derivative_checks=[]
 for s in [0.,1.]:
  p=dict(A=10.,B=8.,P=-.4,h=.05,s=s,N=8)
  T,R,Tp,_=matrices(**p)
  fd=(-matrices(**{**p,'s':s+2*dx})[0]+8*matrices(**{**p,'s':s+dx})[0]
      -8*matrices(**{**p,'s':s-dx})[0]+matrices(**{**p,'s':s-2*dx})[0])/(12*dx)
  err=float(np.linalg.norm(Tp-fd)/max(1.,np.linalg.norm(Tp)))
  assert err<2e-7,err
  derivative_checks.append(err)
 cases=[]
 for A,B,P,h,s in [(10.,8.,-.4,.05,0.),(10.,8.,-.4,.05,1.),(20.,16.,-.4,.05,1.)]:
  runs=[];first=None
  for nt,nd in [(64,512),(96,768)]:
   start=time.monotonic();T,R,Tp,checks=matrices(A,B,P,h,s,64,nt,nd)
   spectra=[]
   for N in [0,8,16,24,32,48,64]:
    a=T[:N+1,:N+1];b=R[:N+1,:N+1];W,cond=whitening(a)
    assert cond['whitening_residual']<2e-8
    M=W.conj().T@b@W;vals,vecs=eigh((M+M.conj().T)/2);v=W@vecs[:,0]
    residual=float(np.linalg.norm(b@v-vals[0]*(a@v))/max(1.,np.linalg.norm(b@v)))
    assert residual<2e-8
    spectra.append(dict(degree=N,minimum=float(vals[0]),maximum=float(vals[-1]),
       condition=cond,residual=residual,witness_real=v.real.tolist(),witness_imag=v.imag.tolist()))
   change=0.
   if first is not None:
    d=np.sqrt(np.diag(T).real)
    change=float(max(np.linalg.norm((M-Q)/d[:,None]/d[None,:],2) for M,Q in zip([T,R],first)))
    assert change<2e-8,change
   first=[T,R]
   runs.append(dict(nt=nt,nd=nd,spectra=spectra,checks=checks,scaled_matrix_change=change,
      matrices=dict(drift_density=record(T),response_density=record(R)),seconds=time.monotonic()-start))
   print(json.dumps(dict(A=A,s=s,nt=nt,nd=nd,minima=[v['minimum'] for v in spectra],change=change)),flush=True)
  cases.append(dict(A=A,B=B,P=P,h=h,clock_coordinate=s,runs=runs))
 paths=['scripts/neutral_hermite_response_probe.py','scripts/verify_neutral_hermite_response.py',
  'scripts/independent_neutral_moment_probe.py','scripts/projected_initial_moment_probe.py',
  'scripts/projected_integrated_response_probe.py','scripts/projected_kernel_matrix_probe.py',
  'scripts/matter_energy_gram_probe.py','scripts/displaced_signed_response_probe.py']
 report=dict(kind='Local ordered-response/drift test on neutral Hermite trial profiles',epsilon=1.,
  couplings=dict(mass2=1.,quartic=1.,vacuum=1.),cases=cases,
  reference=dict(parameters=params,matrix=record(ref),matrix_error=matrix_error,derivative_error=derivative_error),
  derivative_checks=derivative_checks,formal_checkpoint=dict(path=str(parent_path.relative_to(root)),sha256=parent_sha),
  source_sha256={p:sha(root/p) for p in paths},
  profile='H_n(sqrt(2*w)*(x4-B))/sqrt(2^n*n!) times the neutral Gaussian of the zero-charge-projected coherent packet; w=1/(64*abs(h)).',
  ratio='At fixed clock s, T is the positive ordered potential density with vacuum+Phi^2/2+Phi^4/4. R=(2/C-Re(1/Cz+1/Cz^2))*T-Tprime/C. The common shifted clock scalar cancels. This is not full response divided by full Hamiltonian energy.',
  limitations=['Floating quadrature and Gaussian moment recurrence, without certified error enclosures.',
   'Clock coordinate is fixed; no clock integration, evolving state, or uniform state/time/regulator estimate.',
   'The polynomial Hermite family is exploratory; its full ordered operator-domain and response identity have not been added to Lean.',
   'The degree-zero profile is checked against the existing admitted packet implementation.',
   'The separate quadrature shares inverse-clock and source conventions; high-degree errors are checked by angle refinement, not exact arithmetic.',
   'All complex modes are kept, with no rank truncation. Stable finite minima do not prove a lower bound for the infinite family.',
   'No clock recovery, necessary model revision, physical identification or TOE is established.'])
 assert sha(parent_path)==parent_sha and all(sha(root/p)==h for p,h in parent['source_sha256'].items())
 assert sha(root/'UnifiedTheory.lean')==parent['root_check']['source_sha256']
 args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
 print(args.output,flush=True)


if __name__=='__main__':
 main()
