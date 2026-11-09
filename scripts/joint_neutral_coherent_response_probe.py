"""Finite coupled charged/neutral coherent-kernel response diagnostic.

This evaluates the exact Gaussian formula for the transverse kernel in
KFCausalReciprocalNeutralKernel, with P_i=1 and independent real charged
widths and complex neutral sources. All complex cross terms are retained.
It is a floating computation, not a Lean proof, interval certificate,
full-Hamiltonian response test, or bound along evolution. No eigenmodes
are discarded: an ill-conditioned matrix rejects the whole test case.

The scan uses the physical alpha=1/(2*abs(h)), beta=alpha/32 and eps=abs(h),
so every scan point is in the existing strong-domain strip. The coordinate
s is log(eps)+offset. Generalized eigenvalues maximize the local kernel
logarithmic derivative over the entire tested finite coherent span. A
finite maximum does not imply a uniform bound over all finite families.
The reported radial-obstruction profile is the precise earlier Lean
example at eps=1,h=-1/64,s=0, with its source frozen at that clock position.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh
from numpy.polynomial.hermite import hermgauss
from matter_energy_gram_probe import inverse_shift


def geometry(eps,h,s):
    z=inverse_shift(s,eps,h)
    r=np.exp((z-s)/2)
    rp=(np.exp(s)*(r*(1-r*r))/(eps+np.exp(s)*r*r))/2
    return r,rp


def components(alpha,beta,w,b,r,rp):
    w=np.asarray(w,float); b=np.asarray(b,complex)
    wi,wj=w[:,None],w[None,:]
    bi,bj=b[:,None].conj(),b[None,:]
    A=alpha/2*(r.conjugate()**2/wi+r*r/wj)
    B=alpha/2*(r.conjugate()**2*wi+r*r*wj)
    C=B-8*beta*r.imag**2
    Ap=alpha*((r*rp).conjugate()/wi+r*rp/wj)
    Bp=alpha*((r*rp).conjugate()*wi+r*rp*wj)
    Cp=Bp-16*beta*r.imag*rp.imag
    dx=bi+bj; dy=2j*r.imag*(bj-bi); dyp=2j*rp.imag*(bj-bi)
    L=3-2*r.real; Lp=-2*rp.real
    mx=dx/(4*beta); my=dy/(2*C)
    myp=dyp/(2*C)-dy*Cp/(2*C*C)
    mu=mx+L*my; mup=Lp*my+L*myp
    v=1/(4*beta)+L*L/(2*C)
    vp=L*Lp/C-L*L*Cp/(2*C*C)
    pol=1+(mu*mu+v)/2+(mu**4+6*mu*mu*v+3*v*v)/4
    polp=mu*mup+vp/2+mu**3*mup+3*mu*mup*v+1.5*mu*mu*vp+1.5*v*vp
    normalization=-(b.real[:,None]**2+b.real[None,:]**2)/(4*beta)
    E=np.exp(dx*dx/(8*beta)+dy*dy/(4*C)+normalization)
    pref=(np.pi/(4*A))*np.sqrt(np.pi/B)*np.sqrt(np.pi/C)*np.sqrt(np.pi/(2*beta))*E
    score=-Ap/A-Bp/(2*B)-Cp/(2*C)+dy*dyp/(2*C)-dy*dy*Cp/(4*C*C)
    K=pref*pol; Kp=pref*(score*pol+polp)
    return K,Kp


def matrices(alpha,beta,w,b,eps,h,s):
    return components(alpha,beta,w,b,*geometry(eps,h,s))


def quadrature(alpha,beta,wi,wj,bi,bj,r,N):
    A=alpha/2*(r.conjugate()**2/wi+r*r/wj)
    B=alpha/2*(r.conjugate()**2*wi+r*r*wj)
    C=B-8*beta*r.imag**2
    dx=bi.conjugate()+bj; dy=2j*r.imag*(bj-bi.conjugate())
    # Real centering removes linear growth, leaving only an oscillatory phase.
    tx,wx=hermgauss(N); ty,wy=hermgauss(N)
    x=tx/np.sqrt(2*beta)+dx.real/(4*beta)
    y=ty/np.sqrt(C.real)+dy.real/(2*C.real)
    Y,X=np.meshgrid(y,x)
    field=X+(3-2*r.real)*Y
    poly=1+field**2/2+field**4/4
    phase=np.exp(1j*(dx.imag*X+dy.imag*Y-C.imag*Y*Y))
    const=np.exp(dx.real**2/(8*beta)+dy.real**2/(4*C.real)-(bi.real**2+bj.real**2)/(4*beta))
    plane=const*np.einsum('i,j,ij->',wx,wy,poly*phase)/np.sqrt(2*beta*C.real)
    return np.pi/(4*A)*np.sqrt(np.pi/B)*plane


def spectral(K,Kp,floor=1e-9):
    d=1/np.sqrt(K.diagonal().real)
    G=K*d[:,None]*d[None,:]; D=Kp*d[:,None]*d[None,:]
    herr=max(np.linalg.norm(T-T.conj().T)/max(1e-300,np.linalg.norm(T)) for T in [G,D])
    assert herr<1e-10,herr
    G=(G+G.conj().T)/2; D=(D+D.conj().T)/2
    ev=np.linalg.eigvalsh(G)
    if ev[0]<=floor*ev[-1]: return dict(rejected_condition=True,min_eigen=float(ev[0]),max_eigen=float(ev[-1]))
    vals,vec=eigh(D,G)
    coeff=d*vec[:,-1]
    residual=np.linalg.norm(Kp@coeff-vals[-1]*(K@coeff))/(np.linalg.norm(Kp)*np.linalg.norm(coeff)+abs(vals[-1])*np.linalg.norm(K)*np.linalg.norm(coeff))
    return dict(max_slope=float(vals[-1]),min_slope=float(vals[0]),condition=float(ev[-1]/ev[0]),hermitian_error=float(herr),eigen_residual=float(residual)),coeff


def pack(values):
    arr=np.asarray(values,dtype=complex)
    return dict(real=arr.real.tolist(),imag=arr.imag.tolist())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validation():
    alpha,beta,eps,h,s=32.,1.,1.,1.,0.
    w=[1.,1.5,4.]; b=[1+2j,-1+.5j,2-1j]
    K,D=matrices(alpha,beta,w,b,eps,h,s)
    errors=[]
    for delta in [1e-3,1e-4]:
        F=lambda t:matrices(alpha,beta,w,b,eps,h,t)[0]
        fd=(-F(s+2*delta)+8*F(s+delta)-8*F(s-delta)+F(s-2*delta))/(12*delta)
        error=float(np.linalg.norm(fd-D)/np.linalg.norm(D));assert error<2e-8
        errors.append(dict(step=delta,relative_error=error))
    r,_=geometry(eps,h,s);checks=[]
    for i,j in [(0,0),(0,1),(1,2),(2,0)]:
        for order in [48,96]:
            q=quadrature(alpha,beta,w[i],w[j],b[i],b[j],r,order)
            error=float(abs(q-K[i,j])/abs(K[i,j]));assert error<2e-11
            checks.append(dict(i=i,j=j,order=order,relative_error=error))
    return dict(finite_differences=errors,independent_real_quadrature=checks)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    parent=root/'data/quantum_neutral_commutator_domains_audit.json'
    assert digest(parent)=='047e2d5021bd9db56d086d4bde86c593bfd113751493caf4cfc70ba778c35598'
    checks=validation();records=[];best=None;rejected=0
    for h in [1/64,.1,1.,10.,100.]:
        beta=1/(64*h);alpha=32*beta;eps=h
        for scale in [.5,1.,3.]:
            for count in [1,3,5,7]:
                widths=np.geomspace(1,30,count)
                values=np.linspace(-4,4,count) if count>1 else np.array([0.])
                w=np.repeat(widths,count)
                for direction in [1,1j,(1+1j)/np.sqrt(2)]:
                    b=np.tile(direction*np.sqrt(beta)*scale*values,count)
                    for offset in [-3.,0.,1.,2.,3.]:
                        s=np.log(eps)+offset
                        K,D=matrices(alpha,beta,w,b,eps,h,s);out=spectral(K,D)
                        meta=dict(h=h,epsilon=eps,alpha=alpha,beta=beta,source_scale=scale,
                                  count_per_axis=count,dimension=count*count,
                                  source_direction=pack(direction),clock_offset=offset,s=float(s))
                        if isinstance(out,dict):
                            rejected+=1;records.append(dict(**meta,**out));continue
                        result,coeff=out
                        records.append(dict(**meta,**result))
                        if best is None or result['max_slope']>best['result']['max_slope']:
                            best=dict(parameters=meta,result=result,widths=w.tolist(),sources=pack(b),coefficients=pack(coeff),
                                      gram=pack(K),derivative=pack(D))
    r,_=geometry(1.,-1/64,0.)
    b=4+1j*((2/3)/(2*r.imag))
    K,D=matrices(32,1,[1],[b],1.,-1/64,0.)
    q=quadrature(32,1,1,1,b,b,r,96)
    error=float(abs(q-K[0,0])/abs(K[0,0]));assert error<2e-11
    obstruction=dict(epsilon=1.,h=-1/64,s=0.,alpha=32.,beta=1.,width=1.,source=pack(b),geometry=pack(r),
                     kernel=pack(K[0,0]),derivative=pack(D[0,0]),logarithmic_derivative=float((D/K)[0,0].real),
                     quadrature_order=96,quadrature_relative_error=error)
    sources=['scripts/joint_neutral_coherent_response_probe.py','scripts/verify_joint_neutral_coherent_response.py',
             'scripts/matter_energy_gram_probe.py',
             'UnifiedTheory/Audit/KFCausalReciprocalNeutralKernel.lean',
             'UnifiedTheory/Audit/KFCausalReciprocalCrossGeometry.lean',
             'UnifiedTheory/Audit/KFCausalNeutralRadialActualGeometry.lean']
    report=dict(scope=__doc__,source_sha256={p:digest(root/p) for p in sources},
                parent_report=dict(path=str(parent.relative_to(root)),sha256=digest(parent)),
                numpy=np.__version__,conditioning_floor=1e-9,rank_truncation=False,
                validation=checks,test_count=len(records),rejected_cases=rejected,
                records=records,largest_observed=best,radial_obstruction_profile=obstruction,
                conclusion='Finite diagnostic only. No counterexample to the coupled uniform estimate was found in these tested coherent spans. The measured maximum is not a global bound. General neutral polynomials, the full clock integral, full Hamiltonian response, and evolution are not covered by this scan.')
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print('Cases',len(records),'rejected whole matrices',rejected,'largest observed',best['result']['max_slope'])
    print('Radial-obstruction profile full transverse logarithmic derivative',obstruction['logarithmic_derivative'])
    print(args.output)


if __name__=='__main__':
    main()
