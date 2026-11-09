#!/usr/bin/env python3
"""Reproduce a candidate negative fixed-time response on displaced Gaussians.

Run: python3 scripts/displaced_signed_response_probe.py --output PATH
Requires NumPy and SciPy. Floating-point evidence only, not a Lean sign proof.

Q(theta)=(0,0,A*cos(theta)/2,A*cos(theta)/2,A),
P(theta)=(0,0,A*sin(theta)/2,-A*sin(theta)/2,-lam/A).
These are the actual charge-orbit coordinates identified in
KFCausalDisplacedQuarticTestFamily. Clock displacement and phase are zero.
The widths are alpha=1/(2*abs(h)), beta=alpha/32. The common normalization
and charge-dependent constant phase cancel in every reported ratio.

Five transverse integrals are evaluated by Gaussian moments. The remaining
clock and charge integrals use finite quadrature. All responses and energy
components are divided by the same charge-averaged energy at physical time
zero. The full response is a fixed-time weak expression, not a proved time
derivative along evolution. No finite scan tests a state-uniform lower bound.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time
import matter_energy_gram_probe as old
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import logsumexp


def sources(A,lam,h,theta):
    """Use the proved physical centres, without a fitted orbit recipe."""
    theta=np.atleast_1d(theta)
    widths=np.array([1.,1.,1.,1.,1/32])/(2*abs(h))
    Q=np.zeros((len(theta),5)); P=np.zeros_like(Q)
    Q[:,2]=Q[:,3]=A*np.cos(theta)/2; Q[:,4]=A
    P[:,2]=A*np.sin(theta)/2; P[:,3]=-P[:,2]; P[:,4]=-lam/A
    b=2*widths*Q+1j*P/h
    logamp=-np.sum(widths*Q*Q,axis=1)
    return widths,b,logamp,Q,P


def forms(A=3.,lam=3.,h=.05,eps=1.,a=1.,nt=128,ns=160,left=-10.,right=4.,mass2=1.,quartic=1.,vacuumc=1.):
    if not np.isfinite([A,lam,h,eps,a,left,right,mass2,quartic,vacuumc]).all():
        raise ValueError('All parameters must be finite.')
    if not (A != 0 and eps > 0 and a > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
        raise ValueError('Require A nonzero, epsilon,a positive, 0<abs(h)<=2*pi*epsilon/3.')
    if min(mass2,quartic,vacuumc) < 0 or ns < 16 or nt < 8 or left >= right:
        raise ValueError('Require nonnegative couplings and valid quadrature settings.')
    theta=2*np.pi*np.arange(nt)/nt
    widths,b,logamp,_,_=sources(A,lam,h,theta)
    mu0=b.real/2/widths
    V0=np.diag(1/(4*widths))
    logZ0=2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1]+np.sum(b.real*mu0,axis=1)+2*logamp.real
    kinetic=np.zeros(nt)
    for direction in np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]]):
        row=-2*widths*direction
        kinetic+=h*h*(np.abs(b@direction+mu0@row)**2+row@V0@row)
    F=np.array([0.,0.,1.,1.,1.])
    nodes,weights=leggauss(ns)
    nodes=left+(nodes+1)*(right-left)/2
    weights*=(right-left)/2/nt
    ls=[];li=[]
    out={k:[] for k in ['field','quartic','vacuum','direct0','direct1','shear0','shear1','C0','C1','vacuum_response']}
    static=[]; static_rate=[]; static_direct=[]
    flow=np.eye(5)/2;flow[4,:]=[0,0,1,1,0]
    for s,ds in zip(nodes,weights):
        C=np.exp(s)+eps;D=eps/C;chart=np.exp(s)+eps*s
        z=old.inverse_shift(s,eps,h);r=np.exp((z-s)/2)
        L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
        H=2*(L.T@np.diag(widths)@L).real
        if np.linalg.eigvalsh(H)[0] <= 0:
            raise ArithmeticError('Shifted Gaussian quadratic form is not positive.')
        V=.5*np.linalg.inv(H)
        B=b@L;mu=2*B.real@V
        logZ=2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+np.sum(B.real*mu,axis=1)+2*logamp.real
        ls.append(np.log(ds)+np.log(C)-2*s-2*a*(chart*chart-h*h/4)+logZ)
        li.append(np.log(ds)+2*np.log(C)-2*s-2*a*chart*chart+logZ0)
        static.append(.5*(C+kinetic/C))
        static_rate.append(.5*(-np.exp(s)/C+kinetic*np.exp(s)/C**3))
        realfactor=2*(np.exp(s)/(2*C*C)-1/C-2*a*chart)
        static_direct.append(realfactor*.5*(C+kinetic/C))
        fv=F@V@F;fm=mu@F
        moments=[fm*fm+fv,fm**4+6*fm*fm*fv+3*fv*fv]
        phys=eps/(np.exp(z)+eps);m=(D-phys)/eps
        factor=2*(np.exp(z)/(2*(np.exp(z)+eps)**2)-1/(np.exp(z)+eps)-2*a*(chart-.5j*h)).real
        out['vacuum'].append(np.ones(nt));out['field'].append(moments[0]);out['quartic'].append(moments[1])
        out['vacuum_response'].append(np.full(nt,factor))
        # Gaussian integration by parts computes F^(2p)*(velocity dot grad g+g)
        # via Gaussian derivatives of the polynomial, independent of weak TBf.
        Qmat=-2*L.T@np.diag(widths)@L@flow
        lin=B@flow
        covF=V@F
        for p in [1,2]:
            degree=2*p
            meanpower=moments[p-1]
            Mprev=fm if p==1 else fm**3+3*fm*fv
            Mprev2=np.ones(nt) if p==1 else fm*fm+fv
            xmoment=mu*meanpower[:,None]+degree*Mprev[:,None]*covF
            xxmoment=np.einsum('ti,tj,t->tij',mu,mu,meanpower)+V[None,:,:]*meanpower[:,None,None]
            xxmoment+=degree*Mprev[:,None,None]*(np.einsum('ti,j->tij',mu,covF)+np.einsum('i,tj->tij',covF,mu))
            xxmoment+=degree*(degree-1)*Mprev2[:,None,None]*np.outer(covF,covF)
            derivative=meanpower+np.sum(lin*xmoment,axis=1)+np.einsum('ij,tij->t',Qmat,xxmoment)
            rate=(phys*(1-phys)).real/eps*meanpower+2*np.real(m*derivative)
            fieldprime=1.5*np.array([0.,0.,1.,1.,0.])
            covS=F@V@fieldprime;meanS=mu@fieldprime
            cp=p*(meanS*Mprev+(degree-1)*covS*Mprev2)
            out[f'direct{p-1}'].append(factor*meanpower)
            out[f'shear{p-1}'].append(rate)
            out[f'C{p-1}'].append(2*m.real*cp)
    ls=np.concatenate(ls);li=np.concatenate(li);static=np.concatenate(static)
    out={k:np.concatenate(v) for k,v in out.items()}
    growing=mass2/2*out['field']+quartic/4*out['quartic']+vacuumc*out['vacuum']
    logE=logsumexp(np.concatenate([ls+np.log(growing),li+np.log(static)]))
    result={k:float(np.dot(np.exp(ls-logE),v)) for k,v in out.items()}
    result['static']=float(np.dot(np.exp(li-logE),static))
    result['static_response']=float(np.dot(np.exp(li-logE),np.concatenate(static_rate)))
    result['static_direct_response']=float(np.dot(np.exp(li-logE),np.concatenate(static_direct)))
    result['logE']=float(logE)
    result['matter']=mass2/2*result['direct0']+quartic/4*result['direct1']
    result['shear_matter']=mass2/2*result['shear0']+quartic/4*result['shear1']
    result['full_response']=result['matter']+vacuumc*result['vacuum_response']+result['static_response']
    result['input_charge_norm_spread']=float(np.ptp(logZ0))
    result['direct_shear_error']=max(abs(result[f'direct{i}']-result[f'shear{i}']) for i in [0,1])
    result['static_pairing_error']=abs(result['static_response']-result['static_direct_response'])
    assert result['direct_shear_error'] < 2e-8
    assert result['static_pairing_error'] < 2e-10
    assert result['input_charge_norm_spread'] < 2e-8
    assert all(np.isfinite(v) for v in result.values())
    assert abs(result['static']+mass2/2*result['field']+quartic/4*result['quartic']+vacuumc*result['vacuum']-1)<1e-9
    return result


def independent_checks():
    """Check sources and shear polynomials against different calculations."""
    from numpy.polynomial.hermite import hermgauss
    nodes, weights = hermgauss(4)  # Degree six; tensor rule exact in exact arithmetic.
    indices = np.array(list(itertools.product(range(4), repeat=5)))
    cloud = nodes[indices]
    cloud_weights = np.prod(weights[indices], axis=1)/np.pi**2.5
    source_errors, amplitude_errors, moment_errors, chart_errors = [], [], [], []
    A, lam = 10., 4.
    theta = np.array([0., .61, 1.7, 3.1])
    flow = np.eye(5)/2
    flow[4,:] = [0,0,1,1,0]
    F = np.array([0.,0.,1.,1.,1.])
    for h in [.01,-.01,.05,-.05]:
        widths,b,logamp,Q,P = sources(A,lam,h,theta)
        _,b0,logamp0,_,_ = sources(A,lam,h,[0.])
        rotated = b0*np.exp(1j*np.sign(h)*theta[:,None]*np.array([1.,-1.,1.,-1.,0.]))
        rotated_amp = logamp0+np.sum(b0[:,:4]**2-rotated[:,:4]**2,axis=1)/(8*widths[0])
        source_errors.append(float(np.max(abs(b-rotated))))
        amplitude_errors.append(float(np.max(abs(logamp-rotated_amp))))
        assert np.max(abs(Q@F-A*(1+np.cos(theta)))) < 1e-12
        assert np.max(abs(np.sum((Q@flow.T)*P,axis=1)+lam*np.cos(theta))) < 1e-12
        for s in [-2.,-.3,1.]:
            z=old.inverse_shift(s,1.,h)
            chart_errors.append(float(abs(np.exp(z)+z-(np.exp(s)+s-.5j*h))))
            r=np.exp((z-s)/2)
            L=np.eye(5,dtype=complex)*r; L[4,4]=1; L[4,2:4]=2*(r-1)
            H=2*(L.T@np.diag(widths)@L).real
            V=.5*np.linalg.inv(H)
            B=b@L; mu=2*B.real@V
            offsets=cloud@np.linalg.inv(np.linalg.cholesky(H).T).T
            Qmat=-2*L.T@np.diag(widths)@L@flow
            lin=B@flow
            covF=V@F; fv=F@V@F; fm=mu@F
            for p in [1,2]:
                d=2*p
                Mp=fm*fm+fv if p==1 else fm**4+6*fm*fm*fv+3*fv*fv
                Mprev=fm if p==1 else fm**3+3*fm*fv
                Mprev2=np.ones(len(theta)) if p==1 else fm*fm+fv
                xm=mu*Mp[:,None]+d*Mprev[:,None]*covF
                xxm=np.einsum('ti,tj,t->tij',mu,mu,Mp)+V[None,:,:]*Mp[:,None,None]
                xxm+=d*Mprev[:,None,None]*(np.einsum('ti,j->tij',mu,covF)+np.einsum('i,tj->tij',covF,mu))
                xxm+=d*(d-1)*Mprev2[:,None,None]*np.outer(covF,covF)
                expected=Mp+np.sum(lin*xm,axis=1)+np.einsum('ij,tij->t',Qmat,xxm)
                for j in range(len(theta)):
                    x=offsets+mu[j]
                    grad=B[j]-2*(x@L.T*widths)@L
                    shear_polynomial=1+np.sum(grad*(x@flow.T),axis=1)
                    power=(x@F)**d
                    direct=np.dot(cloud_weights,power*shear_polynomial)
                    moment_errors.append(float(abs(direct-expected[j])/max(1.,abs(direct),abs(expected[j]))))
                    moment_errors.append(float(abs(np.dot(cloud_weights,power)-Mp[j])/max(1.,abs(Mp[j]))))
    assert max(source_errors) < 1e-10
    assert max(amplitude_errors) < 1e-8
    assert max(moment_errors) < 2e-10
    assert max(chart_errors) < 2e-12
    return dict(A=A,lam=lam,hbar=[.01,-.01,.05,-.05],clock=[-2.,-.3,1.],
                angles=theta.tolist(),hermite_order=4,
                source_rotation_max_errors=source_errors,amplitude_rotation_max_errors=amplitude_errors,
                gaussian_moment_relative_or_absolute_errors=moment_errors,inverse_chart_errors=chart_errors)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    np.seterr(over='raise',invalid='raise',divide='raise')
    checks=independent_checks()
    print('Independent physical-source, shear-polynomial and inverse-chart checks passed.',flush=True)
    settings=[dict(ns=160,nt=128,left=-10.,right=4.),
              dict(ns=240,nt=192,left=-12.,right=4.5),
              dict(ns=360,nt=256,left=-14.,right=5.)]
    parameters=dict(A=10.,lam=4.,eps=1.,a=1.,mass2=1.,quartic=1.,vacuumc=1.)
    hbars=[.01,-.01,.05]
    runs=[]
    for setting in settings:
        start=time.monotonic()
        values=[dict(h=h,**forms(h=h,**parameters,**setting)) for h in hbars]
        runs.append(dict(quadrature=setting,values=values,seconds=time.monotonic()-start))
        print(json.dumps(dict(quadrature=setting,
            full_response_over_energy=[v['full_response'] for v in values])),flush=True)
    refinements=[]
    for previous,current in zip(runs,runs[1:]):
        for before,after in zip(previous['values'],current['values']):
            changes={k:abs(before[k]-after[k])/max(1.,abs(after[k])) for k in before if k!='h'}
            refinements.append(dict(h=after['h'],changes=changes))
    assert max(max(r['changes'].values()) for r in refinements)<2e-8
    sign_errors=[abs(r['values'][0]['full_response']-r['values'][1]['full_response']) for r in runs]
    assert max(sign_errors)<2e-10
    # Regression of this explicitly identified candidate; this is not certification.
    assert all(v['full_response'] < -.01 for r in runs for v in r['values'])
    root=Path(__file__).resolve().parents[1]
    files=['scripts/displaced_signed_response_probe.py','scripts/matter_energy_gram_probe.py',
           'UnifiedTheory/Audit/KFCausalDisplacedQuarticTestFamily.lean',
           'data/clock_shift_left_asymptotic_audit.json']
    report=dict(kind='Exploratory floating-point quadrature; sign not certified',
                parameters=parameters,physical_time=0.,hbar=hbars,
                physical_orbit='Q=(0,0,A*cos(theta)/2,A*cos(theta)/2,A); P=(0,0,A*sin(theta)/2,-A*sin(theta)/2,-lam/A)',
                normalization='All components and responses divided by the same charge-averaged energy. logE is the unnormalized energy logarithm; common state normalization and constant charge phases cancel.',
                response_recipe='matter=mass2*direct0/2+quartic*direct1/4; full_response=matter+vacuumc*vacuum_response+static_response',
                source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files},
                checks=checks,runs=runs,refinements=refinements,hbar_sign_errors=sign_errors,
                limitations=['No interval enclosure of clock tails or quadrature error; no certified negative integral.',
                             'This displaced family is larger than the old coherent parameter family; finite coherent-span membership is not claimed.',
                             'The full expression has no proved identification with a derivative along Hamiltonian evolution.',
                             'A negative fixed-time response does not disprove a finite one-sided lower energy bound, consistency, or clock escape.',
                             'No model revision or physical TOE follows.'])
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(args.output,flush=True)
    else:
        print(json.dumps(report,indent=2,allow_nan=False))


if __name__=='__main__':
    main()


