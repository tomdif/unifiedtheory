#!/usr/bin/env python3
"""Test the actual zero-charge projected state, retaining complex cross terms.

Run with NumPy/SciPy: python3 scripts/zero_charge_response_probe.py --output PATH
Energy and response are fixed-time forms at t=0, all three couplings one.
The test orbit and its positive real source amplitude are identified by
KFCausalDisplacedQuarticTestFamily and KFCausalDisplacedQuarticOrbitPhase.
The projection averages vectors BEFORE pairing. This is not the older
charge average of the unprojected state's energy.

Five transverse coordinates use analytic Gaussian moment formulas in
floating arithmetic; clock and two charge angles use finite quadrature.
No clock-tail, quadrature-error or sign enclosure is certified.
"""
import argparse
import hashlib
import json
from pathlib import Path

import matter_energy_gram_probe as old
import displaced_signed_response_probe as single
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import i0e
import time

def projected(A=10.,lam=4.,h=.01,eps=1.,a=1.,ns=160,nt=96,nd=384,left=-10.,right=4.):
    if not np.isfinite([A,lam,h,eps,a,left,right]).all():
        raise ValueError('All parameters must be finite.')
    if not (A != 0 and eps > 0 and a > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
        raise ValueError('Require A nonzero, epsilon,a positive and the admissible hbar strip.')
    if any(not isinstance(n,int) or isinstance(n,bool) for n in [ns,nt,nd]):
        raise ValueError('Quadrature counts must be integers.')
    if min(ns,nd) < 16 or nt < 8 or left >= right:
        raise ValueError('Invalid quadrature settings.')
    theta=2*np.pi*np.arange(nt)/nt
    delta,dw=leggauss(nd);delta*=np.pi;dw/=2*nt
    th=np.repeat(theta,nd);ph=(theta[:,None]+delta[None,:]).reshape(-1)
    aw=np.tile(dw,nt)
    widths,b,la,_,_=single.sources(A,lam,h,th)
    _,c,lc,_,_=single.sources(A,lam,h,ph)
    V0=np.diag(1/(4*widths));cl0=2.5*np.log(np.pi)-.5*np.linalg.slogdet(2*np.diag(widths))[1]
    # Divide all transverse kernels by the common unprojected transverse norm.
    _,bzero,lazero,_,_=single.sources(A,lam,h,[0.])
    logbase=cl0+np.sum(bzero.real*(bzero.real/(2*widths)),axis=-1)[0]+2*lazero[0]
    lin=b.conj()+c;mu=lin@V0
    K0=np.exp(cl0+.5*np.sum(lin*mu,axis=-1)+la+lc-logbase)
    exact=np.exp(-A*A/(4*abs(h))*(1-np.cos(ph-th)))
    kernel_error=float(np.max(abs(K0-exact)))
    kinetic=np.zeros_like(K0)
    dirs=np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]])
    for d in dirs:
        row=-2*widths*d;mr=mu@row
        kinetic+=h*h*((b.conj()@d+mr)*(c@d+mr)+row@V0@row)
    normal=np.dot(aw,K0);kin=np.dot(aw,K0*kinetic)
    reference=float(i0e(A*A/(4*abs(h))))
    overlap_error=float(abs(normal-reference)/reference)
    if overlap_error > 5e-10:
        raise ArithmeticError(f'Underresolved charge projection: relative norm error {overlap_error:.6g}')
    assert kernel_error < 2e-9
    nodes,weights=leggauss(ns);nodes=left+(nodes+1)*(right-left)/2;weights*=(right-left)/2
    F=np.array([0.,0.,1.,1.,1.]);W=np.diag(widths)
    E=0j;R=0j;norm=0j;parts=np.zeros(5,complex)
    for s,ds in zip(nodes,weights):
        C=np.exp(s)+eps;chart=np.exp(s)+eps*s;z=old.inverse_shift(s,eps,h);r=np.exp((z-s)/2)
        L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
        H=2*(L.T@W@L).real
        if np.linalg.eigvalsh(H)[0] <= 0:
            raise ArithmeticError('Shifted Gaussian quadratic form is not positive.')
        V=.5*np.linalg.inv(H)
        lin=(b@L).conj()+c@L;mu=lin@V
        K=np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+.5*np.sum(lin*mu,axis=-1)+la+lc-logbase)
        fm=mu@F;fv=F@V@F
        f2=fm*fm+fv;f4=fm**4+6*fm*fm*fv+3*fv*fv
        vac=np.dot(aw,K);linear=np.dot(aw,K*f2);quartic=np.dot(aw,K*f4)
        growing=vac+linear/2+quartic/4
        zg=ds*C*np.exp(-2*s-2*a*(chart*chart-h*h/4))
        zi=ds*C*C*np.exp(-2*s-2*a*chart*chart)
        factor=2*(np.exp(z)/(2*(np.exp(z)+eps)**2)-1/(np.exp(z)+eps)-2*a*(chart-.5j*h)).real
        static=.5*(C*normal+kin/C)
        sr=.5*(-np.exp(s)/C*normal+kin*np.exp(s)/C**3)
        E+=zg*growing+zi*static;R+=zg*growing*factor+zi*sr;norm+=zi*normal
        parts+=np.array([zg*vac,zg*linear/2,zg*quartic/4,zi*static,zg*growing*factor])
    result=dict(E=float(E.real),R=float(R.real),ratio=float(R.real/E.real),norm_over_E=float(norm.real/E.real),
                parts_over_E=(parts.real/E.real).tolist(),kernel_error=kernel_error,
                projection_norm=float(normal.real),projection_norm_reference=reference,projection_norm_relative_error=overlap_error,
                imaginary_error=float(max(abs(E.imag),abs(R.imag),abs(normal.imag),abs(kin.imag))/max(1.,abs(E),abs(R))))

    assert E.real > 0 and norm.real > 0
    assert result['imaginary_error'] < 2e-10
    assert abs(sum(result['parts_over_E'][:4])-1) < 2e-10
    assert all(np.isfinite(v).all() for v in result.values())
    return result


def independent_check():
    """Absolute-angle torus grid, recursive moments and direct static pairing.

    Independent of the difference-angle grid, explicit quartic moment
    polynomial and static integration-by-parts recipe in projected().
    The inverse chart and source helper are shared and checked separately
    by the predecessor probe; this is not an independent certification.
    """
    A,lam,h,eps,a=1.,.4,.3,1.,1.
    nt,ns=64,160
    theta=2*np.pi*np.arange(nt)/nt
    widths,b,la,_,_=single.sources(A,lam,h,theta)
    amp=np.exp(la)
    Z0,_,V0,m0=old.gaussian_gram(b,amp,widths,np.eye(5))
    base=Z0[0,0].real
    kinetic=np.zeros_like(Z0)
    for d in np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]]):
        row=-2*widths*d;constant=b@d
        kinetic+=h*h*(constant.conj()[:,None]*constant[None,:]+
            (constant.conj()[:,None]+constant[None,:])*m0(row)+m0(row,row))
    nodes,weights=leggauss(ns);nodes=-10+(nodes+1)*7;weights*=7
    F=np.array([0.,0.,1.,1.,1.]);energy=0j;response=0j
    for s,ds in zip(nodes,weights):
        C=np.exp(s)+eps;chart=np.exp(s)+eps*s
        z=old.inverse_shift(s,eps,h);r=np.exp((z-s)/2)
        L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
        Z,_,_,moment=old.gaussian_gram(b,amp,widths,L)
        zi=C*C*np.exp(-2*s-2*a*chart*chart)
        zg=C*np.exp(-2*s-2*a*(chart*chart-h*h/4))
        static=zi*.5*(C+kinetic/C)*Z0
        growing=zg*Z*(1+moment(F,F)/2+moment(F,F,F,F)/4)
        direct_static=2*(np.exp(s)/(2*C*C)-1/C-2*a*chart)
        factor=2*(np.exp(z)/(2*(np.exp(z)+eps)**2)-1/(np.exp(z)+eps)-2*a*(chart-.5j*h)).real
        energy+=ds*np.mean(static+growing)/base
        response+=ds*np.mean(direct_static*static+factor*growing)/base
    candidate=projected(A=A,lam=lam,h=h,ns=ns,nt=nt,nd=160)
    errors=dict(energy=abs(energy-candidate['E'])/abs(energy),
                response=abs(response-candidate['R'])/abs(response))
    assert max(errors.values()) < 2e-10
    return dict(parameters=dict(A=A,lam=lam,h=h,eps=eps,a=a),ns=ns,nt=nt,
                absolute_angle_energy=float(energy.real),absolute_angle_response=float(response.real),
                difference_angle_result=candidate,relative_errors=errors)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    np.seterr(over='raise',invalid='raise',divide='raise')
    checks=independent_check()
    try:
        projected(ns=160,nt=96,nd=256)
    except ArithmeticError as exc:
        alias_rejection=str(exc)
        assert alias_rejection.startswith('Underresolved charge projection:')
    else:
        raise AssertionError('Expected the known underresolved grid to be rejected.')
    print('Independent torus calculation and underresolved-grid rejection passed.',flush=True)
    settings=[dict(ns=160,nt=96,nd=768,left=-10.,right=4.),
              dict(ns=240,nt=160,nd=1024,left=-12.,right=4.5),
              dict(ns=360,nt=224,nd=1280,left=-14.,right=5.)]
    parameters=dict(A=10.,lam=4.,eps=1.,a=1.)
    hbars=[.01,-.01,.05];runs=[]
    for setting in settings:
        start=time.monotonic()
        values=[dict(h=h,**projected(h=h,**parameters,**setting)) for h in hbars]
        runs.append(dict(quadrature=setting,values=values,seconds=time.monotonic()-start))
        print(json.dumps(dict(quadrature=setting,response_over_energy=[v['ratio'] for v in values])),flush=True)
    refinements=[]
    for previous,current in zip(runs,runs[1:]):
        for before,after in zip(previous['values'],current['values']):
            changes={k:abs(after[k]-before[k])/max(1.,abs(after[k])) for k in ['E','R','ratio','norm_over_E']}
            refinements.append(dict(h=after['h'],changes=changes))
    assert max(max(r['changes'].values()) for r in refinements) < 2e-8
    sign_errors=[abs(r['values'][0]['ratio']-r['values'][1]['ratio']) for r in runs]
    assert max(sign_errors)<2e-10
    # A regression check for this candidate, not a certified negative integral.
    assert all(v['ratio']<-.01 for r in runs for v in r['values'])
    root=Path(__file__).resolve().parents[1]
    files=['scripts/zero_charge_response_probe.py','scripts/matter_energy_gram_probe.py',
           'scripts/displaced_signed_response_probe.py',
           'UnifiedTheory/Audit/KFCausalDisplacedQuarticTestFamily.lean',
           'UnifiedTheory/Audit/KFCausalDisplacedQuarticOrbitPhase.lean',
           'UnifiedTheory/Audit/KFCausalPureClockZeroProjection.lean',
           'UnifiedTheory/Audit/KFCausalZeroChargeStructuredResponse.lean',
           'data/displaced_structured_response_audit.json']
    report=dict(kind='Exploratory floating-point projection quadrature; sign not certified',
        parameters=parameters,physical_time=0.,couplings=dict(mass2=1.,quartic=1.,vacuum=1.),
        hbar=hbars,checks=checks,underresolved_grid_rejection=alias_rejection,
        runs=runs,refinements=refinements,hbar_sign_errors=sign_errors,
        normalization='E and R use the same common transverse unprojected norm divisor; ratio R/E is independent of this divisor and of unit normalization of the nonzero projected state.',
        parts_over_E_order=['vacuum_energy','mass_energy','quartic_energy','static_energy','matter_plus_vacuum_response'],
        overlap_oracle='K(theta,phi)=exp(-nu*(1-cos(phi-theta))), nu=A^2/(4*abs(h)); its double-circle mean is exp(-nu)*I0(nu). Checked numerically, not formalized here.',
        source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files},
        limitations=['No interval enclosure of clock tails or quadrature error; no certified sign.',
            'Lean proves projected domains, phase and response identities, but not this full numerical transcription.',
            'No Lean nonzero or unit-normalization theorem for this specific projected test state is added.',
            'The response has no proved identification with a Hamiltonian evolution derivative.',
            'Finite negative quotients do not refute a finite state-uniform lower bound or prove clock failure.',
            'The zero-charge constraint remains a model input; no microscopic sector selection is derived.',
            'No model revision, regulator limit or physical TOE follows.'])
    text=json.dumps(report,indent=2,allow_nan=False)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
        print(args.output,flush=True)
    else:
        print(text)


if __name__=='__main__':
    main()
