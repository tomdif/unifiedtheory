#!/usr/bin/env python3
"""Test the signed response on full complex spans of displaced Gaussians.

No rank truncation, no certified quadrature, and no state-uniform bound.
Seeds are [A,lam,p], with the displaced Q/P orbit from the single-state
probe and clock modulation exp(i*p*s). Each seed has the same raw norm;
common unit-state normalization cancels in every generalized quotient.
All couplings and the physical time are 1,1,1 and 0 respectively.

A0/A1 are the candidate extension of the transported-initial polynomial
norms to this displaced span. The older coherent-span initial-map theorem
does not itself prove that extension. H0/H1 are terminal derivative moments.
Their separate maxima are diagnostics, not a lower bound on the response.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import displaced_signed_response_probe as single
import matter_energy_gram_probe as old
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh


def forms(seeds,h=.01,eps=1.,a=1.,ns=160,nt=96,left=-10.,right=4.):
    seeds=np.asarray(seeds,float)
    if seeds.ndim != 2 or seeds.shape[1] != 3 or len(seeds)==0 or not np.isfinite(seeds).all():
        raise ValueError('Expected a nonempty finite list of [A,lam,p] seeds.')
    if np.any(seeds[:,0]==0) or not (eps>0 and a>0 and 0<abs(h)<=2*np.pi*eps/3):
        raise ValueError('Require nonzero A,h and admissible positive clock parameters.')
    if ns<16 or nt<8 or not left<right:
        raise ValueError('Invalid quadrature settings.')
    A,lam,p=seeds.T; n=len(A)
    widths=np.array([1.,1.,1.,1.,1/32])/(2*abs(h)); W=np.diag(widths)
    nodes,weights=leggauss(ns); nodes=left+(nodes+1)*(right-left)/2; weights*=(right-left)/2/nt
    field=np.array([0.,0.,1.,1.,1.]); dirs=np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]])
    cache=[]
    for s,ds in zip(nodes,weights):
        C=np.exp(s)+eps;chart=np.exp(s)+eps*s;z=old.inverse_shift(s,eps,h);r=np.exp((z-s)/2)
        L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
        H=2*(L.T@W@L).real;V=.5*np.linalg.inv(H)
        assert np.linalg.eigvalsh(H)[0]>0
        base=np.exp(z)/(2*(np.exp(z)+eps)**2)-1/(np.exp(z)+eps)-2*a*(chart-.5j*h)
        f=base+1j*p/(np.exp(z)+eps)
        cache.append((s,ds,C,chart,z,L,V,2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1],f))
    out={k:np.zeros((n,n),complex) for k in ['E','R','N','V','Q','L','static','matter','A0','A1','H0','H1']}
    V0=np.diag(1/(4*widths));c0=2.5*np.log(np.pi)-.5*np.linalg.slogdet(2*W)[1]
    for theta in 2*np.pi*np.arange(nt)/nt:
        Q=np.zeros((n,5));P=np.zeros_like(Q)
        Q[:,2]=Q[:,3]=A*np.cos(theta)/2;Q[:,4]=A
        P[:,2]=A*np.sin(theta)/2;P[:,3]=-P[:,2];P[:,4]=-lam/A
        b=2*widths*Q+1j*P/h;la=-np.sum(widths*Q*Q,axis=1)
        lin=b.conj()[:,None,:]+b[None,:,:];mu=lin@V0
        l0=c0+.5*np.sum(lin*mu,axis=-1)+la[:,None]+la[None,:]
        kinetic=np.zeros((n,n),complex)
        for d in dirs:
            row=-2*widths*d
            murow=mu@row
            kinetic+=h*h*((b.conj()@d)[:,None]+murow)*((b@d)[None,:]+murow)+h*h*(row@V0@row)
        for s,ds,C,chart,z,L,V,cl,f in cache:
            B=b@L;lin=B.conj()[:,None,:]+B[None,:,:];mu=lin@V
            lZ=cl+.5*np.sum(lin*mu,axis=-1)+la[:,None]+la[None,:]
            Z=np.exp(np.log(ds)+np.log(C)-2*s-2*a*(chart*chart-h*h/4)+lZ+1j*(p[None,:]*z-p[:,None]*z.conjugate()))
            fm=mu@field;fv=field@V@field
            F2=fm*fm+fv;F4=fm**4+6*fm*fm*fv+3*fv*fv
            Z0=np.exp(np.log(ds)+2*np.log(C)-2*s-2*a*chart*chart+l0+1j*s*(p[None,:]-p[:,None]))
            st=.5*(C+kinetic/C);sr=.5*(-np.exp(s)/C+kinetic*np.exp(s)/C**3)
            rate=f.conj()[:,None]+f[None,:]
            matter=Z*(F2/2+F4/4)
            out['N']+=Z0;out['V']+=Z;out['Q']+=Z*F4;out['L']+=Z*F2
            out['static']+=Z0*st;out['E']+=Z0*st+matter+Z
            out['matter']+=matter*rate;out['R']+=Z0*sr+(matter+Z)*rate
            delta=z-s
            Qi=np.array([0.,0.,1.,1.,0.]);Pi=(3*np.exp(-delta/2)-2)*Qi.astype(complex);Pi[4]=1
            mi=(b.conj()[:,None,:]+b[None,:,:])@V0
            mP=mi@Pi; mPc=mi@Pi.conj(); cov=Pi.conj()@V0@Pi
            vp=Pi@V0@Pi;vpc=Pi.conj()@V0@Pi.conj()
            i2=mPc*mP+cov
            i4=mPc*mPc*mP*mP+vpc*mP*mP+vp*mPc*mPc+4*cov*mPc*mP+vpc*vp+2*cov*cov
            Zinit=np.exp(np.log(ds)+np.log(C)-2*s-2*a*(chart*chart-h*h/4)+l0-2*delta.real+1j*(p[None,:]*z-p[:,None]*z.conjugate()))
            out['A0']+=Zinit*i2;out['A1']+=Zinit*i4
            mq=mu@Qi;vq=Qi@V@Qi;cfq=field@V@Qi
            fq=fm*fm*mq*mq+fv*mq*mq+vq*fm*fm+4*cfq*fm*mq+fv*vq+2*cfq*cfq
            D=eps/C
            out['H0']+=D**5*(1-D)*2.25*Z*(mq*mq+vq)
            out['H1']+=D**5*(1-D)*9*Z*fq
    anti={k:float(np.linalg.norm(M-M.conj().T)/max(1.,np.linalg.norm(M))) for k,M in out.items()}
    assert max(anti.values())<2e-12,anti
    assert all(np.isfinite(M).all() for M in out.values())
    out={k:(M+M.conj().T)/2 for k,M in out.items()}
    return out


def spectral(out):
    W,conditioning=old.whitening(out['E'])
    if conditioning['whitening_residual']>2e-8:
        raise ValueError('Unresolved energy whitening; no modes discarded.')
    transformed={k:W.conj().T@M@W for k,M in out.items()}
    R=transformed['R']; values,U=eigh((R+R.conj().T)/2)
    witness=W@U[:,0]
    quotient=lambda M: float((witness.conj()@M@witness).real/(witness.conj()@out['E']@witness).real)
    maxima={}
    for k in ['A0','A1','H0','H1']:
        M=transformed[k]; maxima[k]=float(eigh((M+M.conj().T)/2,eigvals_only=True)[-1])
    return dict(minimum=float(values[0]),maximum=float(values[-1]),conditioning=conditioning,
                witness=witness,witness_quotient=quotient(out['R']),
                witness_norm_over_energy=quotient(out['N']),separate_cost_maxima=maxima)


def recursive_reference(seeds,h=.3,ns=128,nt=48,left=-10.,right=4.):
    """Independent recursive Gaussian moments, including complex cross terms.

    Static response is evaluated as a direct weak pairing here, rather than
    the integration-by-parts formula used by the main implementation.
    This reference is restricted to modest sources to avoid overflow.
    """
    seeds=np.asarray(seeds); A,lam,p=seeds.T; n=len(A)
    widths=np.array([1.,1.,1.,1.,1/32])/(2*abs(h))
    F=np.array([0.,0.,1.,1.,1.]); Q=F.copy();Q[4]=0
    dirs=np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]])
    out={k:np.zeros((n,n),complex) for k in ['E','R','N','V','Q','L','static','matter','A0','A1','H0','H1']}
    nodes,weights=leggauss(ns);nodes=left+(nodes+1)*(right-left)/2;weights*=(right-left)/2/nt
    for theta in 2*np.pi*np.arange(nt)/nt:
        centres=np.zeros((n,5));momenta=np.zeros_like(centres)
        centres[:,2]=centres[:,3]=A*np.cos(theta)/2;centres[:,4]=A
        momenta[:,2]=A*np.sin(theta)/2;momenta[:,3]=-momenta[:,2];momenta[:,4]=-lam/A
        b=2*widths*centres+1j*momenta/h;amp=np.exp(-np.sum(widths*centres**2,axis=1))
        Z0,mu0,V0,m0=old.gaussian_gram(b,amp,widths,np.eye(5))
        kin=np.zeros((n,n),complex)
        for d in dirs:
            row=-2*widths*d;v=b@d
            kin+=h*h*(v.conj()[:,None]*v[None,:]+(v.conj()[:,None]+v[None,:])*m0(row)+m0(row,row))
        for s,ds in zip(nodes,weights):
            C=np.exp(s)+1;chart=np.exp(s)+s;z=old.inverse_shift(s,1.,h);delta=z-s;r=np.exp(delta/2)
            L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
            Z,mu,V,m=old.gaussian_gram(b,amp,widths,L)
            ci=C*np.exp(-s-chart*chart)*np.exp(1j*p*s)
            cg=np.sqrt(C)*np.exp(-s-(chart-.5j*h)**2)*np.exp(1j*p*z)
            pairi=ci.conj()[:,None]*ci[None,:]*Z0
            pairg=cg.conj()[:,None]*cg[None,:]*Z
            pairinit=np.exp(-2*delta.real)*cg.conj()[:,None]*cg[None,:]*Z0
            Cz=np.exp(z)+1
            f=np.exp(z)/(2*Cz*Cz)-1/Cz-2*(chart-.5j*h)+1j*p/Cz
            fi=np.exp(s)/(2*C*C)-1/C-2*chart+1j*p/C
            rate=f.conj()[:,None]+f[None,:]
            linear=pairg*m(F,F); quartic=pairg*m(F,F,F,F)
            static=pairi*.5*(C+kin/C);matter=linear/2+quartic/4
            P=(3*np.exp(-delta/2)-2)*Q.astype(complex);P[4]=1;D=1/C
            vals=dict(E=static+matter+pairg,R=static*(fi.conj()[:,None]+fi[None,:])+(matter+pairg)*rate,
                      N=pairi,V=pairg,Q=quartic,L=linear,static=static,matter=matter*rate,
                      A0=pairinit*m0(P.conj(),P),A1=pairinit*m0(P.conj(),P.conj(),P,P),
                      H0=D**5*(1-D)*2.25*pairg*m(Q,Q),H1=D**5*(1-D)*9*pairg*m(F,F,Q,Q))
            for k,M in vals.items():out[k]+=ds*M
    return out


def independent_checks():
    seeds=[[1.,.4,0.],[1.2,.7,1.3],[1.5,.9,-.7]]
    current=forms(seeds,h=.3,ns=128,nt=48)
    reference=recursive_reference(seeds)
    errors={k:float(np.linalg.norm(current[k]-reference[k])/max(1.,np.linalg.norm(reference[k]))) for k in current}
    assert max(errors.values())<2e-10,errors
    # Actual negative candidate: a separate implementation of all diagonal forms.
    seed=[10.,4.,0.]; setting=dict(ns=160,nt=128)
    gram=forms([seed],**setting)
    one=single.forms(A=seed[0],lam=seed[1],h=.01,**setting)
    E=gram['E'][0,0].real
    diag=dict(log_energy=abs(np.log(E)-one['logE']),response=abs(gram['R'][0,0].real/E-one['full_response']),
              quartic=abs(gram['Q'][0,0].real/E-one['quartic']),linear=abs(gram['L'][0,0].real/E-one['field']),
              vacuum=abs(gram['V'][0,0].real/E-one['vacuum']),static=abs(gram['static'][0,0].real/E-one['static']))
    assert max(diag.values())<2e-10,diag
    return dict(recursive_seeds=seeds,recursive_hbar=.3,recursive_matrix_errors=errors,
                negative_candidate_diagonal_errors=diag)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    np.seterr(over='raise',invalid='raise',divide='raise')
    checks=independent_checks()
    print('Independent recursive cross-term and negative-candidate diagonal checks passed.',flush=True)
    cases={'A_line_33':[[float(A),4.,0.] for A in np.linspace(8,12,33)],
           'lam_line_33':[[10.,float(l),0.] for l in np.linspace(1,7,33)],
           'clock_line_17':[[10.,4.,float(p)] for p in np.linspace(-30,30,17)]}
    reports=[]
    for name,seeds in cases.items():
        settings=[dict(ns=384 if name=='clock_line_17' else 192,nt=128,left=-10.,right=4.),
                  dict(ns=576 if name=='clock_line_17' else 320,nt=192,left=-12.,right=4.5)]
        matrices=[];values=[];witnesses=[]
        for setting in settings:
            start=time.monotonic();out=forms(seeds,**setting);value=spectral(out)
            c=value.pop('witness');witnesses.append(c);matrices.append(out)
            values.append(dict(quadrature=setting,seconds=time.monotonic()-start,**value,
                               witness_real=c.real.tolist(),witness_imag=c.imag.tolist()))
            print(json.dumps(dict(case=name,quadrature=setting,minimum=value['minimum'],
                energy_condition=value['conditioning']['normalized_energy_condition'])),flush=True)
        c=witnesses[0];refined=matrices[1]
        fixed=float((c.conj()@refined['R']@c).real/(c.conj()@refined['E']@c).real)
        changes={k:float(np.linalg.norm(matrices[0][k]-refined[k])/max(1.,np.linalg.norm(refined[k]))) for k in refined}
        assert max(changes.values())<2e-8,changes
        assert abs(fixed-values[0]['minimum'])<2e-8
        assert abs(values[1]['minimum']-values[0]['minimum'])<2e-8
        reports.append(dict(case=name,seeds=seeds,runs=values,refined_original_witness_quotient=fixed,
                            scaled_gram_changes=changes))
    root=Path(__file__).resolve().parents[1]
    files=['scripts/displaced_response_gram_probe.py','scripts/displaced_signed_response_probe.py',
           'scripts/matter_energy_gram_probe.py','data/displaced_signed_response_probe.json',
           'data/displaced_matter_response_audit.json']
    report=dict(kind='Exploratory complex Gram quadrature; not a certified sign or uniform bound',
                parameters=dict(eps=1.,a=1.,h=.01,time=0.,mass2=1.,quartic=1.,vacuum=1.),
                seed_recipe='[A,lam,p]; Q/P as in displaced_signed_response_probe, multiplied by exp(i*p*s).',
                normalization='Each witness has energy one in its own computed Gram form. All complex interference retained; no rank truncation.',
                source_sha256={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files},
                checks=checks,cases=reports,
                limitations=['No certified quadrature or clock-tail bound.',
                             'Negative finite generalized eigenvalues do not refute every finite one-sided lower energy bound.',
                             'A0/A1 numerically extend the initial polynomial recipe; the coherent-span theorem does not itself establish the displaced-span operator identification.',
                             'Separate cost maxima are attained by potentially different vectors; they are not the signed response.',
                             'No Hamiltonian evolution derivative, clock escape, model change or physical TOE follows.'])
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(args.output,flush=True)
    else:print(json.dumps(report,indent=2,allow_nan=False))


if __name__=='__main__':
    main()

