#!/usr/bin/env python3
"""Positive spectral pole, observer resolution, and an asinh metric chart."""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.integrate import quad
from scipy.special import erfc, gamma, logsumexp
from numpy.polynomial.hermite import hermgauss
import sympy as sy

from ultraviolet_metric_control_audit import stf_basis


RNG=np.random.default_rng(9112761)


def logcosh(x):return np.logaddexp(x,-x)-np.log(2.)


def matrix_function(h,func):
    eig,v=la.eigh(h)
    return (v*func(eig))@v.conj().T


def metric(h,g):return matrix_function(h,lambda x:np.exp(2*np.arcsinh(g*x/2)))


def exact_identities():
    x,g=sy.symbols('x g',real=True,positive=True)
    q=(sy.sqrt(1+g*g*x*x/4)+g*x/2)**2
    qi=(sy.sqrt(1+g*g*x*x/4)-g*x/2)**2
    assert sy.simplify(q*qi-1)==0
    assert sy.simplify(q+qi-2-g*g*x*x)==0
    assert sy.expand(sy.series(2*sy.asinh(g*x/2),g,0,5).removeO())==g*x-g**3*x**3/24
    a,b,u,v,r,s=sy.symbols('a b u v r s',real=True)
    gram=a*sy.Matrix([u,v])*sy.Matrix([[u,v]])-b*sy.Matrix([r,s])*sy.Matrix([[r,s]])
    assert sy.expand(gram.det()+a*b*(u*s-v*r)**2)==0
    return dict(asinh_metric_inverse=True,two_sided_moment_identity='Q+Q^(-1)=2I+g^2 H^2',
                logarithmic_chart='gH-g^3 H^3/24+O(g^5)',
                signed_spectral_reflection_determinant='-a*b*(u*s-v*r)^2',
                nonGaussian_moment_bound='E(exp X) E(exp -X)>=cosh(sqrt(2 Var X))')


def non_gaussian_tests():
    out=[];basis=stf_basis()
    for count in [3,7,15]:
        weights=RNG.uniform(.1,1,size=count);weights/=sum(weights)
        matrices=np.einsum('sa,aij->sij',RNG.normal(size=(count,5)),basis)
        for g in [.2,.7,1.4]:
            values=g*matrices[:,0,0]
            variance=float(weights@(values*values)-(weights@values)**2)
            logproduct=logsumexp(np.log(weights)+values)+logsumexp(np.log(weights)-values)
            lower=logcosh(np.sqrt(2*variance))
            q=sum((w*la.expm(g*h) for w,h in zip(weights,matrices)),np.zeros((3,3)))
            qi=sum((w*la.expm(-g*h) for w,h in zip(weights,matrices)),np.zeros((3,3)))
            matrix_logproduct=np.log(q[0,0]*qi[0,0])
            assert logproduct>=lower-1e-13 and matrix_logproduct>=logproduct-1e-13
            out.append(dict(distribution_atoms=count,coupling=g,component_variance=variance,
                            scalar_log_moment_product=float(logproduct),lower_log_bound=float(lower),
                            matrix_log_moment_product=float(matrix_logproduct)))
    return out


def tail_tests():
    out=[]
    for n in [2.,4.,8.,16.]:
        values=np.array([0.,n*n,-n*n]);weights=np.array([1-1/n**2,1/(2*n*n),1/(2*n*n)])
        variance=weights@(values*values)
        logproduct=2*logsumexp(np.log(weights)+values)
        assert variance==n*n and logproduct>=logcosh(np.sqrt(2*variance))-1e-12
        out.append(dict(model='rare_tail',scale=n,variance=float(variance),probability_nonzero=1/n**2,
                        log_exponential_moment_product=float(logproduct),
                        scope='Divergent variance need not imply divergence in probability; no Lorentzian QFT is claimed for this probability example'))
    for lower in [2.,4.,8.,12.]:
        # For X=Z^3, integrate exp(g Z^3) over [lower,lower+1].
        g=.5;logbound=g*lower**3-(lower+1)**2/2-np.log(2*np.pi)/2
        out.append(dict(model='Gaussian_cubed',integration_lower_endpoint=lower,
                        variance=15.,log_positive_tail_integral_lower_bound=logbound,
                        asinh_two_sided_scalar_mean=2+15*g*g,
                        scope='All polynomial moments finite, exponential moments infinite; divergence follows from the displayed analytical tail bound'))
    return out


def spectral_tests():
    out=[]
    for weights,masses in [(np.array([1.]),np.array([0.])),(np.array([.4,.2,.7]),np.array([0.,.5,2.])),
                           (np.array([.15,1.5]),np.array([0.,3.]))]:
        previous=None
        for cutoff in [2.,8.,32.]:
            x=cutoff*cutoff
            propagator=float(np.sum(weights/(x+masses*masses)))
            monotonic=float(np.sum(weights*masses*masses/(x+masses*masses)**2))
            def radial(m):
                if m==0:return cutoff*cutoff/2
                return .5*(cutoff*np.sqrt(cutoff*cutoff+m*m)-m*m*np.arcsinh(cutoff/m))
            exact=sum(w*radial(m) for w,m in zip(weights,masses))/(4*np.pi*np.pi)
            actual=quad(lambda k:sum(w*k*k/(2*np.sqrt(k*k+m*m)) for w,m in zip(weights,masses)),
                        0,cutoff,epsabs=1e-11,epsrel=1e-12)[0]/(2*np.pi*np.pi)
            bound=weights[0]*cutoff*cutoff/(8*np.pi*np.pi)
            assert abs(actual-exact)<1e-9 and exact>=bound-1e-12
            assert propagator>=weights[0]/x and monotonic>=0
            if previous is not None:assert x*propagator>=previous-1e-12
            previous=x*propagator
            out.append(dict(masses=masses.tolist(),weights=weights.tolist(),cutoff=cutoff,
                            scalar_equal_time_variance=exact,pole_variance_lower_bound=bound,
                            euclidean_xD=x*propagator,derivative_xD=monotonic,
                            scope='Positive scalar spectral examples; the tensor pole bound is proved separately with its TT angular factor'))
    return out


def reflection_tests():
    out=[]
    for ell in [.5,1.,2.]:
        for k in [.4,.7,1.2]:
            times=ell*np.array([.1,.3]);t=times[:,None]+times[None,:]
            matrix=(np.exp(-k*t)*erfc(k*ell-t/(2*ell))+np.exp(k*t)*erfc(k*ell+t/(2*ell)))/(4*k)
            eigen=la.eigvalsh(matrix)
            assert eigen[0]<-1e-8
            # Independent frequency integral for each entry.
            direct=np.array([[quad(lambda w:np.cos(w*s)*np.exp(-ell*ell*(w*w+k*k))/(w*w+k*k),
                                  0,np.inf,epsabs=2e-12)[0]/np.pi for s in row] for row in t])
            assert la.norm(matrix-direct)<3e-11
            out.append(dict(model='exponential_Euclidean_damping',length=ell,spatial_momentum=k,
                            reflected_Gram_eigenvalues=eigen.tolist(),integral_comparison=la.norm(matrix-direct),
                            scope='Reflection-positivity test of this Euclidean covariance as written, not every nonlocal theory'))
    k=.7;times=np.array([.2,.6]);t=times[:,None]+times[None,:]
    for mass in [1.,2.,4.]:
        omega=np.sqrt(k*k+mass*mass)
        a=np.exp(-k*t)/(2*k);b=np.exp(-omega*t)/(2*omega)
        negative=la.eigvalsh(a-b);positive=la.eigvalsh(a+b)
        assert negative[0]<-1e-7 and positive[0]>0
        out.append(dict(model='Pauli_Villars_comparison',mass=mass,
                        negative_weight_eigenvalues=negative.tolist(),positive_weight_eigenvalues=positive.tolist()))
    return out


def minkowski(a,b):return a[...,0]*b[...,0]-np.sum(a[...,1:]*b[...,1:],axis=-1)


def boost(speed):
    v=np.asarray(speed);gamma_=1/np.sqrt(1-v@v);result=np.eye(4)
    result[0,0]=gamma_;result[0,1:]=gamma_*v;result[1:,0]=gamma_*v
    result[1:,1:]+=(gamma_-1)*np.outer(v,v)/(v@v)
    return result


def observer_tests():
    out=[];ell=.4;tau=.25
    u=boost([.2,-.1,.15])[:,0]
    for speed in [.2,.6,.85]:
        transform=boost([speed,0,0])
        for mass in [0.,1.3]:
            spatial=RNG.normal(size=(80,3))
            p=np.column_stack([np.sqrt(np.sum(spatial*spatial,axis=1)+mass*mass),spatial])
            def exponent(p,u):
                energy=minkowski(p,u);s=minkowski(p,p)
                return -.5*(tau*tau*energy*energy+ell*ell*(energy*energy-s))
            original=exponent(p,u);changed=exponent(p@transform.T,transform@u)
            error=float(max(abs(original-changed)))
            assert error<3e-13 and abs(minkowski(u,u)-1)<1e-14
            out.append(dict(boost_speed=speed,mass=mass,observer_filter_error=error,
                            scope='Simultaneous Lorentz transformation of momentum and supplied observer; no preferred observer is selected'))
    return out


def resolved_spectral_tests():
    out=[];z=.4
    for ell,tau in [(.3,.2),(1.,.4),(.5,1.)]:
        a=ell*ell+tau*tau
        for power,weight in [(0,0.),(0,.1),(2,.005)]:
            integral=quad(lambda u:(a+u*u)**(-1.5)*(tau*tau+u*u)**(-power-1),
                          0,np.inf,epsabs=1e-11,epsrel=1e-11)[0]
            continuum=weight*gamma(power+1)*integral/(8*np.pi*np.pi)
            pole=z/(8*np.pi*np.pi*a)
            bound=(z+weight*gamma(power+1)/tau**(2*power+2))/(8*np.pi*np.pi*a)
            assert continuum>=0 and pole+continuum<=bound+1e-10
            out.append(dict(spatial_resolution=ell,temporal_resolution=tau,continuum_power=power,
                            continuum_weight=weight,resolved_scalar_variance=pole+continuum,
                            pole_lower_bound=pole,laplace_spectral_upper_bound=bound,
                            scope='Positive spectrum rho=Z delta_0+weight*s^power ds; spatial resolution alone need not control its mass continuum'))
    return out


def causal_tests():
    out=[];time=.4
    for a in [.04,.16]:
        for radius in [.6,1.2,2.]:
            exact=(np.exp(-(radius-time)**2/(4*a))-np.exp(-(radius+time)**2/(4*a)))/(8*np.pi**1.5*radius*np.sqrt(a))
            direct=quad(lambda k:np.sin(k*radius)*np.sin(k*time)*np.exp(-a*k*k),0,np.inf,
                        epsabs=1e-12)[0]/(2*np.pi*np.pi*radius)
            assert exact>0 and abs(exact-direct)<2e-12
            out.append(dict(resolution_squared=a,time=time,radius=radius,spacelike=True,
                            commutator_kernel=exact,integral_error=abs(exact-direct),
                            scope='Local massless scalar smeared with noncompact Gaussian measurement profiles; not a test of unsmeared graviton microcausality'))
    return out


def chart_tests():
    out=[]
    for d in [3,6]:
        raw=RNG.normal(size=(d,d))+1j*RNG.normal(size=(d,d));h=(raw+raw.conj().T)/2
        rotation=la.expm(.2j*(raw+raw.conj().T))
        for g in [.1,.5,1.,2.]:
            q=metric(h,g);qi=metric(-h,g)
            identity=la.norm(q+qi-2*np.eye(d)-g*g*h@h)
            product=la.norm(q@qi-np.eye(d))
            sqrtq=matrix_function(q,np.sqrt);sqrti=matrix_function(qi,np.sqrt)
            inverse=la.norm((sqrtq-sqrti)/g-h)
            covariance=la.norm(metric(rotation@h@rotation.conj().T,g)-rotation@q@rotation.conj().T)
            assert max(identity,product,inverse,covariance)<5e-10
            out.append(dict(matrix_dimension=d,coupling=g,two_sided_identity_error=identity,
                            inverse_product_error=product,global_chart_inverse_error=inverse,
                            unitary_covariance_error=covariance,minimum_metric_eigenvalue=float(la.eigvalsh(q)[0]),
                            scope='Dimension six also tests a self-adjoint matrix with operator-valued blocks; commuting metric entries are not inferred'))
    # Gaussian cubed: second moments suffice despite infinite exponential moments.
    nodes,weights=hermgauss(32);nodes*=np.sqrt(2);weights/=np.sqrt(np.pi)
    for g in [.2,1.]:
        q=np.exp(2*np.arcsinh(g*nodes**3/2));qi=1/q
        result=float(weights@(q+qi));target=2+15*g*g
        assert abs(result-target)<2e-11
        out.append(dict(model='Gaussian_cubed',coupling=g,two_sided_mean=result,exact_mean=target,
                        scope='Finite asinh-metric and inverse means for a non-Gaussian variable without exponential moments'))
    return out


def canonical_tests():
    basis=np.concatenate([np.eye(3)[None]/np.sqrt(3),stf_basis()]);out=[]
    symplectic=np.block([[np.zeros((6,6)),np.eye(6)],[-np.eye(6),np.zeros((6,6))]])
    for scale in [.2,1.5]:
        for g in [.4,1.2]:
            def mapping(state):
                h=np.einsum('a,aij->ij',state[:6],basis);e,v=la.eigh(h)
                values=2*np.arcsinh(g*e/2)
                diff=e[:,None]-e[None,:]
                divided=np.zeros((3,3))
                for i in range(3):
                    for j in range(3):
                        divided[i,j]=(values[i]-values[j])/diff[i,j] if abs(diff[i,j])>1e-10 else g/np.sqrt(1+(g*e[i]/2)**2)
                jac=np.empty((6,6))
                for j,axis in enumerate(basis):
                    derivative=v@(divided*(v.T@axis@v))@v.T
                    jac[:,j]=np.einsum('aij,ij->a',basis,derivative)
                coordinate=np.einsum('aij,ij->a',basis,(v*values)@v.T)
                return np.concatenate([coordinate,la.solve(jac.T,state[6:])])
            state=RNG.normal(size=12)*scale;step=2e-5
            jac=np.column_stack([(mapping(state+step*axis)-mapping(state-step*axis))/(2*step) for axis in np.eye(12)])
            residual=la.norm(jac@symplectic@jac.T-symplectic)
            assert residual<2e-8,residual
            out.append(dict(configuration_scale=scale,coupling=g,cotangent_symplectic_error=residual,
                            scope='Full six-coordinate canonical chart with all twelve phase-space outputs'))
    return out


def metric_convergence_tests():
    basis=stf_basis();g=.7;out=[];previous=None
    def h(z):return z**3*basis[0]+z*basis[2]
    def density(z):return np.exp(-z*z/2)/np.sqrt(2*np.pi)
    for cutoff in [1.5,2.,3.,4.]:
        error_squared=2*quad(lambda z:((z**3-cutoff**3)**2+(z-cutoff)**2)*density(z),
                             cutoff,np.inf,epsabs=1e-11,epsrel=2e-11)[0]
        qcut=metric(h(cutoff),g);icut=metric(-h(cutoff),g)
        actual=quad(lambda z:(la.norm(metric(h(z),g)-qcut)+la.norm(metric(-h(z),g)-icut))*density(z),
                    cutoff,np.inf,epsabs=1e-11,epsrel=2e-10)[0]
        # ||H||_L2=4 and clipping decreases its pointwise Frobenius norm.
        bound=g*np.sqrt(error_squared)*(2+8*g)
        assert actual<=bound+1e-9
        if previous is not None:assert actual<previous
        previous=actual
        out.append(dict(Gaussian_input_clip=cutoff,field_L2_error=np.sqrt(error_squared),
                        metric_and_inverse_L1_error=actual,analytical_L1_upper_bound=bound,
                        scope='Unbounded non-Gaussian matrix H=Z^3 E0+Z E2, with full Gaussian tail integration; not an interacting spin-field limit'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(exact_identities=exact_identities(),nonGaussian_moments=non_gaussian_tests(),tail_examples=tail_tests(),
                positive_spectra=spectral_tests(),reflection_positivity=reflection_tests(),observer_covariance=observer_tests(),
                resolved_spectra=resolved_spectral_tests(),measurement_commutators=causal_tests(),
                metric_chart=chart_tests(),canonical_pullback=canonical_tests(),metric_convergence=metric_convergence_tests())
    paths=['POSITIVE_SPECTRAL_METRIC.md','scripts/positive_spectral_metric_audit.py',
           'ULTRAVIOLET_METRIC_CONTROL.md','scripts/ultraviolet_metric_control_audit.py',
           'data/ultraviolet_metric_control_audit.json','AFFINE_SPIN_METRIC.md',
           'REDUCED_TENSOR_HAMILTONIAN.md','CANONICAL_METRIC_RECONSTRUCTION.md',
           'CLOCK_MEDIATED_CONSTRAINTS.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    report['scope']={'proved':'Conditional positive-pole non-Gaussian metric moment bound; observer-covariant linear resolution; global positive asinh metric with exact two-sided moment control',
                     'not_proved':['A local positive-metric graviton potential','Einstein diffeomorphism and clock algebra',
                                   'microscopic observer construction','interacting spin regulator removal','physical G','TOE'],
                     'qualification':'The metric chart and measurement family are supplied constructions. A coordinate change alone preserves the original physical difficulties.'}
    target=root/'data/positive_spectral_metric_audit.json';target.write_text(json.dumps(report,indent=2)+'\n')
    keys=['nonGaussian_moments','tail_examples','positive_spectra','reflection_positivity','observer_covariance',
          'resolved_spectra','measurement_commutators','metric_chart','canonical_pullback','metric_convergence']
    print('PASS: exact identities and',sum(len(report[k]) for k in keys),'numerical cases')
    print('Report:',target)


if __name__=='__main__':main()
