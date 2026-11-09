#!/usr/bin/env python3
"""Gaussian TT ultraviolet metric control and the clock cost of a smoother seed."""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.integrate import quad
from scipy.special import beta, expit, gammainc, i0
import sympy as sy


RNG=np.random.default_rng(9112753)


def stf_basis():
    ans=[np.diag([1.,-1.,0.])/np.sqrt(2),np.diag([1.,1.,-2.])/np.sqrt(6)]
    for i,j in [(0,1),(0,2),(1,2)]:
        e=np.zeros((3,3));e[i,j]=e[j,i]=1/np.sqrt(2);ans.append(e)
    return np.array(ans)


def exact_identities():
    mu,k,p,m=sy.symbols('mu k p M',real=True)
    average=sy.integrate((1-mu*mu)**2/4,(mu,-1,1))
    assert average==sy.Rational(4,15)
    defect=sy.expand((k**8-k**4*(k+p)**4)/m**6)
    assert defect.coeff(p,1)==-4*k**7/m**6
    speed=sy.simplify(-defect.coeff(p,1)/k)
    assert speed==4*k**6/m**6
    return dict(TT_diagonal_angular_average=str(average),
                free_diagonal_variance='hbar*Lambda^2/(30*pi^2*c)',
                metric_inverse_moment_product_lower_bound='exp(g^2*hbar*Lambda^2/(30*pi^2*c))',
                high_derivative_clock_defect=str(defect),
                extra_inferred_metric_coefficient=str(speed))


def angular_tests():
    out=[];basis=stf_basis()
    for order in [4,8,16]:
        mu,weight=np.polynomial.legendre.leggauss(order)
        angle=2*np.pi*np.arange(2*order+1)/(2*order+1)
        directions=np.stack(np.broadcast_arrays(np.sqrt(1-mu[:,None]**2)*np.cos(angle),
                            np.sqrt(1-mu[:,None]**2)*np.sin(angle),mu[:,None]),axis=-1)
        project=np.eye(3)-directions[...,None]*directions[...,None,:]
        transformed=np.einsum('...ij,ajk,...kl->...ail',project,basis,project)
        trace=np.einsum('...ij,aji->...a',project,basis)
        transformed-=.5*trace[...,None,None]*project[...,None,:,:]
        representation=np.einsum('aij,...bij->...ab',basis,transformed)
        averaged=np.einsum('u,uvab->ab',weight,representation)/(2*len(angle))
        error=la.norm(averaged-.4*np.eye(5))
        assert error<2e-14
        assert np.max(abs(np.trace(representation,axis1=-2,axis2=-1)-2))<3e-14
        out.append(dict(polar_order=order,azimuth_points=len(angle),isotropic_STF_covariance_error=error,
                        diagonal_angular_average=float(basis[:,0,0]@averaged@basis[:,0,0])))
    return out


def radial_integral(cutoff,z):
    if z==1:return cutoff*cutoff/2
    return quad(lambda k:k/np.sqrt(1+k**(2*(z-1))),0,cutoff,epsabs=2e-12,epsrel=2e-12)[0]


def radial_tests():
    out=[]
    for z in [1,2,3,4,8]:
        target=beta(1/(z-1),.5-1/(z-1))/(2*(z-1)) if z>3 else None
        for cutoff in [2.,4.,8.,16.,32.]:
            result=radial_integral(cutoff,z)
            exact=None
            if z==1:exact=cutoff**2/2
            if z==2:exact=np.sqrt(1+cutoff*cutoff)-1
            if z==3:exact=.5*np.arcsinh(cutoff*cutoff)
            if exact is not None:assert abs(result-exact)<1e-10
            tail=None
            if z>3:
                tail=cutoff**(3-z)/(z-3)
                assert target-result>=-2e-12 and target-result<=tail+2e-12
                assert target-result>=tail/np.sqrt(2)-2e-12
            out.append(dict(ultraviolet_exponent=z,cutoff=cutoff,radial_integral=result,
                            TT_diagonal_variance=result/(15*np.pi*np.pi),
                            infinite_radial_integral=target,tail_upper_bound=tail,
                            scope='Infinite-volume radial Gaussian covariance; c=hbar=M=1'))
    return out


def point_metric_tests():
    basis=stf_basis();draws=RNG.normal(size=(40000,5))
    base=np.einsum('sa,aij->sij',draws,basis)
    eig=np.linalg.eigvalsh(base);radii=la.norm(draws,axis=1)
    ranges=eig[:,-1]-eig[:,0]
    assert np.min(ranges-np.sqrt(1.5)*radii)>-2e-13
    out=[];previous_endpoint=None
    for cutoff in [2.,4.,8.,16.,32.,64.,128.]:
        sigma=cutoff/np.sqrt(20*np.pi*np.pi)
        v11=cutoff*cutoff/(30*np.pi*np.pi)
        log_condition=sigma*ranges
        threshold=np.log(100.)/(np.sqrt(1.5)*sigma)
        upper=float(gammainc(2.5,threshold*threshold/2))
        observed=float(np.mean(log_condition<=np.log(100.)))
        # Pointwise event inclusion is exact; population CDF is an analytical bound.
        assert np.all((log_condition>np.log(100.)) | (radii<=threshold+2e-12))
        assert observed<=upper+.01
        normalized_log_max=sigma*eig[:,-1]-v11/2
        bounded_eigenvalues=expit(sigma*eig)
        endpoint_defect=float(np.mean(np.sum(bounded_eigenvalues*(1-bounded_eigenvalues),axis=1)))
        assert np.max(abs(bounded_eigenvalues+expit(-sigma*eig)-1))<3e-16
        if previous_endpoint is not None:assert endpoint_defect<previous_endpoint
        previous_endpoint=endpoint_defect
        out.append(dict(cutoff=cutoff,diagonal_variance=v11,
                        log_moment_product_lower_bound=v11,
                        median_log_condition=float(np.median(log_condition)),
                        fraction_condition_below_100=observed,chi_squared_probability_upper_bound=upper,
                        normalized_upper_metric_log_95th_percentile=float(np.quantile(normalized_log_max,.95)),
                        bounded_metric_endpoint_defect=endpoint_defect,
                        scope='Exact isotropic five-dimensional one-point TT law; empirical quantiles, not Monte Carlo estimates of rare-event means'))
    assert out[-1]['normalized_upper_metric_log_95th_percentile']<0
    return out


def momentum_tests():
    out=[]
    for z in [1,4]:
        for cutoff in [4.,8.,16.,32.]:
            integrand=(lambda k:k**3) if z==1 else (lambda k:k**3*np.sqrt(1+k**6))
            integral=quad(integrand,0,cutoff,epsabs=2e-10,epsrel=2e-12)[0]
            variance=integral/(15*np.pi*np.pi)
            coordinate=radial_integral(cutoff,z)/(15*np.pi*np.pi)
            bound=cutoff**6/(2025*np.pi**4)
            assert coordinate*variance>=bound-2e-12
            if z==1:assert abs(variance-cutoff**4/(60*np.pi*np.pi))<1e-10
            out.append(dict(ultraviolet_exponent=z,cutoff=cutoff,momentum_diagonal_variance=variance,
                            coordinate_diagonal_variance=coordinate,variance_product_lower_bound=bound,
                            mean_subtracted_momentum_square_variance=2*variance*variance,
                            scope='Exact Gaussian covariance integrals; scalar normal ordering removes the mean, not the variance'))
    return out


def frame_tests():
    basis=stf_basis();out=[]
    a=la.expm(np.array([[.2,.13,0],[-.07,-.1,.11],[.02,0,.05]]))
    condition_a=np.linalg.cond(a)
    for cutoff in [2.,4.,8.]:
        error=0.;smallest_jensen=1.
        for _ in range(80):
            h=np.einsum('a,aij->ij',RNG.normal(size=5),basis)*cutoff/np.sqrt(20*np.pi*np.pi)
            q=la.expm(h);inverse=la.expm(-h)
            conformal=np.exp(.4*RNG.normal())
            changed=conformal*a@q@a.T
            assert np.linalg.cond(changed)>=np.linalg.cond(q)/condition_a**2-2e-10
            error=max(error,la.norm(q@inverse-np.eye(3)))
            smallest_jensen=min(smallest_jensen,q[0,0]-np.exp(h[0,0]),inverse[0,0]-np.exp(-h[0,0]))
            assert abs(np.linalg.det(q)-1)<2e-11
        assert error<3e-11 and smallest_jensen>=-2e-12
        out.append(dict(cutoff=cutoff,frame_condition=condition_a,inverse_identity_error=error,
                        smallest_Jensen_margin=smallest_jensen,tests=80,
                        scope='Scalar conformal factors and a fixed uniformly conditioned frame cannot remove anisotropy'))
    return out


def tensor_fourier_tests():
    size=41;volume=(2*np.pi)**3;basis=stf_basis()
    wave=np.fft.fftfreq(size)*size
    coords=np.stack(np.meshgrid(wave,wave,wave,indexing='ij'),axis=-1)
    mag=np.linalg.norm(coords,axis=-1);safe=np.where(mag>0,mag,1)
    direction=coords/safe[...,None]
    projector=np.eye(3)-direction[...,None]*direction[...,None,:]
    noise=RNG.normal(size=(size,size,size,5))
    coeff=np.fft.fftn(noise,axes=(0,1,2))/size**1.5
    raw=np.einsum('...a,aij->...ij',coeff,basis)
    projected=np.einsum('...ij,...jk,...kl->...il',projector,raw,projector)
    trace=np.einsum('...ij,...ji->...',projector,raw)
    projected-=.5*trace[...,None,None]*projector
    projected[0,0,0]=0
    divergence=np.einsum('...i,...ij->...j',coords,projected)
    assert np.max(abs(divergence))<8e-14
    assert np.max(abs(np.trace(projected,axis1=-2,axis2=-1)))<8e-15
    out=[];g=12.
    for z in [1,4]:
        omega=safe if z==1 else safe*np.sqrt(1+safe**6)
        previous_variance=None
        for cutoff in [2,4,8,16]:
            mask=(mag>0)&(mag<=cutoff)
            weight=np.where(mask,1/np.sqrt(2*omega*volume),0)
            field=np.fft.ifftn(projected*weight[...,None,None]*size**3,axes=(0,1,2))
            assert np.max(abs(field.imag))<5e-15
            field=field.real
            eig=np.linalg.eigvalsh(field)
            v11=float(np.sum(weight*weight*.5*projector[...,0,0]**2))
            expected_frobenius=float(np.sum(2*weight*weight))
            measured_frobenius=float(np.mean(np.sum(field*field,axis=(-2,-1))))
            if z==1 and previous_variance is not None:assert v11>3.5*previous_variance
            previous_variance=v11
            logcond=g*(eig[...,-1]-eig[...,0])
            norm_upper=g*eig[...,-1]-g*g*v11/2
            out.append(dict(ultraviolet_exponent=z,cutoff=cutoff,grid_size=size,metric_coupling=g,
                            analytic_diagonal_variance=v11,expected_field_Frobenius_squared=expected_frobenius,
                            sampled_spatial_Frobenius_squared=measured_frobenius,
                            maximum_log_condition=float(np.max(logcond)),
                            mean_bounded_normalization_log_sup_upper=float(np.max(norm_upper)),
                            scope='One reproducible TT Fourier realization on a fixed torus; finite-grid extrema do not prove continuum sup bounds'))
    return out


def resolution_tests():
    out=[]
    for ell in [.2,.5,1.]:
        for multiple in [1.,2.,4.]:
            cutoff=multiple/ell
            value=quad(lambda k:k*np.exp(-(ell*k)**2),0,cutoff,epsabs=2e-13)[0]
            exact=(1-np.exp(-ell*ell*cutoff*cutoff))/(2*ell*ell)
            assert abs(value-exact)<2e-12
            out.append(dict(resolution=ell,cutoff=cutoff,diagonal_variance=value/(15*np.pi*np.pi),
                            limiting_variance=1/(30*np.pi*np.pi*ell*ell),
                            scope='Flat Gaussian smearing of the logarithmic field before exponentiation'))
    for amplitude in [.3,1.,3.]:
        value=quad(lambda x:np.exp(amplitude*np.cos(x)),0,2*np.pi,epsabs=2e-12)[0]/(2*np.pi)
        assert abs(value-i0(amplitude))<2e-12 and value>1
        out.append(dict(amplitude=amplitude,averaged_exponential_diagonal=value,
                        exponential_of_averaged_log_diagonal=1.,
                        scope='Commuting traceless diagonal example proving that the two coarse-graining prescriptions differ'))
    return out


def clock_tests():
    out=[];size=17;x=2*np.pi*np.arange(size)/size;frequencies=np.fft.fftfreq(size)*size
    def derivative(f,order):return np.fft.ifft((1j*frequencies)**order*np.fft.fft(f))
    for crossover in [2.,4.,8.]:
        for k in [1,2]:
            p=1;mode=np.exp(1j*k*x);lapse=np.exp(1j*p*x)
            def stiffness(n,f):
                return -derivative(n*derivative(f,1),1)+derivative(n*derivative(f,4),4)/crossover**6
            actual=lapse*stiffness(np.ones(size),mode)-stiffness(lapse,mode)
            coefficient=-k*p+(k**8-k**4*(k+p)**4)/crossover**6
            expected=coefficient*np.exp(1j*(k+p)*x)
            error=la.norm(actual-expected)
            assert error<2e-8,error
            inferred=-coefficient/(k*p)
            assert inferred>1
            ratio=np.sqrt(1+(k/crossover)**6)-1
            assert ratio<=(k/crossover)**6/2+1e-15
            out.append(dict(crossover=crossover,field_wavenumber=k,lapse_wavenumber=p,
                            bracket_coefficient=coefficient,ordinary_clock_coefficient=-k*p,
                            inferred_metric_coefficient=inferred,Fourier_output_error=error,
                            relative_dispersion_change=ratio,
                            scope='One canonical scalar with supplied eighth-order spatial stiffness; diagnostic for the proposed UV repair, not the full Einstein bracket'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(exact_identities=exact_identities(),angular_covariance=angular_tests(),radial_spectra=radial_tests(),
                point_metric=point_metric_tests(),momentum_sources=momentum_tests(),
                frame_and_conformal=frame_tests(),TT_fourier=tensor_fourier_tests(),
                resolved_metric=resolution_tests(),clock_defect=clock_tests())
    sources=['ULTRAVIOLET_METRIC_CONTROL.md','scripts/ultraviolet_metric_control_audit.py',
             'AFFINE_SPIN_METRIC.md','data/affine_spin_metric_audit.json',
             'SPATIAL_METRIC_VACUUM.md','data/spatial_metric_vacuum_audit.json',
             'REDUCED_TENSOR_HAMILTONIAN.md','SPIN_CLOCK_BRACKET.md',
             'CLOCK_MEDIATED_CONSTRAINTS.md','data/clock_mediated_constraints_audit.json']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']={'proved':'A Gaussian ultraviolet obstruction to a nondegenerate pointwise exponential TT metric; sufficient Gaussian spectral smoothing and its explicit clock defect',
                     'not_proved':['Interacting ultraviolet completion','Einstein refoliation symmetry','physical Newton constant',
                                   'microscopic selection of the repaired spectrum','TOE'],
                     'qualification':'Applies to the displayed Gaussian equal-time TT ansatz in a regular background frame; no no-go claim for general quantum gravity or distributional observables'}
    target=root/'data/ultraviolet_metric_control_audit.json';target.write_text(json.dumps(report,indent=2)+'\n')
    count=sum(len(report[k]) for k in ['angular_covariance','radial_spectra','point_metric','momentum_sources','frame_and_conformal',
                                      'TT_fourier','resolved_metric','clock_defect'])
    print('PASS: exact identities and',count,'numerical cases')
    print('Report:',target)
    print('Largest-cutoff point metric:',report['point_metric'][-1])


if __name__=='__main__':main()
