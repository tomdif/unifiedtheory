#!/usr/bin/env python3
"""Scalar-induced shear dynamics and the failure of a common Einstein cone."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gamma, ive
import sympy as sy


def frequency_integral_checks():
    rng=np.random.default_rng(95203);rows=[]
    for case in range(16):
        a,b=rng.uniform(.2,3.,2);frequency=rng.uniform(0,2.)
        numerical,error=quad(lambda nu:1/((nu*nu+a*a)*((nu+frequency)**2+b*b))/(2*np.pi),
                             -np.inf,np.inf,epsabs=1e-12,epsrel=1e-11)
        expected=(a+b)/(2*a*b*((a+b)**2+frequency**2))
        assert abs(numerical-expected)<1e-10
        rows.append(dict(a=float(a),b=float(b),frequency=float(frequency),
                         absolute_error=float(abs(numerical-expected)),quadrature_error=float(error)))
    return dict(cases=rows)


def symbolic_identities():
    q=sy.Symbol('q',real=True)
    assert sy.trigsimp(sy.sin(q)**2+(1-sy.cos(q))**2-2*(1-sy.cos(q)))==0
    # The spatial integration-by-parts identity proving a strict speed deficit.
    other=sy.Symbol('other',positive=True)
    omega2=other+2*(1-sy.cos(q))
    derivative=sy.diff(sy.sin(q)/omega2**sy.Rational(5,2),q)
    expected=sy.cos(q)/omega2**sy.Rational(5,2)-5*sy.sin(q)**2/omega2**sy.Rational(7,2)
    assert sy.simplify(derivative-expected)==0
    # A nonzero symmetric tensor cannot have s^T T s identically zero.
    x,y,z=sy.symbols('x y z');c=sy.symbols('c0:6')
    polynomial=c[0]*x*x+c[1]*y*y+c[2]*z*z+2*c[3]*x*y+2*c[4]*y*z+2*c[5]*z*x
    matrix,_=sy.linear_eq_to_matrix(sy.Poly(polynomial,x,y,z).coeffs(),c)
    assert matrix.rank()==6
    return dict(positive_stencil_identity=True,strict_speed_deficit_identity=True,
                tensor_temporal_gram_kernel_dimension=6-int(matrix.rank()))


def moments(t):
    if t==0:return 1.,0.,.5,.375
    a0=ive(0,2*t);a1=ive(1,2*t)
    return a0,a1,a1/(2*t),3*ive(2,2*t)/(4*t*t)


def bessel_coefficients(mass,polarization):
    def integrand(t,power,cosine=False):
        a0,a1,s2,s4=moments(t)
        transverse=2*(s4*a0-s2*s2) if polarization=='plus' else 4*s2*s2
        return t**(power/2-1)*np.exp(-mass*mass*t)*transverse*(a1 if cosine else a0)/gamma(power/2)
    values=[];errors=[]
    for power,cosine,factor in [(3,False,-1/8),(5,False,1/32),(5,True,1/32)]:
        value,error=quad(lambda t:integrand(t,power,cosine),0,np.inf,
                         epsabs=2e-13,epsrel=2e-11,limit=300)
        values.append(factor*value);errors.append(abs(factor)*error)
    r,zt,zz=values
    assert r<0 and 0<zz<zt
    return dict(mass=mass,polarization=polarization,mass_shift=r,time_coefficient=zt,
                space_coefficient=zz,speed=float(np.sqrt(zz/zt)),
                estimated_coefficient_errors=errors,
                normalization='One real scalar and unit squared source coupling; lattice spacing and scalar acoustic speed are one.')


def grid(n,mass):
    q=(np.arange(n)+.5)*2*np.pi/n-np.pi
    x,y,z=np.meshgrid(q,q,q,indexing='ij')
    sx,sy,sz=np.sin(x),np.sin(y),np.sin(z)
    omega=np.sqrt(mass*mass+2*(3-np.cos(x)-np.cos(y)-np.cos(z)))
    return x,y,z,sx,sy,sz,omega


def bz_coefficients(data,polarization):
    _,_,_,sx,sy,sz,omega=data
    vertex=sy*sy-sx*sx if polarization=='plus' else -2*sx*sy
    r=-np.mean(vertex**2/omega**3)/8
    zt=np.mean(vertex**2/omega**5)/32
    zz=5*np.mean(vertex**2*sz**2/omega**7)/32
    return np.array([r,zt,zz])


def coefficient_comparison():
    reference={(mass,pol):bessel_coefficients(mass,pol)
               for mass,pol in itertools.product([0.,.2],['plus','cross'])}
    rows=[]
    for n,mass in itertools.product([24,40,64,96],[0.,.2]):
        data=grid(n,mass)
        for pol in ['plus','cross']:
            values=bz_coefficients(data,pol)
            ref=reference[(mass,pol)]
            target=np.array([ref['mass_shift'],ref['time_coefficient'],ref['space_coefficient']])
            errors=abs(values-target)
            if n==96:
                assert errors.max() < (2.5e-6 if mass==0 else 2e-11)
            rows.append(dict(points_per_axis=n,mass=mass,polarization=pol,
                             coefficients=values.tolist(),absolute_errors=errors.tolist()))
    # The finite grid has a mild infrared error at m=0; the Bessel integral
    # supplies an independent infinite-volume value rather than extrapolation.
    for mass in [0.,.2]:
        assert reference[(mass,'plus')]['speed']-reference[(mass,'cross')]['speed']>.05
        assert abs(reference[(mass,'cross')]['mass_shift'])>3*abs(reference[(mass,'plus')]['mass_shift'])
    return dict(infinite_volume=list(reference.values()),brillouin_zone_checks=rows,
                scope='Independent adaptive one-dimensional Bessel integrals and three-dimensional midpoint quadrature. Error estimates are floating-point quadrature estimates, not interval certificates.')


def static_and_temporal_checks():
    data=grid(64,.2)
    _,_,_,sx,sy,_,omega=data
    rows=[]
    for pol in ['plus','cross']:
        vertex=sy*sy-sx*sx if pol=='plus' else -2*sx*sy
        r,zt,_=bz_coefficients(data,pol)
        for amplitude in [.004,.002]:
            ratio=amplitude*vertex/omega**2
            # The rationalized expression avoids subtracting the extensive
            # background zero-point energy when evaluating its second variation.
            plus=ratio/(np.sqrt(1+ratio)+1)
            minus=-ratio/(np.sqrt(1-ratio)+1)
            second=np.mean(omega*(plus+minus)/2)/amplitude**2
            assert abs(second-r)<2e-8
            rows.append(dict(polarization=pol,amplitude=amplitude,
                             exact_vacuum_curvature=float(second),bubble_curvature=float(r)))
        for frequency in [.02,.01,.005]:
            # Pi(Omega,0)-Pi(0,0), evaluated without subtractive cancellation.
            difference=np.mean(vertex**2*frequency**2/(8*omega**3*(4*omega**2+frequency**2)))
            coefficient=difference/frequency**2
            assert abs(coefficient-zt)/zt<.002
            rows.append(dict(polarization=pol,frequency=frequency,
                             frequency_difference_coefficient=float(coefficient),limit=float(zt)))
    return dict(cases=rows)


def temporal_gram_check():
    data=grid(48,.2);_,_,_,sx,sy,sz,omega=data
    # Frobenius-orthonormal symmetric components; no TT projection here.
    vertices=np.array([sx*sx,sy*sy,sz*sz,np.sqrt(2)*sx*sy,np.sqrt(2)*sy*sz,np.sqrt(2)*sz*sx])
    weighted=vertices.reshape(6,-1)/omega.ravel()**2.5
    gram=weighted@weighted.T/(32*omega.size)
    eigen=np.linalg.eigvalsh(gram)
    assert eigen.min()>1e-5
    return dict(eigenvalues=eigen.tolist(),rank=6,
                scope='The full six-component temporal response is positive definite. It supplies no gauge null directions or first-class gravitational constraints.')


def pole_checks():
    data=grid(96,0.);x,y,z,sx,sy,_,omega=data
    rows=[]
    for momentum in [.4,.2,.1,.05]:
        a=np.sqrt(2*(3-np.cos(x)-np.cos(y)-np.cos(z-momentum/2)))
        b=np.sqrt(2*(3-np.cos(x)-np.cos(y)-np.cos(z+momentum/2)))
        total=a+b;threshold=2*np.sin(momentum/2)
        for pol in ['plus','cross']:
            vertex=sy*sy-sx*sx if pol=='plus' else -2*sx*sy
            base=np.mean(vertex**2/(4*omega**3))
            prefactor=vertex**2*total/(2*a*b)
            def inverse(frequency):
                return -.5*(np.mean(prefactor/(total**2-frequency**2))-base)
            assert inverse(0)>0 and inverse(.99999*threshold)<0
            pole=brentq(inverse,0,.99999*threshold,xtol=1e-12)
            residue_inverse=.5*np.mean(prefactor/(total**2-pole**2)**2)
            assert residue_inverse>0 and pole<threshold
            rows.append(dict(polarization=pol,momentum=momentum,frequency=float(pole),
                             speed=float(pole/momentum),two_scalar_threshold=float(threshold),
                             inverse_propagator_residual=float(abs(inverse(pole))),
                             positive_kinetic_residue_inverse=float(residue_inverse)))
    return dict(cases=rows,
                scope='Poles of a deliberately mass-tuned Gaussian collective-source model built from the exact scalar response. This does not establish a pole, critical phase, or mass tuning in the full spin-field Hamiltonian.')


def spin_response_reference(coefficients):
    rows=[];coupling=.5
    for row in coefficients['infinite_volume']:
        if row['mass']!=0:continue
        # Exact isolated-cell susceptibility is 2 mu/(Omega^2+mu^2).
        # Adding the scalar self-energy is only a Gaussian/RPA reference.
        mu=-2*coupling**2*row['mass_shift']
        time=1/(2*mu)+coupling**2*row['time_coefficient']
        space=coupling**2*row['space_coefficient']
        rows.append(dict(polarization=row['polarization'],coupling=coupling,
                         reference_critical_spin_gap=mu,reference_speed=float(np.sqrt(space/time))))
    return dict(cases=rows,
                scope='A susceptibility-matching reference, not a controlled proof of the interacting critical spin phase. One common bare gap cannot satisfy both polarization tunings here.')


def main():
    root=Path(__file__).resolve().parents[1]
    coefficients=coefficient_comparison()
    report=dict(symbolic=symbolic_identities(),frequency_integral=frequency_integral_checks(),
                coefficients=coefficients,independent_response=static_and_temporal_checks(),
                temporal_gram=temporal_gram_check(),tuned_gaussian_poles=pole_checks(),
                isolated_spin_reference=spin_response_reference(coefficients))
    sources=['INDUCED_TENSOR_DYNAMICS.md','scripts/induced_tensor_dynamics_audit.py',
             'SPIN_CLOCK_BRACKET.md','scripts/spin_clock_bracket_audit.py',
             'INDUCED_GEOMETRY_INTERACTION.md','COLLECTIVE_GEOMETRY_STABILITY.md',
             'COMPACT_TENSOR_DYNAMICS.md','COMPACT_CONSTRAINT_NORMALIZER.md',
             'EINSTEIN_MODEL_DECISION.md','NONLINEAR_TENSOR_BACKREACTION.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']='Scalar fluctuations induce positive shear derivative coefficients and mass-tuned Gaussian linear poles, but unequal subluminal speeds and a full-rank six-component response fail the Einstein matching test. A microscopic gravitational phase and TOE remain unproved.'
    (root/'data/induced_tensor_dynamics_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
