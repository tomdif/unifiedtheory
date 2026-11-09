#!/usr/bin/env python3
"""Nonlinear vacuum initial-data benchmark; not a microscopic GR derivation."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
import sympy as sy


def conformal_identities():
    xyz=sy.symbols('x y z',real=True)
    psi=sy.Function('psi')(*xyz)
    a,b=(sy.Function(name)(xyz[2]) for name in ['a','b'])
    tau=sy.Symbol('tau',real=True)
    sigma=sy.Matrix([[a,b,0],[b,-a,0],[0,0,0]])
    delta=lambda i,j:sy.Integer(i==j)
    gamma=lambda i,j,k:2*(delta(i,j)*sy.diff(psi,xyz[k])
                         +delta(i,k)*sy.diff(psi,xyz[j])
                         -delta(j,k)*sy.diff(psi,xyz[i]))/psi
    kup=psi**(-10)*sigma+tau*psi**(-4)*sy.eye(3)/3
    divergence=[]
    for i in range(3):
        value=sum(sy.diff(kup[i,j],xyz[j]) for j in range(3))
        value+=sum(gamma(i,j,k)*kup[k,j]+gamma(j,j,k)*kup[i,k]
                   for j,k in itertools.product(range(3),repeat=2))
        divergence.append(sy.simplify(value))
    assert divergence==[0,0,0]
    ricci=sy.zeros(3)
    for i,j in itertools.product(range(3),repeat=2):
        value=sum(sy.diff(gamma(k,i,j),xyz[k])-sy.diff(gamma(k,i,k),xyz[j]) for k in range(3))
        value+=sum(gamma(k,k,l)*gamma(l,i,j)-gamma(k,j,l)*gamma(l,i,k)
                   for k,l in itertools.product(range(3),repeat=2))
        ricci[i,j]=sy.simplify(value)
    scalar=sy.simplify(sy.trace(ricci)/psi**4)
    expected_scalar=-8*sum(sy.diff(psi,x,2) for x in xyz)/psi**5
    assert sy.simplify(scalar-expected_scalar)==0
    trace=sy.simplify(psi**4*sy.trace(kup))
    norm=sy.simplify(psi**8*sy.trace(kup*kup))
    assert trace==tau
    assert sy.simplify(norm-(2*(a*a+b*b)*psi**(-12)+tau*tau/3))==0
    return dict(momentum_constraints_identically_zero=True,scalar_curvature_identity=True,
                trace_identity=True,extrinsic_norm_identity=True,
                scope='A general three-dimensional conformal factor and a z-dependent flat TT seed; identities are exact, not finite-difference constraints.')


def exact_curved_data():
    amplitude,wave,z=sy.symbols('A k z',real=True)
    sigma=amplitude*sy.Matrix([[sy.cos(wave*z),sy.sin(wave*z),0],
                              [sy.sin(wave*z),-sy.cos(wave*z),0],[0,0,0]])
    tau=sy.sqrt(3)*amplitude
    extrinsic=sigma+tau*sy.eye(3)/3
    hamiltonian=sy.trigsimp(sy.trace(extrinsic)**2-sy.trace(extrinsic*extrinsic))
    assert hamiltonian==0
    magnetic=sy.Matrix(3,3,lambda i,j:sum(sy.LeviCivita(i,2,l)*sy.diff(extrinsic[l,j],z)
                                         for l in range(3)))
    electric=(tau*extrinsic-extrinsic*extrinsic).applyfunc(sy.trigsimp)
    assert (magnetic+wave*sigma).applyfunc(sy.trigsimp)==sy.zeros(3)
    assert magnetic==magnetic.T
    assert sy.trigsimp(sy.trace(electric))==0
    magnetic_norm=sy.trigsimp(sy.trace(magnetic*magnetic))
    assert magnetic_norm==2*amplitude**2*wave**2
    p=extrinsic-tau*sy.eye(3)
    assert sy.simplify(sy.trace(p)+2*tau)==0
    assert sy.trigsimp(sy.trace(p*p)-sy.trace(p)**2/2)==0
    rows=[]
    for amp,k in itertools.product([.001,.01,.1,1.],[1,2,5]):
        rows.append(dict(amplitude=amp,wavenumber=k,mean_curvature=np.sqrt(3)*amp,
                         magnetic_weyl_norm_squared=2*amp*amp*k*k))
    return dict(exact_vacuum_scalar_constraint=True,magnetic_weyl_identity=True,
                canonical_constraint_identity=True,cases=rows,
                scope='Exact non-flat vacuum initial data on the continuum torus. The subsequent Einstein evolution is supplied by the known Cauchy theorem, not simulated or derived from spins.')


def perturbative_coefficients():
    coeff={1:sy.Rational(1,2),2:sy.Rational(3,10),3:sy.Rational(1,2),
           4:-sy.Rational(19,80),6:-sy.Rational(9,400)}
    mean=sy.Rational(417,200)
    z=sy.Symbol('z',real=True)
    a=sy.cos(z)+sy.cos(2*z)/4
    b=sy.sin(z)+sy.Rational(3,20)*sy.sin(3*z)
    source=mean+sum(c*sy.cos(n*z) for n,c in coeff.items())
    assert sy.simplify(sy.expand((2*(a*a+b*b)-source).rewrite(sy.exp)))==0
    response=sum(c*sy.cos(n*z)/(8*n*n) for n,c in coeff.items())
    assert sy.expand(-8*sy.diff(response,z,2)-(source-mean))==0
    correlation=sum(c*c/(16*n*n) for n,c in coeff.items())
    return dict(mean_source=str(mean),normalized_c_derivative_at_zero=str(-7*correlation),
                mean_source_times_response=str(correlation),
                source_fourier_coefficients={str(n):str(c) for n,c in coeff.items()},
                inverse_laplacian_response_verified=True)


def laplacian(shape):
    # Positive periodic -Delta, with all coordinate periods equal to 2 pi.
    result=sp.csr_matrix((1,1))
    for n in shape:
        h=2*np.pi/n
        axis=sp.diags([-np.ones(n-1),2*np.ones(n),-np.ones(n-1)],[-1,0,1],format='lil')
        axis[0,n-1]=axis[n-1,0]=-1
        result=sp.kronsum(result,axis.tocsr()/h**2,format='csr')
    return result


def linear_response(source):
    eigen=np.zeros(source.shape)
    for axis,n in enumerate(source.shape):
        symbol=4*np.sin(np.pi*np.fft.fftfreq(n))**2/(2*np.pi/n)**2
        reshape=[1]*source.ndim;reshape[axis]=n
        eigen+=symbol.reshape(reshape)
    transformed=np.fft.fftn(source-source.mean())
    nonzero=eigen>0
    transformed[nonzero]/=8*eigen[nonzero]
    transformed[~nonzero]=0
    return np.fft.ifftn(transformed).real


def solve_normalized(source,epsilon):
    shape=source.shape;n=source.size;source=source.ravel()
    positive_lap=laplacian(shape)
    lam=epsilon*epsilon
    w=np.zeros(n);c=float(source.mean())
    def evaluate(w,c):
        psi=1+w
        f=c*psi**5-source*psi**(-7)
        residual=8*(positive_lap@w)+lam*f
        volume=np.expm1(6*np.log1p(w)).mean()
        return psi,residual,volume
    for iteration in range(30):
        psi,residual,volume=evaluate(w,c)
        norm=max(np.max(abs(residual)),abs(volume))
        if norm<2e-12:break
        jac=8*positive_lap+sp.diags(lam*(5*c*psi**4+7*source*psi**(-8)))
        factor=spla.splu(jac.tocsc())
        v=factor.solve(-residual)
        u=factor.solve(lam*psi**5)
        volume_gradient=6*psi**5/n
        dc=(volume+volume_gradient@v)/(volume_gradient@u)
        dw=v-u*dc
        step=1.
        while step>2**(-20):
            if c+step*dc>0 and np.min(1+w+step*dw)>0:
                _,new_residual,new_volume=evaluate(w+step*dw,c+step*dc)
                if max(np.max(abs(new_residual)),abs(new_volume)) < norm:
                    break
            step/=2
        assert step>2**(-20)
        w+=step*dw;c+=step*dc
    else:raise AssertionError('Newton iteration did not converge')
    psi,residual,volume=evaluate(w,c)
    lower=(source.min()/c)**(1/12)
    upper=(source.max()/c)**(1/12)
    assert psi.min()>=lower-1e-11 and psi.max()<=upper+1e-11
    m=lam*(5*c*lower**4+7*source.min()*upper**(-8))
    fixed_c_bound=np.max(abs(residual))/m
    return w.reshape(shape),c,dict(shape=list(shape),vertices=n,epsilon=epsilon,
                                   c=c,tau_squared=1.5*lam*c,newton_iterations=iteration,
                                   scalar_residual=float(np.max(abs(residual))),
                                   volume_residual=float(abs(volume)),
                                   minimum_psi=float(psi.min()),maximum_psi=float(psi.max()),
                                   subsolution=float(lower),supersolution=float(upper),
                                   fixed_c_residual_error_bound=float(fixed_c_bound))


def one_dimensional_checks():
    rows=[];solutions={}
    for n in [32,64,128,256]:
        z=2*np.pi*np.arange(n)/n
        source=2*((np.cos(z)+.25*np.cos(2*z))**2+(np.sin(z)+.15*np.sin(3*z))**2)
        w,c,row=solve_normalized(source,.2)
        rows.append(row);solutions[n]=w
    differences=[float(np.max(abs(solutions[n]-solutions[2*n][::2]))) for n in [32,64,128]]
    ratios=[differences[i]/differences[i+1] for i in range(2)]
    assert min(ratios)>3.8 and max(ratios)<4.3
    n=256;z=2*np.pi*np.arange(n)/n
    source=2*((np.cos(z)+.25*np.cos(2*z))**2+(np.sin(z)+.15*np.sin(3*z))**2)
    response=linear_response(source)
    assert np.max(abs(8*laplacian((n,))@response-(source-source.mean())))<1e-11
    cprime=-7*np.mean(source*response)
    perturbative=[]
    for epsilon in [.2,.1,.05,.025]:
        w,c,row=solve_normalized(source,epsilon);lam=epsilon**2
        row['psi_expansion_error']=float(np.max(abs(w-lam*response)))
        row['c_expansion_error']=float(abs(c-source.mean()-lam*cprime))
        perturbative.append(row)
    for key in ['psi_expansion_error','c_expansion_error']:
        error_ratios=[perturbative[i][key]/perturbative[i+1][key] for i in range(3)]
        assert min(error_ratios)>14 and max(error_ratios)<18
    return dict(grid_cases=rows,successive_grid_differences=differences,convergence_ratios=ratios,
                small_amplitude_cases=perturbative,discrete_c_derivative=float(cprime),
                scope='A local second-order elliptic discretization. The analytical fixed-c residual bound is evaluated in floating point, without interval certification; volume errors are separate. Continuum existence and uniqueness are analytical arguments in the note.')


def three_dimensional_checks():
    rows=[]
    for n in [6,8,10]:
        x,y,z=np.meshgrid(*([2*np.pi*np.arange(n)/n]*3),indexing='ij')
        # Three flat TT patterns on orthogonal axes. The dominant z pattern
        # has constant norm sqrt(2); the others have norms .15 sqrt(2),
        # .1 sqrt(2), which supplies a positive analytic lower bound.
        sigma=np.zeros((n,n,n,3,3))
        for coordinate,amplitude,i,j in [(z,1.,0,1),(x,.15,1,2),(y,.1,2,0)]:
            sigma[...,i,i]+=amplitude*np.cos(coordinate)
            sigma[...,j,j]-=amplitude*np.cos(coordinate)
            sigma[...,i,j]+=amplitude*np.sin(coordinate)
            sigma[...,j,i]+=amplitude*np.sin(coordinate)
        source=np.sum(sigma*sigma,axis=(-2,-1))
        assert source.min()>=2*(1-.15-.1)**2-1e-12
        assert np.max(abs(np.trace(sigma,axis1=-2,axis2=-1)))<1e-12
        # Centered derivative of the seed (not of the conformal metric).
        div=sum((np.roll(sigma[...,i,:],-1,axis=i)-np.roll(sigma[...,i,:],1,axis=i))
                 /(4*np.pi/n) for i in range(3))
        assert np.max(abs(div))<1e-12
        for epsilon in [.1,.3]:
            _,_,row=solve_normalized(source,epsilon)
            rows.append(row)
    return dict(cases=rows,scope='Six nonconstant three-dimensional source tests through 1000 vertices, with independently transverse-traceless seeds. These are constraint solves, not spacetime evolution simulations.')


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(conformal=conformal_identities(),exact_initial_data=exact_curved_data(),
                perturbative_coefficients=perturbative_coefficients(),
                one_dimensional=one_dimensional_checks(),three_dimensional=three_dimensional_checks())
    sources=['NONLINEAR_TENSOR_BACKREACTION.md','scripts/nonlinear_tensor_backreaction_audit.py',
             'GRAVITY_FROM_CLOCK_CONSTRAINTS.md','BOND_TENSOR_CONSTRAINTS.md',
             'COMPACT_TENSOR_CONSTRAINTS.md','COMPACT_TENSOR_DYNAMICS.md',
             'COMPACT_CONSTRAINT_NORMALIZER.md','EINSTEIN_MODEL_DECISION.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']='Nonlinear vacuum initial data and a necessary global constraint for the supplied Einstein target. The microscopic gravitational dynamics, its state selection, and a TOE remain unproved.'
    (root/'data/nonlinear_tensor_backreaction_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
