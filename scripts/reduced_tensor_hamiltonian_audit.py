#!/usr/bin/env python3
"""Reduced logarithmic TT Hamiltonian coefficients under Einstein constraints."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from numpy.polynomial.legendre import leggauss, legvander
import sympy as sy

from canonical_metric_reconstruction_audit import ExpGeometry, SpectralMomentum


def christoffel_lower(derivative):
    result = np.zeros_like(derivative)
    for k, i, j in itertools.product(range(3), repeat=3):
        result[..., k, i, j] = (derivative[..., i, k, j]+derivative[..., j, k, i]-derivative[..., k, i, j])/2
    return result


def contraction(inverse, left, right):
    return np.einsum('...ij,...kil,...ljk->...', inverse, left, right)


def exact_identities():
    z = sy.Symbol('z')
    f2 = (z/(2*sy.sinh(z/2)))**2
    assert sy.series(f2, z, 0, 6).removeO() == 1-z*z/12+z**4/240
    d = [[[sy.Symbol('d'+str(a)+str(min(i,j))+str(max(i,j)))
           for j in range(3)] for i in range(3)] for a in range(3)]
    gamma = [[[ (d[i][k][j]+d[j][k][i]-d[k][i][j])/2
               for j in range(3)] for i in range(3)] for k in range(3)]
    bulk = sum(gamma[k][i][l]*gamma[l][i][k] for i,k,l in itertools.product(range(3),repeat=3))
    gradient = sum(d[a][i][j]**2 for a,i,j in itertools.product(range(3),repeat=3))
    crossed = sum(d[l][i][k]*d[k][i][l] for i,k,l in itertools.product(range(3),repeat=3))
    assert sy.expand(bulk+gradient/4-crossed/2) == 0
    nx, ny, nz = sy.symbols('nx ny nz', real=True)
    n = sy.Matrix([nx,ny,nz]); squared=(n.T*n)[0]
    projector=n*n.T/squared-sy.eye(3)/3
    assert sy.simplify(sy.trace(projector*projector)-sy.Rational(2,3)) == 0
    assert sy.Rational(3,8)**2*sy.Rational(2,3)==sy.Rational(3,32)
    return dict(logarithmic_kinetic_factor_series='1-z^2/12+z^4/240',
                christoffel_quadratic_bulk_identity=True,
                aligned_longitudinal_squared_coefficient='3/32',
                scope="Exact algebra used in the reduced Hamiltonian expansion. TT differential identities, asymptotically flat constraints and the canonical reduction are stated in the note.")


def compact_profile():
    x,y,z=sy.symbols('x y z',real=True)
    coordinates=[x,y,z]
    r2=x*x+y*y+z*z
    b,c=90*(1-r2)**8,-720*(1-r2)**7
    tau=sy.Matrix([[24*x*y*z*c,-12*z*(x*x-y*y)*c,-12*y*(2*b+(x*x+y*y)*c)],
                   [-12*z*(x*x-y*y)*c,-24*x*y*z*c,12*x*(2*b+(x*x+y*y)*c)],
                   [-12*y*(2*b+(x*x+y*y)*c),12*x*(2*b+(x*x+y*y)*c),0]])
    eta=sy.zeros(3)
    for i,j in itertools.product(range(3),repeat=2):
        eta[i,j]=sy.factor(sum(
            sy.LeviCivita(i,k,l)*sy.diff(tau[l,j],coordinates[k])
            +sy.LeviCivita(j,k,l)*sy.diff(tau[l,i],coordinates[k])
            for k,l in itertools.product(range(3),repeat=2))/2)
    assert eta==eta.T and sy.factor(sy.trace(eta))==0
    for j in range(3):
        assert sy.factor(sum(sy.diff(eta[i,j],coordinates[i]) for i in range(3)))==0
    def ball_integral(expression):
        # For a rotationally invariant scalar, evaluate at y=0 and integrate
        # 2*pi*r^2 dr dmu with x=r*sqrt(1-mu^2), z=r*mu.
        result=sy.S.Zero
        for (a,b),coefficient in sy.Poly(sy.expand(expression),x,z).terms():
            assert a%2==0 and b%2==0
            angular=sum((-1)**j*sy.binomial(a//2,j)*sy.Rational(2,b+2*j+1)
                        for j in range(a//2+1))
            result+=coefficient*angular/sy.Integer(a+b+3)
        return sy.factor(2*sy.pi*result)
    norm_integral=ball_integral(sum(eta[i,j]**2 for i,j in itertools.product(range(3),repeat=2)).subs(y,0))
    gradient_integral=ball_integral(sum(sy.diff(eta[i,j],coordinates[a])**2
                                      for a,i,j in itertools.product(range(3),repeat=3)).subs(y,0))/4
    assert sy.simplify(gradient_integral/norm_integral)==sy.Rational(105,4)
    radial=1-x*x-z*z
    reduced_h=np.array([[sy.cancel(eta[i,j].subs(y,0)/radial**6)
                         for j in range(3)] for i in range(3)],dtype=object)
    reduced_dh=np.array([[[sy.cancel(sy.diff(eta[i,j],coordinates[a]).subs(y,0)/radial**5)
                           for j in range(3)] for i in range(3)] for a in range(3)],dtype=object)
    first=christoffel_lower(reduced_dh)
    second=christoffel_lower(reduced_dh@reduced_h+reduced_h@reduced_dh)/2
    for k,i,j in itertools.product(range(3),repeat=3):
        second[k,i,j]-=sum(reduced_h[k,l]*first[l,i,j] for l in range(3))
    cubic=2*sum(first[k,i,l]*second[l,i,k] for i,k,l in itertools.product(range(3),repeat=3))
    cubic-=sum(reduced_h[i,j]*first[k,i,l]*first[l,j,k]
               for i,j,k,l in itertools.product(range(3),repeat=4))
    cubic_integral=ball_integral(radial**16*sy.expand(cubic))
    assert sy.simplify(cubic_integral/sy.pi)<0
    cubic_coefficient=sy.simplify(-cubic_integral/norm_integral**sy.Rational(3,2))
    expressions=[sy.factor(eta[i,j].subs(y,0)) for i,j in itertools.product(range(3),repeat=2)]
    expressions += [sy.factor(sy.diff(eta[i,j],coordinates[a]).subs(y,0))
                    for a,i,j in itertools.product(range(3),repeat=3)]
    evaluator=sy.lambdify([x,z],expressions,'numpy',cse=True)
    jets=[eta[i,j] for i,j in itertools.product(range(3),repeat=2)]
    jets += [sy.diff(eta[i,j],coordinates[a]) for a,i,j in itertools.product(range(3),repeat=3)]
    jets += [sy.diff(eta[i,j],coordinates[a],coordinates[b])
             for a,b,i,j in itertools.product(range(3),repeat=4)]
    evaluator.jets=sy.lambdify(coordinates,[sy.factor(e) for e in jets],'numpy',cse=True)
    return evaluator,dict(trace_zero=True,divergence_zero=True,
                          seed='symmetrized curl of the Cotton TT tensor of diag(-1,-1,2)*(1-r^2)^10',
                          exact_unnormalized_L2_squared=str(norm_integral),
                          exact_normalized_gradient_energy='105/4',
                          exact_cubic_curvature_coefficient=str(cubic_coefficient),
                          exact_cubic_curvature_coefficient_positive=True,
                          compact_boundary_vanishing_order=6)


class Profile:
    def __init__(self,nr,na,evaluator,normalization=None):
        r,wr=leggauss(nr); r=(r+1)/2;wr=wr/2
        mu,wm=leggauss(na)
        self.r,self.mu=r,mu
        self.weight=(2*np.pi*r[:,None]**2*wr[:,None]*wm[None,:]).ravel()
        x=(r[:,None]*np.sqrt(1-mu[None,:]**2)).ravel()
        z=(r[:,None]*mu[None,:]).ravel()
        values=np.stack(np.broadcast_arrays(*evaluator(x,z)),axis=-1)
        raw=values[:,:9].reshape(-1,3,3)
        norm_squared=float(self.weight@np.sum(raw*raw,axis=(1,2)))
        self.normalization=np.sqrt(norm_squared) if normalization is None else normalization
        self.h=raw/self.normalization
        self.dh=values[:,9:].reshape(-1,3,3,3)/self.normalization
        self.f=np.sum(self.h*self.h,axis=(1,2))
        self.v=np.sum(self.dh*self.dh,axis=(1,2,3))/4
        self.identity=np.broadcast_to(np.eye(3),self.h.shape)
        self.g1=christoffel_lower(self.dh)
        h2=self.h@self.h
        dh2=self.dh@self.h[:,None]+self.h[:,None]@self.dh
        dh3=(self.dh@h2[:,None]+self.h[:,None]@self.dh@self.h[:,None]+h2[:,None]@self.dh)
        self.g2=christoffel_lower(dh2)/2-np.einsum('pkl,plij->pkij',self.h,self.g1)
        self.g3=(christoffel_lower(dh3)/6
                 -np.einsum('pkl,plij->pkij',self.h,christoffel_lower(dh2))/2
                 +np.einsum('pkl,plij->pkij',h2,self.g1)/2)
        self.r2_bulk=contraction(self.identity,self.g1,self.g1)
        self.r3_bulk=(2*contraction(self.identity,self.g1,self.g2)-contraction(self.h,self.g1,self.g1))
        self.r4_bulk=(2*contraction(self.identity,self.g1,self.g3)+contraction(self.identity,self.g2,self.g2)
                      -2*contraction(self.h,self.g1,self.g2)+contraction(h2,self.g1,self.g1)/2)
        self.nr,self.na=nr,na
        self.polynomials=legvander(self.mu,self.na-1)
        self.angular_projection=(self.polynomials.T*wm)*(2*np.arange(self.na)+1)[:,None]/2
        minimum=np.minimum(r[:,None],r[None,:]);maximum=np.maximum(r[:,None],r[None,:])
        self.kernels=np.array([(minimum/maximum)**ell/maximum*
                               (wr*r*r)[None,:]/(2*ell+1) for ell in range(na)])
        assert abs(self.weight@(self.r2_bulk+self.v)) < 3e-10
        assert abs(self.weight@self.f-1) < 2e-12

    def potential(self,amplitude):
        values,vectors=np.linalg.eigh(amplitude*self.h)
        transpose=vectors.swapaxes(-1,-2)
        midpoint=(values[:,:,None]+values[:,None,:])/2
        difference=(values[:,:,None]-values[:,None,:])/2
        ratio=np.ones_like(difference)
        np.divide(np.sinh(difference),difference,out=ratio,where=abs(difference)>1e-12)
        factors=np.exp(midpoint)*ratio
        dg=vectors[:,None]@((transpose[:,None]@(amplitude*self.dh)@vectors[:,None])*factors[:,None])@transpose[:,None]
        inverse=(vectors*np.exp(-values)[:,None,:])@transpose
        gamma=np.einsum('pkl,plij->pkij',inverse,christoffel_lower(dg))
        return -float(self.weight@contraction(inverse,gamma,gamma))

    def newton(self,source):
        # N=(-Delta)^(-1), with the entire exterior tail represented analytically.
        coefficients=source.reshape(self.nr,self.na)@self.angular_projection.T
        radial=np.einsum('lij,jl->il',self.kernels,coefficients)
        return (radial@self.polynomials.T).ravel()


def compact_curvature(evaluator):
    reference=Profile(48,32,evaluator)
    rows=[]
    for nr,na in [(32,20),(48,32),(64,40)]:
        profile=Profile(nr,na,evaluator,reference.normalization)
        c2=float(profile.weight@profile.v)
        c3=-float(profile.weight@profile.r3_bulk)
        c4=-float(profile.weight@profile.r4_bulk)
        assert abs(c3)>1e-4
        for amplitude in [.005,.01,.02,.04]:
            exact=profile.potential(amplitude)
            expansion=c2*amplitude**2+c3*amplitude**3+c4*amplitude**4
            odd=(profile.potential(amplitude)-profile.potential(-amplitude))/(2*amplitude**3)
            assert abs(exact-expansion)<3.3*amplitude**5
            assert abs(odd-c3)<3.2*amplitude**2
            rows.append(dict(radial_points=nr,angular_points=na,amplitude=amplitude,
                             normalized_profile_gradient_energy=c2,cubic_curvature_coefficient=c3,
                             quartic_curvature_coefficient=c4,exact_compact_curvature_potential=exact,
                             fourth_order_expansion=expansion,expansion_error=abs(exact-expansion),
                             odd_difference_cubic_coefficient=odd))
        print(json.dumps(rows[-1]),flush=True)
    return dict(cases=rows,scope="A genuine compact, nonzero TT metric profile with its full exponential-metric curvature integral. This checks local curvature coefficients, not a replacement of the scalar and vector Einstein solves by an unconstrained energy."),reference


def curvature_from_jets(q,dq,ddq):
    inverse=la.inv(q)
    lower=christoffel_lower(dq)
    gamma=np.einsum('kl,lij->kij',inverse,lower)
    derivatives=np.zeros((3,3,3,3))
    for a in range(3):
        inverse_derivative=-inverse@dq[a]@inverse
        derivatives[a]=(np.einsum('kl,lij->kij',inverse_derivative,lower)
                        +np.einsum('kl,lij->kij',inverse,christoffel_lower(ddq[a])))
    ricci=np.zeros((3,3))
    for i,j in itertools.product(range(3),repeat=2):
        ricci[i,j]=sum(derivatives[k,k,i,j]-derivatives[j,k,i,k] for k in range(3))
        ricci[i,j]+=sum(gamma[k,k,l]*gamma[l,i,j]-gamma[k,i,l]*gamma[l,j,k]
                        for k,l in itertools.product(range(3),repeat=2))
    return float(np.sum(inverse*ricci))


def exponential_curvature(h,dh,ddh):
    q=la.expm(h)
    dq=np.array([la.expm_frechet(h,d,compute_expm=False) for d in dh])
    ddq=np.zeros((3,3,3,3))
    for a,b in itertools.product(range(3),repeat=2):
        block=np.zeros((9,9))
        for i in range(3):
            block[3*i:3*i+3,3*i:3*i+3]=h
        block[:3,3:6]=dh[a];block[3:6,6:]=dh[b]
        first=la.expm(block)[:3,6:]
        block[:3,3:6]=dh[b];block[3:6,6:]=dh[a]
        second=la.expm(block)[:3,6:]
        ddq[a,b]=first+second+la.expm_frechet(h,ddh[a,b],compute_expm=False)
    return curvature_from_jets(q,dq,ddq)


def pointwise_scalar(evaluator,normalization):
    rows=[]
    for point in [[.08,.03,.12],[.16,.11,.25],[.25,.05,.36],[.37,.14,.18],
                  [.46,.2,.3],[.58,.1,.17]]:
        jets=np.array(evaluator.jets(*point),float)/normalization
        h,dh,ddh=jets[:9].reshape(3,3),jets[9:36].reshape(3,3,3),jets[36:].reshape(3,3,3,3)
        target=-float(np.sum(dh*dh))/4
        estimates=[]
        for epsilon in [.001,.002]:
            plus=exponential_curvature(epsilon*h,epsilon*dh,epsilon*ddh)
            minus=exponential_curvature(-epsilon*h,-epsilon*dh,-epsilon*ddh)
            estimates.append((plus+minus)/(2*epsilon**2))
        extrapolated=(4*estimates[0]-estimates[1])/3
        error=abs(extrapolated-target)
        assert error<3e-6
        rows.append(dict(point=point,quadratic_scalar_curvature=target,
                         independent_exponential_Ricci_estimate=extrapolated,error=error))
    return dict(cases=rows,scope="Independent Ricci evaluation uses first Frechet derivatives and 9x9 block exponentials for second derivatives. A centered small-amplitude extrapolation checks R_2=-|grad h|^2/4 pointwise on an exact compact TT profile.")


def kinetic_pointwise():
    rows=[];rng=np.random.default_rng(9112661)
    for size,case in itertools.product([0.,.2,.6],range(4)):
        h=rng.normal(size=(3,3));h=(h+h.T)/2;h-=np.eye(3)*np.trace(h)/3
        h*=size/max(la.norm(h,2),1e-12)
        p=rng.normal(size=(3,3));p=(p+p.T)/2;p-=np.eye(3)*np.trace(p)/3
        geometry=ExpGeometry(h);t=geometry.apply(p,inverse=True)
        direct=float(np.trace(geometry.metric@t@geometry.metric@t))
        values,vectors=la.eigh(h);gap=values[:,None]-values[None,:]
        factor=np.ones_like(gap)
        np.divide(gap,2*np.sinh(gap/2),out=factor,where=abs(gap)>1e-12)
        predicted=float(np.sum((factor*(vectors.T@p@vectors))**2))
        bound=1. if size==0 else (size/np.sinh(size))**2
        assert abs(direct-predicted)<3e-12
        assert bound*np.sum(p*p)-3e-12 <= direct <= np.sum(p*p)+3e-12
        rows.append(dict(log_metric_operator_norm=size,case=case,kinetic_norm=direct,
                         spectral_identity_error=abs(direct-predicted),lower_factor=bound))
    return dict(cases=rows,scope="Pointwise exact logarithmic cotangent kinetic factor and its positive spectral bounds; no cubic h p^2 term is present.")


def periodic_kinetic():
    rows=[]
    for size,epsilon in itertools.product([7,9,11],[.025,.05,.1]):
        energies=[];quartic=None;maximum_residual=0.
        for sign in [-1,1]:
            lattice=SpectralMomentum(size,sign*epsilon)
            lattice.s*=epsilon
            w=np.zeros(lattice.h.shape[:-1])
            for iteration in range(100):
                p=lattice.s+lattice.longitudinal(w)
                residual=lattice.constraint(p)
                maximum=float(la.norm(residual.ravel())/size**1.5)
                if maximum<2e-15:
                    break
                w-=lattice.inverse_flat(residual)
            assert maximum<2e-15
            maximum_residual=max(maximum_residual,maximum)
            t=lattice.geometry.apply(p,inverse=True)
            tg=t@lattice.geometry.metric
            energies.append(float(np.mean(np.trace(tg@tg,axis1=-2,axis2=-1))))
            comm=lattice.s@lattice.h-lattice.h@lattice.s
            source=np.stack([np.sum(lattice.s*d,axis=(-2,-1)) for d in lattice.dh],axis=-1)-lattice.divergence(comm)
            w2=-lattice.inverse_flat(source)
            l2=lattice.longitudinal(w2)
            quartic=float(np.mean(np.sum(l2*l2,axis=(-2,-1))-np.sum(comm*comm,axis=(-2,-1))/12))
            quadratic=float(np.mean(np.sum(lattice.s*lattice.s,axis=(-2,-1))))
        actual=sum(energies)/2
        error=abs(actual-quadratic-quartic)
        assert error<.003*epsilon**6
        rows.append(dict(grid_per_axis=size,amplitude=epsilon,quadratic_kinetic=quadratic,
                         predicted_fourth_order_correction=quartic,
                         averaged_full_nonlinear_kinetic=actual,
                         remainder_after_quartic=error,momentum_residual=maximum_residual))
    return dict(cases=rows,scope="Full periodic nonlinear vector constraint solve, averaged over opposite h signs, tests the quartic kinetic correction and absent cubic term. It is not a periodic scalar-constraint or ADM-energy solve.")


def split_newton(evaluator,normalization,order):
    r,wr=leggauss(order);r=(r+1)/2;wr/=2
    t,wt=leggauss(order);t=(t+1)/2;wt/=2
    mu,wm=leggauss(order)
    polynomials=legvander(mu,32)
    projection=(polynomials.T*wm)*(2*np.arange(33)+1)[:,None]/2
    def coefficients(radius):
        x=radius[...,None]*np.sqrt(1-mu**2);z=radius[...,None]*mu
        values=np.stack(np.broadcast_arrays(*evaluator(x.ravel(),z.ravel())),axis=-1)/normalization
        h=values[:,:9].reshape(-1,3,3);dh=values[:,9:].reshape(-1,3,3,3)
        f=np.sum(h*h,axis=(1,2)).reshape(radius.shape+(order,))
        v=np.sum(dh*dh,axis=(1,2,3)).reshape(radius.shape+(order,))/4
        return f@projection.T,v@projection.T
    fr,vr=coefficients(r)
    fst,vst=coefficients(r[:,None]*t[None,:])
    base=(wr*r**4)[:,None,None]*wt[None,:,None]*t[None,:,None]**(np.arange(33)[None,None,:]+2)
    base*=4*np.pi/(2*np.arange(33)[None,None,:]+1)**2
    ff=float(np.sum(base*(fr[:,None,:]*fst+fr[:,None,:]*fst)))
    fv=float(np.sum(base*(fr[:,None,:]*vst+vr[:,None,:]*fst)))
    vv=float(np.sum(base*(vr[:,None,:]*vst+vr[:,None,:]*vst)))
    return ff,fv,vv


def aligned_coefficients(evaluator,profile):
    rows=[]
    c2=float(profile.weight@profile.v);c3=-float(profile.weight@profile.r3_bulk)
    c4=-float(profile.weight@profile.r4_bulk)
    f4=float(profile.weight@(profile.f*profile.f))
    for order in [36,44,52]:
        ff,fv,vv=split_newton(evaluator,profile.normalization,order)
        rows.append(dict(quadrature_order=order,newton_F_F=ff,newton_F_V=fv,newton_V_V=vv,
                         a2_coefficient=c2,a3_coefficient=c3,
                         a4_coefficient=c4+vv/8,a2_b2_coefficient=3*f4/32-3*fv/4,
                         b4_coefficient=-7*ff/8,aligned_longitudinal_norm_coefficient=3*f4/32))
    for key in ['newton_F_F','newton_F_V','newton_V_V']:
        assert abs(rows[-1][key]-rows[-2][key])<2e-9
    return dict(cases=rows,scope="Coefficients of the reduced energy restricted to h=a eta,s=b eta with integral eta^2=1. Split-domain polynomial Gaussian quadrature removes the Green-kernel diagonal kink and includes the whole-space inverse. This two-dimensional restriction is not an invariant dynamical subspace.")


def momentum_slice(evaluator,normalization):
    rows=[]
    for nr,na in [(32,20),(64,32),(96,40)]:
        profile=Profile(nr,na,evaluator,normalization)
        self_energy=float(profile.weight@(profile.f*profile.newton(profile.f)))
        for amplitude in [.02,.04,.08]:
            psi=np.ones_like(profile.f)
            for _ in range(100):
                updated=1+amplitude**2*profile.newton(profile.f*psi**-7)/8
                if max(abs(updated-psi))<2e-15:
                    psi=updated;break
                psi=updated
            residual=float(max(abs(psi-1-amplitude**2*profile.newton(profile.f*psi**-7)/8)))
            energy=amplitude**2*float(profile.weight@(profile.f*psi**-7))
            fourth=amplitude**2-7*self_energy*amplitude**4/8
            error=abs(energy-fourth)
            assert residual<3e-14 and error<.2*amplitude**6
            rows.append(dict(radial_points=nr,angular_points=na,amplitude=amplitude,
                             kappa_times_ADM_energy=energy,quartic_prediction=fourth,
                             remainder=error,integral_equation_residual=residual,
                             discretized_newton_self_energy=self_energy))
    return dict(cases=rows,scope="Full conformal scalar solve for the same compact TT profile on h=0. It checks the pure-momentum quartic term against the nonlinear boundary energy, with discretization error separated from amplitude order.")


def main():
    root=Path(__file__).resolve().parents[1]
    evaluator,seed=compact_profile()
    curvature,profile=compact_curvature(evaluator)
    exact_cubic=float(sy.N(sy.sympify(seed['exact_cubic_curvature_coefficient'])))
    assert abs(exact_cubic+float(profile.weight@profile.r3_bulk))<1e-10
    report=dict(exact_algebra=exact_identities(),compact_TT_seed=seed,compact_curvature=curvature,
                pointwise_scalar_source=pointwise_scalar(evaluator,profile.normalization),
                pointwise_kinetic=kinetic_pointwise(),nonlinear_momentum_kinetic=periodic_kinetic(),
                aligned_mode_coefficients=aligned_coefficients(evaluator,profile),
                full_momentum_slice=momentum_slice(evaluator,profile.normalization))
    sources=['REDUCED_TENSOR_HAMILTONIAN.md','scripts/reduced_tensor_hamiltonian_audit.py',
             'CANONICAL_METRIC_RECONSTRUCTION.md','scripts/canonical_metric_reconstruction_audit.py',
             'TENSOR_PACKET_SELF_GRAVITY.md','scripts/tensor_packet_self_gravity_audit.py',
             'SPATIAL_METRIC_VACUUM.md','PREPOTENTIAL_LATTICE_BRIDGE.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']=('A classical small-amplitude reduced TT Hamiltonian is derived through quartic '
                     'order from supplied asymptotically flat Einstein constraints. The quadratic '
                     'wave energy sources the conformal metric; the logarithmic kinetic cubic term '
                     'cancels and a nonzero cubic curvature interaction remains. This supplies a '
                     'nonlinear physical tensor target, not a microscopic phase, invariant finite-time '
                     'flow, quantum constraint construction or physical TOE.')
    target=root/'data/reduced_tensor_hamiltonian_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    counts={key:len(value['cases']) for key,value in report.items() if isinstance(value,dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target),cases=counts,total_cases=sum(counts.values()),
                          source_references=len(sources),scope=report['scope']),indent=2))


if __name__=='__main__':
    main()
