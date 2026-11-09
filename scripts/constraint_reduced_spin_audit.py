#!/usr/bin/env python3
"""Exact symbolic and finite-matrix audit of the spatial-constraint repair."""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse.linalg as sla
import sympy as s

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def continuum_and_lattice():
    c,cx,Lx,P,Px,Qx,Qxx,pi,pix,fx,fxx,W,U,k,g,h = s.symbols(
        'c cx Lx P Px Qx Qxx pi pix fx fxx W U k g h',nonzero=True)
    E=P**2+g*Qx**2+k*pi**2+h*fx**2
    Ex=2*(P*Px+g*Qx*Qxx+k*pi*pix+h*fx*fxx)
    Wx=W*Lx+U*fx
    cd=W/c; cxd=Wx/c-W*cx/c**2
    Lxd=Ex/(2*c**2)+Wx/c**2-(E+2*W)*cx/c**3
    Pd=g*(Qxx/c-Qx*cx/c**2)
    Qxd=Px/c-P*cx/c**2
    pid=h*(fxx/c-fx*cx/c**2)-U/c
    fxd=k*(pix/c-pi*cx/c**2)
    rate=s.factor(Pd*Qx+P*Qxd+pid*fx+pi*fxd-cd*Lx-c*Lxd+2*cxd)
    assert rate==0

    # Independent canonical differentiation of the actual periodic graph
    # Hamiltonian, rather than assuming its continuum product rule.
    q=s.symbols('q0:4'); p=s.symbols('p0:4'); cs=s.symbols('c0:4',positive=True)
    ls=s.symbols('l0:4')
    H=sum(cs[i]/2+p[i]**2/(2*cs[i]) for i in range(4))
    H+=sum((1/cs[i]+1/cs[(i+1)%4])*(q[(i+1)%4]-q[i])**2/4 for i in range(4))
    qdot=[s.diff(H,p[i]) for i in range(4)]
    pdot=[-s.diff(H,q[i]) for i in range(4)]
    ldot=[-s.diff(H,cs[i]) for i in range(4)]
    cdot=[s.diff(H,ls[i]) for i in range(4)]
    equations=dict(zip(q+p+ls+cs,qdot+pdot+ldot+cdot))
    initial=dict(zip(q+p+ls+cs,[0,1,0,0]+[0]*8+[1]*4))
    derivatives=[]
    for j in range(4):
        prev,nxt=(j-1)%4,(j+1)%4
        D=p[j]*(q[nxt]-q[prev])/2-cs[j]*(ls[nxt]-ls[prev])/2+cs[nxt]-cs[prev]
        assert D.subs(initial)==0
        derivatives.append(s.simplify(sum(s.diff(D,v)*dv for v,dv in equations.items()).subs(initial)))
    assert derivatives==[s.Rational(1,4),0,-s.Rational(1,4),0]

    convergence=[]
    for N in [16,32,64,128,256]:
        dx=2*np.pi/N; x=np.arange(N)*dx
        q=np.cos(x)+0.2*np.cos(2*x)
        dq=(np.roll(q,-1)-np.roll(q,1))/(2*dx)
        lap=(np.roll(q,-1)-2*q+np.roll(q,1))/dx**2
        local_grad=((np.roll(q,-1)-q)**2+(q-np.roll(q,1))**2)/(4*dx**2)
        defect=lap*dq-(np.roll(local_grad,-1)-np.roll(local_grad,1))/(2*dx)
        convergence.append(dict(sites=N,spacing=dx,rms_initial_constraint_rate=float(la.norm(defect)/np.sqrt(N))))
    print('Continuum propagation and exact four-site counterexample verified.',flush=True)
    return dict(continuum_constraint_rate=str(rate),four_site_initial_constraint=[0]*4,
                four_site_constraint_derivative=[str(v) for v in derivatives],
                smooth_grid_samples=convergence,
                scope='Continuum identity along supplied smooth solutions; graph inconsistency is exact at finite spacing.')


def finite_reduction(R,correction='second_order',functional_order=2):
    model=ConstraintReducedSpinModel(Parameters(R=R,flavors=6,correction=correction,
                                              functional_order=functional_order))
    p=model.params; physical=model.physical; ix=np.ix_(physical,physical)
    n=model.number; x=(n-1)/R
    if correction=='exact':
        lower=np.ones(model.dim); upper=(n<R).astype(float)
    else:
        f=lambda v:np.ones_like(v) if correction=='bare' else 1+v/2+3*v*v/8
        lower=(1-x)*f(x)**2
        upper=(1-n/R)*f(n/R)**2
    expected_mean=np.diag(p.hbar*(lower+upper)/2*model.charge)
    mean_error=float(la.norm(model.mean_source-expected_mean))
    local_identity_error=float(la.norm(model.constraint-model.mean_source))
    constraint_sector_error=float(la.norm(model.constraint[:,physical]))
    assert mean_error<2e-12 and local_identity_error<2e-11 and constraint_sector_error<2e-11
    assert la.norm(model.C*model.charge_difference)<1e-13
    assert la.norm(model.Qx-1j*model.charge_difference*model.Q)<2e-12
    assert la.norm(model.phix-1j*model.charge_difference*model.phi)<2e-12
    assert la.norm(model.L-model.L.conj().T)<2e-11
    assert la.norm(model.L*model.same_charge-model.Lbar)<2e-11
    assert la.eigvalsh(model.C)[0]>0
    H=model.matrix(0.1)
    assert la.norm(H-H.conj().T)<2e-11 and la.norm(H*model.charge_difference)==0
    minimum_energy=float(la.eigvalsh(H[ix])[0])
    assert minimum_energy>0

    # Independent finite translation average: charge differences are at
    # most 2R, so 2R+1 equally spaced phases integrate every entry exactly.
    seed=model.seed_static+np.exp(0.2)*model.seed_growing
    averaged=np.zeros_like(seed)
    for angle in 2*np.pi*np.arange(2*R+1)/(2*R+1):
        averaged+=np.exp(1j*angle*model.charge_difference)*seed/(2*R+1)
    averaging_error=float(la.norm(averaged-H))
    assert averaging_error<2e-11

    # A symmetrized ordinary inverse is not an exact Jordan inverse.
    primitive=np.zeros_like(model.source)
    np.divide(model.source,1j*model.charge_difference,out=primitive,where=~model.same_charge)
    invC=la.inv(model.C)
    naiveL=model.Lbar+(invC@primitive+primitive@invC)/2
    naiveLx=1j*model.charge_difference*naiveL
    naiveD=model.source-(model.C@naiveLx+naiveLx@model.C)/2
    naive_error=float(la.norm(naiveD[:,physical]))

    state,preparation_probability=model.physical_packet()
    final20=model.evolve(state,0.1,20)
    final40=model.evolve(state,0.1,40)
    full=model.embed(final40)
    final_constraint=float(la.norm(model.constraint@full))
    assert final_constraint<2e-11 and abs(la.norm(full)-1)<2e-11
    clock_rate=float((1j/p.hbar*np.vdot(full,(H@model.C-model.C@H)@full)).real)
    potential=float((np.exp(0.2)*np.vdot(full,model.potential@full)).real)
    gradient=float((np.exp(0.2)*np.vdot(full,model.gradient@full)).real)
    assert gradient>0 and potential>0
    # The physical sector has many states and a nonconstant Hamiltonian.
    assert len(physical)>1 and la.norm(H[ix]-np.eye(len(physical))*minimum_energy)>1e-3

    # Full-space frozen evolution cross-checks the restriction independently.
    frozen=sla.expm_multiply(-0.1j/p.hbar*H,model.embed(state))
    restricted=sla.expm_multiply(-0.1j/p.hbar*H[ix],state)
    full_vs_restricted=float(la.norm(frozen-model.embed(restricted)))
    assert full_vs_restricted<2e-11
    print(f'R={R}, dim={model.dim}, physical={len(physical)}, constraint={final_constraint:.3g}',flush=True)
    return dict(capacity=R,dimension=model.dim,physical_dimension=len(physical),
                correction=correction,functional_order=functional_order,
                source_mean_identity_error=mean_error,local_constraint_identity_error=local_identity_error,
                constraint_on_entire_physical_sector=constraint_sector_error,
                symmetrized_inverse_constraint_error=naive_error,
                translation_average_error=averaging_error,minimum_physical_energy=minimum_energy,
                physical_preparation_probability=preparation_probability,
                final_constraint_norm=final_constraint,norm_error=abs(float(la.norm(full))-1),
                time_step_state_difference=float(la.norm(final20-final40)),
                full_vs_restricted_evolution_error=full_vs_restricted,
                clock_rate=clock_rate,potential_energy=potential,clock_rate_defect=abs(clock_rate-potential),
                gradient_energy=gradient)


def main():
    np.random.seed(0)
    report=dict(classical=continuum_and_lattice(),
                finite_quantum=[finite_reduction(R) for R in [2,3,4,5,6]],
                comparisons=[finite_reduction(4,'exact',None),finite_reduction(4,'bare',2)])
    root=Path(__file__).resolve().parents[1]
    sources=['scripts/constraint_reduced_spin_model.py','scripts/constraint_reduced_spin_audit.py',
             'scripts/quantum_areal_spin_model.py','scripts/holomorphic_tensor_phase_audit.py',
             'UnifiedTheory/Audit/KFCausalArealConstraintPropagation.lean',
             'UnifiedTheory/Audit/KFCausalQuantumConstraintReduction.lean']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['numerical_environment']=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=s.__version__)
    report['scope']=('Specified nonlocal Fourier reduction with one Q harmonic pair, one scalar harmonic pair, '
                     'a scalar zero mode and a homogeneous geometry clock. The local symmetrized constraint '
                     'is reconstructed; total charge zero is imposed and preserved. No microscopic selection, '
                     'unreduced quantum Dirac algebra, spatial continuum limit, full 3D gravity or TOE is proved.')
    target=root/'data/constraint_reduced_spin_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,flush=True)


if __name__=='__main__':
    main()
