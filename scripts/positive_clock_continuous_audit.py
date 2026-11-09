#!/usr/bin/env python3
"""Correspondence checks for basis-free reconstruction and continuous flow.

Lean proves the algebraic and conditional continuous-time statements for
arbitrary finite capacity. Numerical ODE solves check the executable
Hamiltonian and convergence; they are not existence or continuum proofs.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse.linalg as sla
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def gram(A):
    return A.conj().T @ A


def half_polynomial(S):
    identity = np.eye(len(S), dtype=complex)
    return identity/2 + gram(S + 2*identity)/8


def transcription(model):
    """Independently assemble the definitions in the new Lean modules."""
    p = model.params
    A = [a.toarray() for a in model.ann]
    skew = [a-a.conj().T for a in A]
    scale = np.sqrt(p.hbar/2)
    S = scale*(A[0]+A[0].conj().T)
    Ps = -1j*scale*skew[0]
    F = half_polynomial(S)
    D = half_polynomial(-S)
    C = gram(F)
    raw_base = D@D@Ps
    base = (raw_base+raw_base.conj().T)/2
    P = -1j*scale*(skew[1]+skew[2])
    Qx = -1j*scale*(skew[1]-skew[2])
    pi = -1j*scale*(skew[3]+skew[4]+skew[5])
    phix = -1j*scale*(skew[3]-skew[4])
    phi = scale*sum(A[a]+A[a].conj().T for a in [3,4,5])
    M = (P@Qx+Qx@P+pi@phix+phix@pi)/2
    K = np.zeros_like(M)
    np.divide(M,1j*model.charge_difference,out=K,where=~model.same_charge)
    # Clock-only spectral theorem: neither sorting nor the eigenvectors
    # are required to preserve the occupation labels' charge sectors.
    eigenvalues,U = la.eigh(C)
    transformed = U.conj().T@K@U
    X = U@(2*transformed/(eigenvalues[:,None]+eigenvalues[None,:]))@U.conj().T
    L = base+X
    E = half_polynomial(L)
    static = gram(F)/2+gram(P@D)/2+gram(pi@D)/2
    growing = (gram(Qx@D)+gram(phix@D))/2
    growing += p.mass2/2*gram(phi@E@D)+p.quartic/4*gram(phi@phi@E@D)+p.vacuum*gram(E@D)
    errors = {name:float(la.norm(a-b)) for name,a,b in [
        ('clock',C,model.C),('base',base,model.Lbar),('source',M,model.source),
        ('longitudinal',L,model.L),('static_seed',static,model.seed_static),
        ('growing_seed',growing,model.seed_growing)]}
    assert max(errors.values()) < 5e-10, errors
    inverse_error = float(la.norm((C@X+X@C)/2-K))
    assert inverse_error < 5e-11
    assert la.norm(X-X.conj().T) < 5e-11
    minimum_clock = float(eigenvalues[0])
    assert minimum_clock >= 0.25-1e-12
    assert la.norm(C*model.charge_difference) < 1e-12
    assert la.norm(base*model.charge_difference) < 1e-12
    constraint = M-(C@(1j*model.charge_difference*L)+(1j*model.charge_difference*L)@C)/2
    identity_error = float(la.norm(constraint-M*model.same_charge))
    assert identity_error < 5e-11
    return dict(capacity=p.R,correction=p.correction,dimension=model.dim,
                transcription_errors=errors,minimum_clock_eigenvalue=minimum_clock,
                clock_basis_charge_defect=float(la.norm(U*model.charge_difference)),
                jordan_inverse_error=inverse_error,constraint_identity_error=identity_error)


def continuous_flow(R,correction):
    model = ConstraintReducedSpinModel(Parameters(R=R,flavors=6,correction=correction,
        hbar=0.2,vacuum=0.03,functional_order=2))
    p = model.params
    dimension = model.dim
    end = 0.3
    grid = np.linspace(0,end,7)
    def rhs(t,flat):
        return (-1j/p.hbar*model.matrix(t)@flat.reshape(dimension,dimension)).ravel()
    initial = np.eye(dimension,dtype=complex)
    result = solve_ivp(rhs,(0,end),initial.ravel(),method='DOP853',t_eval=grid,
                       rtol=2e-12,atol=2e-14)
    assert result.success,result.message
    projector = np.diag((model.charge==0).astype(float))
    unitarity = []
    covariance = []
    constraint = []
    for column in result.y.T:
        U = column.reshape(dimension,dimension)
        unitarity.append(float(la.norm(U.conj().T@U-initial)))
        covariance.append(float(la.norm(U.conj().T@projector@U-projector)))
        constraint.append(float(la.norm(model.constraint@U@projector)))
    assert max(unitarity) < 2e-9
    assert max(covariance) < 2e-9
    assert max(constraint) < 2e-11
    U = result.y[:,-1].reshape(dimension,dimension)
    state,_ = model.physical_packet()
    full = model.embed(state)
    exact_reference = U@full
    midpoint_errors = []
    for steps in [20,40]:
        midpoint_errors.append(float(la.norm(model.embed(model.evolve(state,end,steps))-exact_reference)))
    assert midpoint_errors[1] < midpoint_errors[0]/3
    frozen = sla.expm_multiply(-1j*end/p.hbar*model.matrix(end/2),full)
    frozen_error = float(la.norm(frozen-exact_reference))
    commutator = float(la.norm(model.matrix(0)@model.matrix(end)-model.matrix(end)@model.matrix(0)))
    assert commutator > 1e-5 and frozen_error > 1e-6
    return dict(capacity=R,correction=correction,dimension=dimension,
                full_propagator=True,time_interval=[0,end],sampled_times=len(grid),
                ode_function_evaluations=result.nfev,maximum_unitarity_error=max(unitarity),
                maximum_conserved_projector_error=max(covariance),maximum_constraint_error=max(constraint),
                unequal_time_hamiltonian_commutator_norm=commutator,
                frozen_midpoint_state_error=frozen_error,midpoint_state_errors_20_40=midpoint_errors)


def main():
    profiles = ['bare','second_order','exact']
    algebra = []
    for R in [2,4,6]:
        for correction in profiles:
            model = ConstraintReducedSpinModel(Parameters(R=R,flavors=6,correction=correction,
                functional_order=2,vacuum=0.03))
            algebra.append(transcription(model))
    flows = [continuous_flow(R,c) for R in [2,3] for c in profiles]
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/positive_clock_continuous_audit.py','scripts/constraint_reduced_spin_model.py',
               'scripts/quantum_areal_spin_model.py','scripts/holomorphic_tensor_phase_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalPositiveClockReconstruction','KFCausalContinuousConstraintFlow',
        'KFCausalConcreteClockConstraint','KFCausalReducedSpinHamiltonian',
        'KFCausalSpinSourceIdentity','KFCausalQuantumArealCandidate',
        'KFCausalFiniteOccupationLadders','KFCausalGradedSpinSource','KFCausalQuantumConstraintReduction']]
    report = dict(algebraic_correspondence=algebra,continuous_flows=flows,
        source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources},
        numerical_environment=dict(numpy=np.__version__,scipy=scipy.__version__),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Exact finite Lean construction and conditional preservation along global differentiable '
               'Schrodinger propagators; numerical full-space ODE checks and integrator convergence. '
               'Global propagator existence is not formalized here. The imposed physical sector, '
               'finite-clock response error, continuum limit and microscopic derivation remain separate.'))
    target = root/'data/positive_clock_continuous_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(f'{target}: {len(algebra)} operator comparisons and {len(flows)} full propagators passed.')


if __name__=='__main__':
    main()
