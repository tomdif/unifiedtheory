#!/usr/bin/env python3
"""Clock error separation and correspondence for the exponential model.

Exact symbolic counterexamples, finite ladder identities and state bounds,
and independent matrix-function/ODE checks. No continuum claim is made.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters
from holomorphic_tensor_phase_audit import finite_operators


def symbolic_clock():
    s, p = sy.symbols('s p', real=True)
    half = lambda x: 1+x/2+x*x/8
    C = half(s)**2
    D = half(-s)
    L = D**2*p
    potential = half(L)**2*D**2
    force = sy.diff(C, s)*sy.diff(C/2+potential, p)
    jacobian = sy.diff(C, s)*D**2
    assert sy.expand(jacobian-1-s**2*(s**5-2*s**4+16*s**2+64*s-128)/1024) == 0
    exact_potential = sy.exp(sy.exp(-s)*p)*sy.exp(-s)
    assert sy.simplify(sy.exp(s)*sy.diff(exact_potential, p)-exact_potential) == 0
    rows = []
    for x in [-2, 0, 1]:
        vals = [sy.factor(expr.subs({s:x, p:0})) for expr in [potential, force, force-potential]]
        rows.append(dict(s=x, p=0, potential=str(vals[0]), clock_rate=str(vals[1]), defect=str(vals[2])))
    assert rows[-1]['defect'] == '-1225/65536'
    return dict(polynomial_jacobian_defect=str(sy.factor(jacobian-1)),
                polynomial_points=rows, exponential_classical_identity=True)


def ladder_case(m, R, profile):
    states, ops = finite_operators(m, m, R, R)
    states = np.asarray(states)
    N = states.sum(axis=1)
    x = (N-1)/R
    factors = np.ones(len(N)) if profile == 'bare' else 1/np.sqrt(1-x)
    A = ops[0] @ sp.diags(factors)
    bracket = A@A.conj().T-A.conj().T@A
    coefficient = 1-(N+states[:,0])/R if profile == 'bare' else 1-(states[:,0]+1)*(N == R)
    matrix_error = float(la.norm((bracket-sp.diags(coefficient)).data))
    assert matrix_error < 1e-10
    rng = np.random.default_rng(1000*m+10*R+(profile == 'exact'))
    psi = rng.normal(size=len(N))+1j*rng.normal(size=len(N))
    psi *= 7/la.norm(psi)  # The theorem also covers unnormalized vectors.
    probability = abs(psi)**2
    defect = float(np.sum((1-coefficient)*probability))
    matrix_expectation = np.vdot(psi, psi-bracket@psi)
    assert abs(matrix_expectation-defect) < 1e-10
    moment_order = 1 if profile == 'bare' else 2
    bound = float(2*np.sum(N**moment_order*probability)/R)
    assert -1e-11 <= defect <= bound+1e-10
    top = np.flatnonzero(states[:,0] == R)[0]
    top_defect = float(1-coefficient[top])
    assert abs(top_defect-(2 if profile == 'bare' else R+1)) < 1e-12
    if profile == 'exact':
        below = psi*(N < R)
        assert la.norm(below-bracket@below) < 1e-10
    return dict(flavors=m, capacity=R, profile=profile, dimension=len(N),
                matrix_identity_error=matrix_error, expectation_error=float(abs(matrix_expectation-defect)),
                defect=defect, moment_order=moment_order, moment_bound=bound, top_state_defect=top_defect)


def exponential_case(R, profile):
    model = ConstraintReducedSpinModel(Parameters(R=R, flavors=6, correction=profile,
        hbar=0.2, vacuum=0.03, functional_order=None))
    p = model.params
    A = [a.toarray() for a in model.ann]
    skew = [a-a.conj().T for a in A]
    scale = np.sqrt(p.hbar/2)
    S = scale*(A[0]+A[0].conj().T)
    Ps = -1j*scale*skew[0]
    gram = lambda X: X.conj().T@X
    # Matrix exponentials here are independent of the model's clock-block
    # eigendecompositions. Jordan reconstruction uses its clock eigenbasis.
    F, D = la.expm(S/2), la.expm(-S/2)
    C = gram(F)
    rawbase = D@D@Ps
    base = (rawbase+rawbase.conj().T)/2
    P = -1j*scale*(skew[1]+skew[2])
    Qx = -1j*scale*(skew[1]-skew[2])
    pi = -1j*scale*(skew[3]+skew[4]+skew[5])
    phix = -1j*scale*(skew[3]-skew[4])
    phi = scale*sum(A[j]+A[j].conj().T for j in [3,4,5])
    source = (P@Qx+Qx@P+pi@phix+phix@pi)/2
    primitive = np.zeros_like(source)
    np.divide(source, 1j*model.charge_difference, out=primitive, where=~model.same_charge)
    eig, U = la.eigh(C)
    L = base+U@(2*(U.conj().T@primitive@U)/(eig[:,None]+eig[None,:]))@U.conj().T
    E = la.expm(L/2)
    static = gram(F)/2+gram(P@D)/2+gram(pi@D)/2
    growing = (gram(Qx@D)+gram(phix@D))/2
    growing += p.mass2/2*gram(phi@E@D)+p.quartic/4*gram(phi@phi@E@D)+p.vacuum*gram(E@D)
    errors = {name:float(la.norm(a-b)) for name,a,b in [
        ('clock',C,model.C), ('base',base,model.Lbar), ('source',source,model.source),
        ('longitudinal',L,model.L), ('static_seed',static,model.seed_static),
        ('growing_seed',growing,model.seed_growing)]}
    assert max(errors.values()) < 2e-10, errors
    inverse_error = float(la.norm(F@D-np.eye(model.dim)))
    assert inverse_error < 2e-11
    constraint = source-(C@(1j*model.charge_difference*L)+(1j*model.charge_difference*L)@C)/2
    identity_error = float(la.norm(constraint-source*model.same_charge))
    assert identity_error < 2e-10
    row = dict(capacity=R, profile=profile, dimension=model.dim, transcription_errors=errors,
               clock_inverse_error=inverse_error, constraint_identity_error=identity_error,
               minimum_clock_eigenvalue=float(eig[0]))
    assert eig[0] > 0
    if R <= 3 and profile != 'second_order':
        d = model.dim
        identity = np.eye(d, dtype=complex)
        def rhs(t, flat):
            return (-1j/p.hbar*model.matrix(t)@flat.reshape(d,d)).ravel()
        grid = np.linspace(0, 0.2, 5)
        result = solve_ivp(rhs, (0, 0.2), identity.ravel(), method='DOP853',
                           t_eval=grid, rtol=2e-12, atol=2e-14)
        assert result.success, result.message
        projector = np.diag((model.charge == 0).astype(float))
        state, _ = model.physical_packet()
        initial = model.embed(state)
        samples = []
        for t, col in zip(grid, result.y.T):
            flow = col.reshape(d,d)
            psi = flow@initial
            probabilities = abs(psi)**2
            N = model.number
            coeff = 1-(N+model.states[:,0])/R if profile == 'bare' else 1-(model.states[:,0]+1)*(N == R)
            defect = float(np.sum((1-coeff)*probabilities))
            k = 1 if profile == 'bare' else 2
            moment = float(np.sum(N**k*probabilities))
            assert -1e-12 <= defect <= 2*moment/R+1e-12
            samples.append(dict(time=float(t), moment=moment, ccr_defect=defect,
                ccr_bound=2*moment/R, unitarity_error=float(la.norm(flow.conj().T@flow-identity)),
                constraint_error=float(la.norm(constraint@flow@projector))))
        assert max(x['unitarity_error'] for x in samples) < 2e-9
        assert max(x['constraint_error'] for x in samples) < 2e-10
        row['flow_samples'] = samples
    return row


def main():
    symbolic = symbolic_clock()
    ladders = [ladder_case(m, R, profile) for m in [1,2,6] for R in [1,2,4,6]
               for profile in ['bare','exact']]
    matrices = [exponential_case(R, profile) for R in [2,3,4]
                for profile in ['bare','second_order','exact']]
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/global_spin_dynamics_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/clock_limit_exponential_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalFiniteClockCCR','KFCausalPolynomialClockObstruction','KFCausalExponentialClockDynamics']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p,h in previous['source_sha256'].items())
    report = dict(symbolic=symbolic, ladder_cases=ladders, exponential_models=matrices,
        source_sha256=hashes, numerical_environment=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=sy.__version__),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Exact finite CCR identities and state moment bounds; conditional moment-controlled '
               'CCR limits; a classical fixed-polynomial clock counterexample and exponential repair; '
               'exact finite global constrained dynamics of the exponential variant. '
               'Uniform evolved moment bounds, infinite-dimensional domains, spatial continuum, '
               'microscopic sector selection and a TOE remain unproved.'))
    target = root/'data/clock_limit_exponential_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(f'{target}: {len(ladders)} ladder cases, {len(matrices)} exponential models, '
          f'{sum("flow_samples" in row for row in matrices)} global-flow comparisons passed.')
    print('Maximum transcription error:',max(max(row['transcription_errors'].values()) for row in matrices))
    print('Maximum constraint identity error:',max(row['constraint_identity_error'] for row in matrices))


if __name__ == '__main__':
    main()
