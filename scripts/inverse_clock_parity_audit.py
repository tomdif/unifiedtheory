#!/usr/bin/env python3
"""Audit exact-amplitude parity coercivity of the exponential spin model.

The finite matrix checks test transcription of the Lean identities and
all-state lower bounds. They do not establish an infinite-dimensional
limit, occupation propagation, or semiclassical correspondence.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def gram(A):
    return A.conj().T@A


def minimum(A):
    assert la.norm(A-A.conj().T) < 2e-8
    return float(la.eigvalsh(A)[0])


def inspect(model):
    R, h = model.params.R, model.params.hbar
    identity = np.eye(model.dim)
    parity = np.diag((-1.)**(R+model.number))
    ng = model.states[:,1]+model.states[:,2]
    number = np.diag(ng)
    boundary = np.diag((ng+2)*(model.number == R))
    loops = sum((A.toarray()@A.conj().T.toarray()+A.conj().T.toarray()@A.toarray()
                 for A in model.ann[1:3]))
    pair = .5*(gram(model.P@model.D)+gram(model.Qx@model.D))*model.same_charge
    inverse = gram(model.D)
    boundary_clock = model.D.conj().T@boundary@model.D
    identities = dict(
        parity_involution=la.norm(parity@parity-identity),
        parity_clock_anticommutation=la.norm(parity@model.S+model.S@parity),
        inverse_parity_congruence=la.norm(model.D@parity@model.D-parity),
        clock_parity_congruence=la.norm(model.F@parity@model.F-parity),
        exact_inverse=la.norm(model.C@inverse-identity),
        exact_loops=la.norm(loops-(2*identity+2*number-boundary)),
        exact_gravity_pair=la.norm(pair-(h*inverse+h*model.D.conj().T@number@model.D-h/2*boundary_clock)),
        clock_positive_remainder=la.norm(model.C-parity-model.F.conj().T@(identity-parity)@model.F))
    assert max(identities.values()) < 2e-8, (R,h,identities)
    margins = dict(loops_minus_parity=minimum(loops-(identity-parity)),
        clock_minus_parity=minimum(model.C-parity),
        inverse_minus_parity=minimum(inverse-parity),
        gravity_pair_minus_parity=minimum(pair-h/2*(inverse-parity)))
    assert min(margins.values()) > -2e-8, (R,h,margins)
    times = []
    alpha = min(1,h)
    for t in [-.5,-.2,0.,.2,.5]:
        beta = min(1,np.exp(2*t))
        H = model.matrix(t)
        lower = minimum(H-beta*alpha/2*inverse)
        assert lower > -2e-8, (R,h,t,lower)
        row = dict(time=t, coefficient=beta*alpha/2, minimum_uniform_inverse_margin=lower)
        if t >= 0:
            raw = minimum(H-(model.C/2+h*inverse-h/2*boundary_clock))
            assert raw > -2e-8
            row['minimum_boundary_corrected_margin'] = raw
        times.append(row)
    # Independent all-state generalized eigenvalue; not a fitted proof coefficient.
    sharp = float(la.eigvalsh(model.matrix(0),inverse,subset_by_index=[0,0])[0])
    assert sharp >= alpha/2-2e-8
    return dict(capacity=R,hbar=h,dimension=model.dim,
        potential_parameters=dict(mass2=model.params.mass2,quartic=model.params.quartic,vacuum=model.params.vacuum),
        identity_errors={k:float(v) for k,v in identities.items()},
        minimum_positive_remainders=margins,time_samples=times,
        sharp_finite_inverse_coefficient=sharp,proved_capacity_uniform_coefficient=alpha/2)


def evolution(model):
    d = model.dim
    identity = np.eye(d,dtype=complex)
    inverse = gram(model.D)
    H0 = model.matrix(0)
    alpha = min(1,model.params.hbar)
    def rhs(t,flat):
        return (-1j/model.params.hbar*model.matrix(t)@flat.reshape(d,d)).ravel()
    rows = []
    for end in [-.2,.2]:
        result = solve_ivp(rhs,(0,end),identity.ravel(),method='DOP853',
            t_eval=[end/2,end],rtol=2e-12,atol=2e-14)
        assert result.success,result.message
        for t,flat in zip(result.t,result.y.T):
            U = flat.reshape(d,d)
            beta = min(1,np.exp(2*t))
            energy_factor = max(1,np.exp(2*t))
            coefficient = 2*energy_factor/(beta*alpha)
            margin = minimum(coefficient*H0-U.conj().T@inverse@U)
            clock_margin = minimum(2*energy_factor*H0-U.conj().T@model.C@U)
            unitary = float(la.norm(U.conj().T@U-identity))
            assert min(margin,clock_margin) > -2e-8
            assert unitary < 2e-9
            rows.append(dict(time=float(t),inverse_energy_factor=float(coefficient),
                minimum_evolved_inverse_margin=margin,minimum_evolved_clock_margin=clock_margin,
                unitarity_error=unitary))
    return dict(capacity=model.params.R,hbar=model.params.hbar,dimension=d,samples=rows)


def main():
    cases,flows = [],[]
    for R in [1,2,3,4]:
        for h in [.1,.2,.5,1.,2.]:
            model = ConstraintReducedSpinModel(Parameters(R=R,flavors=6,correction='exact',
                hbar=h,mass2=0,quartic=0,vacuum=0,functional_order=None))
            cases.append(inspect(model))
    for R in [2,3,4,5]:
        model = ConstraintReducedSpinModel(Parameters(R=R,flavors=6,correction='exact',
            hbar=.2,vacuum=.03,functional_order=None))
        cases.append(inspect(model))
        if R <= 4:
            flows.append(evolution(model))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/quantum_energy_domain_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/inverse_clock_parity_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalGravityPairCoercivity','KFCausalInverseClockEnergy',
        'KFCausalOccupationParity','KFCausalUniformInverseClock']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p,h in previous['source_sha256'].items())
    report = dict(matrix_cases=cases,evolution_cases=flows,source_sha256=hashes,
        numerical_environment=dict(numpy=np.__version__,scipy=scipy.__version__),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Exact amplitude compensation and exact exponentials. Lean derives H(t)>= '
               'min(1,exp(2t))*min(1,hbar)*C^{-1}/2 for every finite capacity and all states, '
               'with nonnegative potential coefficients and hbar>=0. Positive hbar and the '
               'proved energy-growth bound give inverse-clock expectation control with no '
               'boundary-tail assumption. Constants degenerate as hbar tends to zero. '
               'Occupation/momentum propagation, operator domains and convergence, physical '
               'identification and a TOE remain unproved.'))
    target = root/'data/inverse_clock_parity_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(f'{target}: {len(cases)} matrix cases, {len(flows)} full propagators, {len(hashes)} source hashes.')
    print('Maximum identity residual:',max(max(c['identity_errors'].values()) for c in cases))
    print('Minimum all-time inverse margin:',min(s['minimum_uniform_inverse_margin'] for c in cases for s in c['time_samples']))
    print('Maximum unitarity residual:',max(s['unitarity_error'] for f in flows for s in f['samples']))


if __name__ == '__main__':
    main()
