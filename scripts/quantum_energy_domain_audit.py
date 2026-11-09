#!/usr/bin/env python3
"""Energy control and limits of energy-based clock control.

Check finite propagator energy inequalities as matrix inequalities, search
for physical-sector occupation/energy witnesses, and verify the classical
positive-clock boundary. Finite spectra do not prove asymptotic coercivity.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import sympy as sy
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def model_at(R, profile):
    return ConstraintReducedSpinModel(Parameters(R=R, flavors=6, correction=profile,
        hbar=0.2, vacuum=0.03, functional_order=None))


def energy_flow(model):
    d = model.dim
    identity = np.eye(d, dtype=complex)
    def rhs(t, flat):
        return (-1j/model.params.hbar*model.matrix(t)@flat.reshape(d,d)).ravel()
    flows = {0.:identity}
    for end in [-0.2, 0.2]:
        result = solve_ivp(rhs, (0,end), identity.ravel(), method='DOP853',
                           t_eval=[end/2,end], rtol=2e-12, atol=2e-14)
        assert result.success, result.message
        flows.update({float(t):col.reshape(d,d) for t,col in zip(result.t,result.y.T)})
    transported = {}
    samples = []
    for t, U in sorted(flows.items()):
        H = model.matrix(t)
        Hdot = 2*np.exp(2*t)*model.growing
        Udot = -1j/model.params.hbar*H@U
        source = U.conj().T@Hdot@U
        derivative = Udot.conj().T@H@U+source+U.conj().T@H@Udot
        derivative_error = float(la.norm(derivative-source))
        assert derivative_error < 2e-10
        clock_margin = float(la.eigvalsh(H-model.C/2)[0])
        assert clock_margin > -2e-10
        transported[t] = U.conj().T@H@U
        unitarity = float(la.norm(U.conj().T@U-identity))
        assert unitarity < 2e-9
        samples.append(dict(time=t, derivative_identity_error=derivative_error,
                            minimum_clock_energy_margin=clock_margin, unitarity_error=unitarity))
    comparisons = []
    for s in sorted(flows):
        for t in sorted(flows):
            if s >= t:
                continue
            lower = float(la.eigvalsh(transported[t]-transported[s])[0])
            upper = float(la.eigvalsh(np.exp(2*(t-s))*transported[s]-transported[t])[0])
            clock_bound = 2*np.exp(2*(t-s))*transported[s]-flows[t].conj().T@model.C@flows[t]
            clock = float(la.eigvalsh(clock_bound)[0])
            assert min(lower, upper, clock) > -2e-9, (s,t,lower,upper,clock)
            comparisons.append(dict(start=s, end=t, minimum_energy_lower_margin=lower,
                minimum_energy_upper_margin=upper, minimum_clock_bound_margin=clock))
    return dict(capacity=model.params.R, profile=model.params.correction, dimension=d,
                samples=samples, all_state_matrix_comparisons=comparisons)


def occupation_witness(model):
    """Sharp finite coefficient in <N²> <= C_R(<H>+||psi||²), on charge zero."""
    H = model.matrix(0,physical=True)
    N = model.number[model.physical]
    d = len(N)
    values, vectors = la.eigh(np.diag(N*N), H+np.eye(d), subset_by_index=[d-1,d-1])
    psi = vectors[:,0]
    psi /= la.norm(psi)
    full = model.embed(psi)
    energy = float(np.vdot(psi,H@psi).real)
    moment = float(np.sum(abs(psi)**2*N*N))
    ratio = moment/(energy+1)
    assert abs(ratio-values[0]) < 1e-9
    residual = float(la.norm(N*N*psi-values[0]*(H+np.eye(d))@psi))
    assert residual < 2e-9
    return dict(capacity=model.params.R, physical_dimension=d, sharp_finite_coefficient=float(values[0]),
        energy=energy, second_occupation_moment=moment, generalized_eigenvector_residual=residual,
        boundary_probability=float(np.sum(abs(full[model.number == model.params.R])**2)),
        mean_clock_s=float(np.vdot(full,model.S@full).real),
        mean_clock_ps=float(np.vdot(full,model.Ps@full).real),
        scope='Finite spectral witness only; does not prove absence of a uniform quantum bound.')


def classical_domain():
    t = sy.symbols('t', real=True)
    c = 2*sy.exp(3*t/2)-1
    L = sy.log(3*c)-t/2
    rate = 3*sy.exp(3*t/2)
    assert sy.simplify(sy.diff(c,t)-rate) == 0
    assert sy.simplify(sy.diff(L,t)-(-sy.Rational(1,2)+rate/c)) == 0
    assert sy.simplify(sy.diff(rate,t)-3*rate/2) == 0
    crossing = -2*sy.log(2)/3
    assert sy.simplify(c.subs(t,crossing)) == 0
    energy = sy.simplify(c/2+rate)
    assert sy.simplify(energy-(4*sy.exp(3*t/2)-sy.Rational(1,2))) == 0
    assert sy.simplify(energy.subs(t,crossing)) == sy.Rational(3,2)
    samples = []
    for k in [1,2,4,6,8,10]:
        delta = 10.**(-k)
        time = float(crossing)+delta
        clock = np.expm1(1.5*delta)  # Stable at the exact boundary.
        s = np.log(clock)
        longitudinal = np.log(3)+s-time/2
        ps = clock*longitudinal
        E = 1.5+2*np.expm1(1.5*delta)
        assert 0 < clock and 1.5 < E < 3.5
        samples.append(dict(distance_from_boundary=delta, time=time, clock=clock,
                            chart_s=s, chart_ps=ps, energy=E))
    return dict(boundary_time=str(crossing), boundary_time_float=float(crossing),
                boundary_energy='3/2', near_boundary_samples=samples,
                implication='The exact classical positive-clock branch is not global for these initial data.')


def main():
    flows, witnesses = [], []
    for R in [2,3,4,5,6]:
        exact = model_at(R,'exact')
        witnesses.append(occupation_witness(exact))
        if R <= 4:
            flows.append(energy_flow(exact))
            flows.append(energy_flow(model_at(R,'bare')))
    classical = classical_domain()
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/clock_limit_exponential_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/quantum_energy_domain_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in [
        'KFCausalQuantumEnergyControl','KFCausalExponentialEnergyBound',
        'KFCausalClockEnergyObstruction','KFCausalVacuumClockDomain']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p,h in previous['source_sha256'].items())
    report = dict(energy_flows=flows, finite_occupation_witnesses=witnesses, classical_domain=classical,
        source_sha256=hashes, numerical_environment=dict(numpy=np.__version__,scipy=scipy.__version__,sympy=sy.__version__),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Lean proves a capacity-independent energy-growth factor and upper clock-expectation '
               'bound for the exponential model. Classical bounded energy does not control clock '
               'momentum, and some positive-clock solutions reach a finite-time branch boundary. '
               'The finite quantum spectral witnesses do not prove an asymptotic obstruction. '
               'Occupation propagation, infinite-dimensional domains, continuum correspondence '
               'and a TOE remain unproved.'))
    target = root/'data/quantum_energy_domain_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(f'{target}: {len(flows)} full propagator energy checks, {len(witnesses)} finite spectral witnesses, classical boundary verified.')
    print('Maximum derivative residual:',max(s['derivative_identity_error'] for f in flows for s in f['samples']))
    print('Maximum unitarity residual:',max(s['unitarity_error'] for f in flows for s in f['samples']))
    print('Finite occupation/energy coefficients:',[w['sharp_finite_coefficient'] for w in witnesses])


if __name__ == '__main__':
    main()
