#!/usr/bin/env python3
"""Full regularized finite dynamics and an infinite-coordinate trial vector.

Independent matrix transcription, all-state evolution inequalities, and
quadrature for the proved homogeneous Gaussian form-domain supplier. No
infinite-capacity, regulator-removal or full physical limit is claimed.
"""
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import scipy
import scipy.linalg as la
from scipy.integrate import solve_ivp

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters
from regularized_constraint_spin_model import RegularizedConstraintSpinModel


def gram(A):
    return A.conj().T@A


def minimum(A):
    assert la.norm(A-A.conj().T) < 2e-9
    return float(la.eigvalsh(A)[0])


def matrix_case(R, profile, epsilon):
    p = Parameters(R=R,flavors=6,correction=profile,hbar=.2,vacuum=.03,functional_order=None)
    m = RegularizedConstraintSpinModel(p,epsilon)
    ann = [a.toarray() for a in m.ann]
    skew = [a-a.conj().T for a in ann]
    scale = np.sqrt(p.hbar/2)
    S = scale*(ann[0]+ann[0].conj().T)
    Ps = -1j*scale*skew[0]
    F,D = la.expm(S/2),la.expm(-S/2)
    C = gram(F)
    mobility = la.solve(C+epsilon*np.eye(m.dim),np.eye(m.dim),assume_a='pos')
    base = (mobility@Ps+Ps@mobility)/2
    P = -1j*scale*(skew[1]+skew[2])
    Qx = -1j*scale*(skew[1]-skew[2])
    pi = -1j*scale*(skew[3]+skew[4]+skew[5])
    phix = -1j*scale*(skew[3]-skew[4])
    phi = scale*sum(ann[j]+ann[j].conj().T for j in [3,4,5])
    source = (P@Qx+Qx@P+pi@phix+phix@pi)/2
    primitive = np.zeros_like(source)
    np.divide(source,1j*m.charge_difference,out=primitive,where=~m.same_charge)
    values,U = la.eigh(C)
    L = base+U@(2*(U.conj().T@primitive@U)/(values[:,None]+values[None,:]))@U.conj().T
    E = la.expm(L/2)
    K = gram(F)/2+gram(P@D)/2+gram(pi@D)/2
    V = (gram(Qx@D)+gram(phix@D))/2
    V += p.mass2/2*gram(phi@E@D)+p.quartic/4*gram(phi@phi@E@D)+p.vacuum*gram(E@D)
    errors = {key:float(la.norm(a-b)) for key,a,b in [
        ('clock',C,m.C),('mobility',mobility,m.mobility.toarray()),('base',base,m.Lbar),
        ('source',source,m.source),('longitudinal',L,m.L),('static_seed',K,m.seed_static),
        ('growing_seed',V,m.seed_growing)]}
    assert max(errors.values()) < 2e-10,errors
    constraint = source-(C@(1j*m.charge_difference*L)+(1j*m.charge_difference*L)@C)/2
    identity_error = float(la.norm(constraint-source*m.same_charge))
    assert identity_error < 2e-10
    projector = np.diag((m.charge==0).astype(float))
    assert la.norm(constraint@projector) < 2e-10
    free = RegularizedConstraintSpinModel(Parameters(R=R,flavors=6,correction=profile,
        hbar=.2,mass2=0,quartic=0,vacuum=0,functional_order=None),0)
    margins = []
    for t in [-.2,0.,.2]:
        H = m.matrix(t)
        row = dict(time=t,minimum_hamiltonian=minimum(H),
            minimum_added_potential=minimum(H-free.matrix(t)),minimum_clock_margin=minimum(H-C/2))
        if profile=='exact':
            alpha = min(1,np.exp(2*t))*min(1,p.hbar)/2
            row['minimum_inverse_clock_margin'] = minimum(H-alpha*gram(D))
        assert min(v for k,v in row.items() if k!='time') > -2e-10,row
        margins.append(row)
    zero_error = None
    if epsilon==0:
        old = ConstraintReducedSpinModel(p)
        zero_error = max(float(la.norm(m.matrix(t)-old.matrix(t))) for t in [-.2,0,.2])
        assert zero_error < 2e-10
    return m,dict(capacity=R,profile=profile,epsilon=epsilon,dimension=m.dim,
        transcription_errors=errors,constraint_identity_error=identity_error,
        zero_regulator_hamiltonian_error=zero_error,operator_margins=margins)


def flow_case(m):
    identity = np.eye(m.dim,dtype=complex)
    flows = {0.:identity}
    def rhs(t,flat):
        return (-1j/m.params.hbar*m.matrix(t)@flat.reshape(m.dim,m.dim)).ravel()
    for end in [-.2,.2]:
        result = solve_ivp(rhs,(0,end),identity.ravel(),method='DOP853',t_eval=[end/2,end],
            rtol=2e-12,atol=2e-14)
        assert result.success,result.message
        flows.update({float(t):flat.reshape(m.dim,m.dim) for t,flat in zip(result.t,result.y.T)})
    projector = np.diag((m.charge==0).astype(float))
    samples,transported = [],{}
    for t,U in sorted(flows.items()):
        H = m.matrix(t)
        Hdot = 2*np.exp(2*t)*m.growing
        Udot = -1j/m.params.hbar*H@U
        derivative_error = float(la.norm(Udot.conj().T@H@U+U.conj().T@H@Udot))
        unity = float(la.norm(gram(U)-identity))
        constraint_error = float(la.norm(m.constraint@U@projector))
        assert derivative_error < 2e-10
        assert unity < 2e-9 and constraint_error < 2e-10
        samples.append(dict(time=t,unitarity_error=unity,constraint_error=constraint_error,
            energy_derivative_cancellation_error=derivative_error,
            minimum_energy_source=minimum(U.conj().T@Hdot@U)))
        transported[t] = U.conj().T@H@U
    comparisons = []
    for s in sorted(flows):
        for t in sorted(flows):
            if s>=t:
                continue
            beta = min(1,np.exp(2*t))*min(1,m.params.hbar)
            U = flows[t]
            upper = np.exp(2*(t-s))*transported[s]
            row = dict(start=s,end=t,
                minimum_energy_increase=minimum(transported[t]-transported[s]),
                minimum_energy_growth_margin=minimum(upper-transported[t]),
                minimum_evolved_clock_margin=minimum(2*upper-U.conj().T@m.C@U),
                minimum_evolved_inverse_margin=minimum(2*upper/beta-U.conj().T@gram(m.D)@U))
            assert min(v for k,v in row.items() if k not in ['start','end']) > -2e-9,row
            comparisons.append(row)
    return dict(capacity=m.params.R,epsilon=m.epsilon,dimension=m.dim,
        samples=samples,all_state_comparisons=comparisons)


def gaussian_trial_checks():
    rows = []
    with mp.workdps(50):
        h = mp.mpf('.2')
        floor = mp.exp(-mp.pi/2)/16
        ceiling = mp.quad(lambda q:(2+2*q*q)*mp.exp(-2*mp.pi*q*q),[-mp.inf,0,mp.inf])
        for epsilon in ['0.01','0.1','1.0']:
            e = mp.mpf(epsilon)
            def c(q):
                return e*mp.lambertw(mp.exp(q/e)/e).real
            def g2(q):
                return mp.exp(-2*mp.pi*q*q)
            norm = mp.quad(lambda q:c(q)*g2(q),[-mp.inf,0,mp.inf])
            clock = mp.quad(lambda q:c(q)**2*g2(q),[-mp.inf,0,mp.inf])
            potential = mp.quad(lambda k:mp.exp(2*mp.pi*h*k)*g2(k),[-mp.inf,0,mp.inf])
            exact = mp.exp(mp.pi*h*h/2)/mp.sqrt(2)
            assert norm>0 and clock>0 and potential>0
            assert floor<=norm<=ceiling and clock<=ceiling
            assert abs(potential-exact)<mp.mpf('1e-40')
            for q in [-5,-1,0,1,5]:
                assert 0<c(q)<=1+abs(q)
                assert c(q)**2<=2+2*q*q
                assert min(q,1)<=c(q)
            energy = (clock/2+potential)/norm
            uniform_bound = (ceiling/2+potential)/floor
            assert energy<=uniform_bound
            modulations = []
            for p in [-1,0,1]:
                shifted = mp.quad(lambda k:mp.exp(2*mp.pi*h*k)*g2(k-p),[-mp.inf,p,mp.inf])
                expected = mp.exp(2*mp.pi*h*p)*exact
                assert abs(shifted-expected)<mp.mpf('1e-40')
                modulations.append(dict(momentum=p,potential_form_integral=mp.nstr(shifted,30),
                    normalized_unit_vacuum_energy=mp.nstr((clock/2+shifted)/norm,30),
                    regulator_uniform_energy_bound=mp.nstr((ceiling/2+shifted)/floor,30)))
            rows.append(dict(epsilon=epsilon,hbar=str(h),norm_square=mp.nstr(norm,30),
                clock_form_integral=mp.nstr(clock,30),potential_form_integral=mp.nstr(potential,30),
                potential_integral_check_error=mp.nstr(abs(potential-exact),8),
                normalized_unit_vacuum_energy=mp.nstr(energy,30),uniform_norm_floor=mp.nstr(floor,30),
                uniform_form_ceiling=mp.nstr(ceiling,30),regulator_uniform_energy_bound=mp.nstr(uniform_bound,30),
                momentum_modulations=modulations))
    return rows


def fourier_modulation_checks():
    rows = []
    with mp.workdps(50):
        for p in [-1,mp.mpf('.5'),1]:
            for k in [-1,0,1]:
                actual = mp.quad(lambda q:mp.exp(-2j*mp.pi*q*k)*mp.exp(2j*mp.pi*p*q)*
                    mp.exp(-mp.pi*q*q),[-mp.inf,0,mp.inf])
                expected = mp.exp(-mp.pi*(k-p)**2)
                error = abs(actual-expected)
                assert error<mp.mpf('1e-40')
                rows.append(dict(momentum=str(p),frequency=k,transform_error=mp.nstr(error,8)))
    return rows


def main():
    matrices,flows = [],[]
    for R in [2,3,4]:
        for profile in ['bare','exact']:
            for epsilon in [0.,.01,.1,1.]:
                m,row = matrix_case(R,profile,epsilon)
                matrices.append(row)
                if profile=='exact' and R<=3 and epsilon in [.1,1.]:
                    flows.append(flow_case(m))
    trials = gaussian_trial_checks()
    fourier_samples = fourier_modulation_checks()
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/longitudinal_domain_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/regularized_constraint_spin_model.py',
        'scripts/regularized_spin_dynamics_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in ['KFCausalRegularizedClockDatum',
        'KFCausalRegularizedSpinDynamics','KFCausalRegularizedGaussianCore',
        'KFCausalRegularizedTrialBounds','KFCausalFourierUniqueness',
        'KFCausalRegularizedGaussianTotality','KFCausalRegularizedFormDomain']]
    hashes = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p]==h for p,h in previous['source_sha256'].items())
    report = dict(matrix_cases=matrices,flow_cases=flows,homogeneous_trial_vectors=trials,
        fourier_modulation_samples=fourier_samples,
        source_sha256=hashes,numerical_environment=dict(numpy=np.__version__,scipy=scipy.__version__,mpmath=mp.__version__),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('The full finite regularized six-mode Hamiltonian has proved unique global unitary, '
               'constraint-preserving dynamics and energy/clock bounds. The homogeneous '
               'infinite-coordinate form has a constructed dense linear domain and normalized '
               'Gaussian-dressed states with regulator-uniform initial norm and energy bounds. '
               'Form closedness, the full infinite Hamiltonian domain, '
               'capacity/regulator limits, physical identification and a TOE remain unproved.'))
    target = root/'data/regularized_spin_dynamics_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,':',len(matrices),'matrix cases,',len(flows),'propagators,',len(trials),
          'Gaussian families,',len(fourier_samples),'Fourier samples,',len(hashes),'source hashes.')
    print('Maximum transcription error:',max(max(c['transcription_errors'].values()) for c in matrices))
    print('Maximum unitarity error:',max(s['unitarity_error'] for f in flows for s in f['samples']))


if __name__ == '__main__':
    main()
