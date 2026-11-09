#!/usr/bin/env python3
"""Reproducible finite-matrix tests of the revised areal spin candidate.

Full occupation spaces are retained at each stated capacity. Three active
flavors are used in the large runs; a separate six-flavor calculation
checks the spectator embedding. Numerical evidence is not a limit proof.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse as sp
from scipy.integrate import solve_ivp

from quantum_areal_spin_model import ArealSpinModel, ArealSpinLattice, Parameters


END = 0.2
CENTERS = (0., 0., 0.1, 0.2, 0.3, 0.1)


def embedding(small, large):
    lookup = {tuple(s):i for i,s in enumerate(large.states)}
    rows = [lookup[tuple(s)+(0,)*(large.params.flavors-small.params.flavors)] for s in small.states]
    return sp.csr_matrix((np.ones(small.dim), (rows,np.arange(small.dim))),
                         shape=(large.dim,small.dim))


def finite_checks():
    model = ArealSpinModel(Parameters(R=4, functional_order=2))
    H, C = model.matrix(END).toarray(), model.C.toarray()
    S, Ps = model.S.toarray(), model.Ps.toarray()
    eye = np.eye(model.dim)
    F = eye+S/2+S@S/8
    D = eye-S/2+S@S/8
    L = (D@D@Ps+Ps@D@D)/2
    E = eye+L/2+L@L/8
    construction_error = max(la.norm(F-model.clockHalf.toarray()),
                             la.norm(D-model.inverseHalf.toarray()),
                             la.norm(E-model.expLhalf.toarray()))
    force = 1j/model.params.hbar*(H@C-C@H)
    eigenforce = la.eigvalsh(force)
    mineig = float(la.eigvalsh(H)[0])
    minclock = float(la.eigvalsh(C)[0])
    assert construction_error < 2e-12
    assert la.norm(H-H.conj().T) < 1e-12 and mineig > 0
    assert minclock >= 0.25-1e-12
    assert abs(np.trace(force)) < 1e-12 and eigenforce[0] < 0 < eigenforce[-1]

    full = ArealSpinModel(Parameters(R=4, flavors=6, functional_order=2))
    J = embedding(model,full)
    residual = full.matrix(END)@J-J@model.matrix(END)
    embedding_error = float(sp.linalg.norm(residual))
    assert embedding_error < 2e-12
    print('Positive polynomial construction and six-flavor spectator embedding passed.', flush=True)
    return dict(capacity=4, dimension=model.dim, full_six_flavor_dimension=full.dim,
                polynomial_matrix_residual=construction_error,
                minimum_H_eigenvalue=mineig, minimum_C_eigenvalue=minclock,
                clock_force_trace_abs=float(abs(np.trace(force))),
                clock_force_eigenvalue_range=[float(eigenforce[0]),float(eigenforce[-1])],
                six_flavor_intertwining_residual=embedding_error,
                clock_force_is_not_globally_nonnegative=True)


def capacity_and_order():
    reference = ArealSpinModel(Parameters(R=32, correction='exact'))
    psi0, tail = reference.coherent_state(CENTERS)
    ref20 = reference.evolve(psi0,END,20)
    ref40 = reference.evolve(psi0,END,40)
    ref80 = reference.evolve(psi0,END,80)
    steps = dict(steps=[20,40,80], raw_state_error_20_to_40=float(la.norm(ref20-ref40)),
                 raw_state_error_40_to_80=float(la.norm(ref40-ref80)))
    assert steps['raw_state_error_40_to_80'] < steps['raw_state_error_20_to_40']/3.5
    rows = []
    for R in [4,8,16,32]:
        for correction in ['bare','second_order','exact']:
            model = ArealSpinModel(Parameters(R=R,correction=correction))
            initial, tail = model.coherent_state(CENTERS)
            final = model.evolve(initial,END,40)
            diag = model.diagnostics(END,final)
            assert abs(diag['norm']-1) < 2e-11 and diag['energy'] > 0
            rows.append(dict(capacity=R, dimension=model.dim, correction=correction,
                             initial_preparation_tail=tail,
                             raw_state_distance_to_R32_exact_80_steps=float(la.norm(embedding(model,reference)@final-ref80)),
                             **diag))
            print(f"R={R:2d} {correction:12s}: clock-rate defect {diag['clock_rate_defect']:.4g}",flush=True)
    orders = []
    for order in [2,4,6,None]:
        model = ArealSpinModel(Parameters(R=32,functional_order=order))
        initial, _ = model.coherent_state(CENTERS)
        final = model.evolve(initial,END,40)
        orders.append(dict(Taylor_order=order, **model.diagnostics(END,final),
                           raw_state_distance_to_exact_spin_exact_functions=float(la.norm(final-ref80))))
    exactrows = [r for r in rows if r['correction']=='exact']
    assert all(y['clock_rate_defect'] < x['clock_rate_defect'] for x,y in zip(exactrows,exactrows[1:]))
    assert exactrows[-1]['clock_rate_defect'] < 2e-9
    return dict(end_time=END,hbar=0.05,initial_centers=CENTERS,
                time_step_convergence=steps,capacity_comparison=rows,polynomial_comparison=orders,
                comparison_scope='Fixed-hbar finite-capacity diagnostics; not a classical or continuum convergence proof.')


def semiclassical():
    def rhs(t,y):
        Q,P,L,c,phi,pi = y
        W = np.exp(2*t+L)*(0.5*phi**2/2+0.1*phi**4/4)
        return [P/c,0,-0.5+(P*P+pi*pi+2*W)/(2*c*c),W/c,pi/c,
                -np.exp(2*t+L)*(0.5*phi+0.1*phi**3)/c]
    solution = solve_ivp(rhs,(0,END),[0.1,0.2,0.,1.,0.3,0.1],rtol=2e-12,atol=2e-14)
    assert solution.success
    classical = dict(clock=float(solution.y[3,-1]),longitudinal=float(solution.y[2,-1]),
                     scalar=float(solution.y[4,-1]))
    rows = []
    for hbar,R in [(0.1,16),(0.05,24),(0.025,32)]:
        model = ArealSpinModel(Parameters(R=R,hbar=hbar,correction='exact'))
        initial,tail = model.coherent_state(CENTERS)
        final = model.evolve(initial,END,40)
        diag = model.diagnostics(END,final)
        rows.append(dict(hbar=hbar,capacity=R,initial_preparation_tail=tail,
                         initial_clock=model.diagnostics(0,initial)['clock'],
                         errors_to_classical={key:abs(diag[key]-value) for key,value in classical.items()},**diag))
    print('Semiclassical packet comparison completed (three finite samples).',flush=True)
    return dict(classical=classical,samples=rows,
                scope='Centers match the classical initial datum; finite-width quantum means need not equal those centers.')


def two_site():
    rows = []
    for R in [2,4,6]:
        local = ArealSpinModel(Parameters(R=R,functional_order=2))
        lattice = ArealSpinLattice(local,2,iter([(0,1)]))
        assert len(lattice.gradient_terms)==4
        a,_ = local.coherent_state(CENTERS)
        b,_ = local.coherent_state((0.,0.,-0.1,-0.05,0.2,0.05))
        initial = np.kron(a,b)
        gradient = float(sum(la.norm(A@initial)**2 for A in lattice.gradient_terms))
        final = lattice.evolve(initial,0.1,20)
        refined = lattice.evolve(initial,0.1,40)
        assert abs(la.norm(final)-1) < 2e-11 and gradient > 0
        rows.append(dict(capacity=R,dimension=lattice.dim,initial_gradient_energy=gradient,
                         norm_error=abs(float(la.norm(final))-1),
                         raw_state_error_20_to_40=float(la.norm(final-refined)),
                         initial_clocks=[float(np.vdot(initial,C@initial).real) for C in lattice.clocks],
                         final_clocks=[float(np.vdot(final,C@final).real) for C in lattice.clocks]))
    print('Two-site positive gradient evolution passed.',flush=True)
    return dict(samples=rows,scope='Supplied graph and reduced Hamiltonian; no exact lattice spatial constraint or continuum limit.')


def main():
    np.random.seed(0)
    report = dict(finite_construction=finite_checks(),homogeneous=capacity_and_order(),
                  semiclassical=semiclassical(),two_site=two_site())
    report['numerical_environment'] = dict(numpy=np.__version__,scipy=scipy.__version__,random_seed=0)
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/quantum_areal_spin_model.py','scripts/quantum_areal_spin_audit.py',
               'scripts/holomorphic_tensor_phase_audit.py',
               'UnifiedTheory/Audit/KFCausalQuantumArealCandidate.lean']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Specified finite-spin quantization of a supplied reduced areal target. '
                       'Large runs use a three-active-flavor invariant sector. '
                       'Original-law selection, quantum constraint closure, joint limits and a TOE are unproved.')
    target = root/'data/quantum_areal_spin_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(target,flush=True)


if __name__ == '__main__':
    main()
