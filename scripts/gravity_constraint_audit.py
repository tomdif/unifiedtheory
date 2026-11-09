#!/usr/bin/env python3
"""Microscopic trace channel and conditional continuum gravity constraints."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from microscopic_spin_two_audit import tensor_basis


def microscopic_trace():
    pauli = [sy.Matrix([[0, 1], [1, 0]])/2,
             sy.Matrix([[0, -sy.I], [sy.I, 0]])/2, sy.diag(1, -1)/2]
    spins = []
    for site in range(4):
        row = []
        for component in pauli:
            factors = [sy.eye(2) for _ in range(4)]
            factors[site] = component
            row.append(sy.kronecker_product(*factors))
        spins.append(row)
    aa = [spins[0][i]+spins[1][i] for i in range(3)]
    bb = [spins[2][i]+spins[3][i] for i in range(3)]
    square = lambda vv: sum((v*v for v in vv), sy.zeros(16))
    casimir = square([a+b for a, b in zip(aa, bb)])
    plus = sy.Matrix([1, 0, 0, 0])
    zero = sy.Matrix([0, 1, 1, 0])/sy.sqrt(2)
    minus = sy.Matrix([0, 0, 0, 1])
    singlet = sy.Matrix([0, 1, -1, 0])/sy.sqrt(2)
    omega = (sy.kronecker_product(plus, minus)-sy.kronecker_product(zero, zero)
             +sy.kronecker_product(minus, plus))/sy.sqrt(3)
    eta = sy.kronecker_product(singlet, singlet)
    ps = (sy.eye(16)-square(aa)/2)*(sy.eye(16)-square(bb)/2)
    p0 = omega*omega.T
    p2 = casimir*(casimir-2*sy.eye(16))/24
    assert ps == eta*eta.T and (eta.T*omega)[0] == 0
    assert casimir*eta == sy.zeros(16, 1)
    exchange = sum((spins[0][i]*spins[2][i] for i in range(3)), sy.zeros(16))
    amplitude = sy.simplify((eta.T*exchange*omega)[0])
    assert amplitude == -sy.sqrt(3)/4
    scalar_creation = sy.simplify(-4/sy.sqrt(3)*ps*exchange*p0)
    assert scalar_creation == eta*omega.T
    states = [eta]
    for e in tensor_basis():
        quad = sum((e[i, j]*(aa[i]*aa[j]+aa[j]*aa[i])/2
                    for i in range(3) for j in range(3)), sy.zeros(16))
        states.append(sy.simplify(sy.sqrt(3)*quad*omega))
    columns = sy.Matrix.hstack(*states)
    assert sy.simplify(columns.conjugate().T*columns) == sy.eye(6)
    active_number = ps+p2
    assert sy.simplify(columns*columns.conjugate().T-active_number) == sy.zeros(16)
    creation = [state*omega.T for state in states]
    annih = [op.conjugate().T for op in creation]
    for alpha, beta in itertools.product(range(6), repeat=2):
        assert sy.simplify(annih[alpha]*creation[beta]
                           -(p0 if alpha == beta else sy.zeros(16))) == sy.zeros(16)
    momenta = [(b-c)/(sy.I*sy.sqrt(2)) for b, c in zip(annih, creation)]
    coordinates = [(b+c)/sy.sqrt(2) for b, c in zip(annih, creation)]
    for ops in [momenta, coordinates]:
        assert sy.simplify(sum((op*op for op in ops), sy.zeros(16))
                           -(6*p0+active_number)/2) == sy.zeros(16)
    d = sy.Matrix(sy.symbols('dx dy dz', real=True))
    complete = [sy.eye(3)/sy.sqrt(3)]+tensor_basis()
    assert sy.expand(sum((d.T*e*d)[0]**2 for e in complete)-d.dot(d)**2) == 0
    return dict(hilbert_dimension=16, active_dimension=7, inactive_dimension=9,
                scalar_transition_amplitude=str(amplitude), six_channel_identities=36,
                scalar_creation_from_exchange=True, complete_tensor_norm_identity=True,
                single_cell_quadrature_square='(6 P_0 + N)/2',
                naive_kinetic_vacuum_energy_over_J=1.5,
                naive_kinetic_excited_energy_over_J=.25,
                scope='Exact finite-spin kinematics; scalar promotion changes the onsite Hamiltonian.')


def block_occupation_algebra():
    # Include one extra occupation level before taking any compressed commutator.
    cutoff = 3
    basis = [n for n in itertools.product(range(cutoff+2), repeat=6)
             if sum(n) <= cutoff+1]
    lookup = {n: i for i, n in enumerate(basis)}
    mask = np.array([i for i, n in enumerate(basis) if sum(n) <= cutoff])
    number = np.array([sum(n) for n in basis])
    canonical = []
    for alpha in range(6):
        create = np.zeros((len(basis), len(basis)))
        for col, n in enumerate(basis):
            nxt = list(n); nxt[alpha] += 1; nxt = tuple(nxt)
            if nxt in lookup:
                create[lookup[nxt], col] = np.sqrt(n[alpha]+1)
        canonical.append(create)
    rows = []
    for copies in [8, 16, 64, 256]:
        collective = [c*np.sqrt(1-number/copies)[None, :] for c in canonical]
        creation_error = max(la.norm((b-c)[:, mask], 2)
                             for b, c in zip(collective, canonical))
        creation_bound = np.sqrt(cutoff+1)*cutoff/copies
        assert creation_error <= creation_bound+1e-12
        maximum = 0.
        for alpha, beta in itertools.product(range(6), repeat=2):
            comm = collective[alpha].T@collective[beta]-collective[beta]@collective[alpha].T
            error = comm-(np.eye(len(basis)) if alpha == beta else 0)
            error = error[np.ix_(mask, mask)]
            flavor = canonical[beta]@canonical[alpha].T
            predicted = -(flavor+(np.diag(number) if alpha == beta else 0))/copies
            assert la.norm(error-predicted[np.ix_(mask, mask)]) < 1e-12
            norm = float(la.norm(error, 2)); maximum = max(maximum, norm)
            assert norm <= 2*cutoff/copies+1e-12
        rows.append(dict(copies=copies, creation_error=float(creation_error),
                         creation_bound=float(creation_bound), commutator_error=maximum,
                         commutator_bound=2*cutoff/copies))
    return dict(flavors=6, input_occupation_cutoff=cutoff, matrix_dimension=len(basis),
                compressed_dimension=len(mask), commutator_checks=144, rows=rows,
                scope='Exact symmetric-block occupation representation; no ground-phase selection or dynamics convergence claimed.')


def dispersion():
    j, g, ell, mass = sy.symbols('J g ell r', real=True)
    aa = (j+mass+g*ell)/2
    bb = (mass+g*ell-j)/2
    assert sy.expand(aa**2-bb**2-j*(mass+g*ell)) == 0
    momentum = sy.Matrix(sy.symbols('px py pz', real=True))
    mu, hopping, speed = sy.symbols('mu hopping speed', real=True)
    schr_energy = mu+hopping*momentum.dot(momentum)
    schr_clock = sy.Matrix([sy.diff(schr_energy**2, p)/2 for p in momentum])
    assert sy.simplify(schr_clock-2*hopping*schr_energy*momentum) == sy.zeros(3, 1)
    relativistic_square = mu**2+speed**2*momentum.dot(momentum)
    assert sy.Matrix([sy.diff(relativistic_square, p)/2 for p in momentum]) == speed**2*momentum
    rng = np.random.default_rng(7031)
    cases = []
    # Positive analytic matrix families K=F^dagger F test the min-max bound.
    for _ in range(20):
        f0 = np.diag([0., 0., 1., 2.])
        f1 = rng.normal(size=(4, 4))+1j*rng.normal(size=(4, 4))
        projected_slope = (f0.T@f1+f1.conj().T@f0)[:2, :2]
        assert la.norm(projected_slope) == 0
        trial_constant = la.norm(f1[:, :2], 2)**2
        for k in [1e-1, 1e-2, -1e-2, 1e-3]:
            ff = f0+k*f1
            eigen = la.eigvalsh(ff.conj().T@ff)
            assert eigen[0] >= -1e-12 and eigen[1] <= trial_constant*k*k+1e-12
            cases.append(float(eigen[1]/(trial_constant*k*k)))
    return dict(pairing_identity=True, clock_principal_symbol_identities=True,
                positive_band_minmax_cases=len(cases),
                maximum_minmax_ratio=max(cases), gapless_paired_exponent=1,
                number_conserving_seed_exponent=2,
                scope='Canonical pairing and finite positive-matrix checks; not a microscopic paired phase.')


def symbolic_brackets_and_legendre():
    lam = sy.symbols('lambda', real=True)
    names = sy.symbols('p0 p1 p2 p3 p4 p5', real=True)
    p = sy.Matrix([[names[0], names[3], names[5]],
                   [names[3], names[1], names[4]], [names[5], names[4], names[2]]])
    hs = sy.symbols('h0 h1 h2 h3 h4 h5', real=True)
    hess = sy.Matrix([[hs[0], hs[3], hs[5]], [hs[3], hs[1], hs[4]], [hs[5], hs[4], hs[2]]])
    contraction = sy.trace((p-lam*sy.trace(p)*sy.eye(3))*(sy.trace(hess)*sy.eye(3)-hess))
    assert sy.expand(contraction-((1-2*lam)*sy.trace(p)*sy.trace(hess)-sy.trace(p*hess))) == 0
    gravity_product, matter_product = sy.symbols('gravity_product matter_product')
    solution = sy.solve([gravity_product-1, matter_product-1,
                         2*gravity_product*(1-2*lam)], [gravity_product, matter_product, lam], dict=True)
    assert solution == [{gravity_product: 1, matter_product: 1, lam: sy.Rational(1, 2)}]
    y = sy.symbols('y', real=True)
    witness_integral = sy.integrate(sy.sin(y)**2, (y, 0, 2*sy.pi))
    assert witness_integral == sy.pi
    # The integrated derivative bracket has the same nonzero trace anomaly.
    witness_direct = sy.integrate(2*(2*lam-1)*sy.cos(y)*(-sy.cos(y)), (y, 0, 2*sy.pi))
    assert sy.simplify(witness_direct-2*(1-2*lam)*witness_integral) == 0
    kk = p
    pp = kk-sy.trace(kk)*sy.eye(3)
    kinetic = sy.trace(pp*pp)-sy.trace(pp)**2/2
    assert sy.expand(kinetic-(sy.trace(kk*kk)-sy.trace(kk)**2)) == 0
    assert sy.expand(2*sy.trace(pp*kk)-kinetic-(sy.trace(kk*kk)-sy.trace(kk)**2)) == 0
    rho, lapse, u, velocity = sy.symbols('rho lapse u velocity', nonzero=True)
    scalar_p = rho*velocity/(lapse*u)
    assert sy.simplify(scalar_p*velocity-lapse*u*scalar_p**2/(2*rho)
                       -rho*velocity**2/(2*lapse*u)) == 0
    return dict(curvature_variation_contraction=True,
                closure_solution={str(k): str(v) for k, v in solution[0].items()},
                trace_anomaly_witness_integral=str(witness_integral),
                gravitational_legendre_transform=True, scalar_legendre_transform=True,
                scope='Polynomial and integrated identities within the stated continuum ansatz; functional geometry remains an analytical supplier.')


def periodic_functional_brackets():
    rng = np.random.default_rng(7057)
    length = 16
    grid = np.array(list(itertools.product(2*np.pi*np.arange(length)/length, repeat=3)))
    def field():
        value = np.zeros(len(grid)); grad = np.zeros((len(grid), 3)); hess = np.zeros((len(grid), 3, 3))
        for _ in range(4):
            wave = rng.integers(-2, 3, size=3)
            amplitude, phase = rng.normal(), rng.uniform(0, 2*np.pi)
            argument = grid@wave+phase
            value += amplitude*np.cos(argument)
            grad -= amplitude*np.sin(argument)[:, None]*wave
            hess -= amplitude*np.cos(argument)[:, None, None]*np.outer(wave, wave)
        return value, grad, hess
    basis = [np.diag(np.eye(3)[i]) for i in range(3)]
    for i, j in [(0, 1), (1, 2), (2, 0)]:
        e = np.zeros((3, 3)); e[i, j] = e[j, i] = 1/np.sqrt(2); basis.append(e)
    basis = np.array(basis)
    rows = []
    for trial in range(12):
        n, dn, ddn = field(); m, dm, ddm = field()
        pp = [field() for _ in range(6)]
        p = np.einsum('sx,xij->sij', np.column_stack([x[0] for x in pp]), basis)
        dp = np.einsum('sax,xij->saij', np.stack([x[1] for x in pp], axis=2), basis)
        trace = np.trace(p, axis1=1, axis2=2)
        trace_grad = np.trace(dp, axis1=2, axis2=3)
        divergence = np.einsum('siij->sj', dp)
        v = n[:, None]*dm-m[:, None]*dn
        dg = -2*np.mean(np.sum(v*divergence, axis=1))
        anomaly = np.mean(np.sum(v*trace_grad, axis=1))
        a, b = .7, 1.4
        lam = [0., .5, 1.][trial % 3]
        kinetic = np.sum(p*p, axis=(1, 2))-lam*trace**2
        dq = a*(2*np.einsum('sij,sjk->sik', p, p)
                -2*lam*trace[:, None, None]*p-.5*kinetic[:, None, None]*np.eye(3))
        dmomentum = 2*a*(p-lam*trace[:, None, None]*np.eye(3))
        qn = n[:, None, None]*dq+b*(np.trace(ddn, axis1=1, axis2=2)[:, None, None]*np.eye(3)-ddn)
        qm = m[:, None, None]*dq+b*(np.trace(ddm, axis1=1, axis2=2)[:, None, None]*np.eye(3)-ddm)
        direct = np.mean(np.sum(qn*m[:, None, None]*dmomentum
                                -n[:, None, None]*dmomentum*qm, axis=(1, 2)))
        predicted = a*b*dg+2*a*b*(1-2*lam)*anomaly
        gravity_error = float(abs(direct-predicted))
        assert gravity_error < 1e-10
        phi, dphi, ddphi = field(); momentum, _, _ = field()
        u, w = .6, 1.7
        lap = np.trace(ddphi, axis1=1, axis2=2)
        # Include a nonlinear ultralocal potential to test its cancellation.
        vn = -w*(np.sum(dn*dphi, axis=1)+n*lap)+n*phi**3
        vm = -w*(np.sum(dm*dphi, axis=1)+m*lap)+m*phi**3
        matter_direct = np.mean(vn*m*u*momentum-n*u*momentum*vm)
        matter_d = np.mean(momentum*np.sum(v*dphi, axis=1))
        matter_error = float(abs(matter_direct-u*w*matter_d))
        assert matter_error < 1e-10
        rows.append(dict(trial=trial, trace_coefficient=lam,
                         gravity_bracket_error=gravity_error, scalar_bracket_error=matter_error))
    return dict(grid_vertices=length**3, rows=rows,
                scope='Flat-metric phase-space samples with variable momentum and lapse. The curved-metric functional identity is derived analytically, not established by these finite samples.')


def weak_field_and_universality():
    # Independent linearized Ricci calculation from metric-perturbation Hessian jets.
    pairs = list(itertools.combinations_with_replacement(range(3), 2))
    f = sy.symbols('F0:6'); s = sy.symbols('S0:6')
    hf = sy.zeros(3); hs = sy.zeros(3)
    for ij, ff, ss in zip(pairs, f, s):
        i, j = ij; hf[i, j] = hf[j, i] = ff; hs[i, j] = hs[j, i] = ss
    eta = sy.diag(-1, 1, 1, 1)
    def second(mu, nu, a, b):
        if a == 0 or b == 0 or mu != nu:
            return sy.S.Zero
        return -2*(hf[a-1, b-1] if mu == 0 else hs[a-1, b-1])
    ricci = sy.zeros(4)
    for mu, nu in itertools.product(range(4), repeat=2):
        ricci[mu, nu] = sy.expand(sum(eta[alpha, alpha]*(second(alpha, nu, alpha, mu)
                                    +second(alpha, mu, alpha, nu)-second(mu, nu, alpha, alpha)
                                    -second(alpha, alpha, mu, nu))/2 for alpha in range(4)))
    scalar = sy.trace(eta*ricci)
    einstein = sy.simplify(ricci-eta*scalar/2)
    expected = sy.zeros(4); expected[0, 0] = 2*sy.trace(hs)
    expected[1:4, 1:4] = hs-hf-sy.eye(3)*sy.trace(hs-hf)
    assert einstein == expected
    assert sy.expand(scalar-(4*sy.trace(hs)-2*sy.trace(hf))) == 0
    # Decaying Newton potential: harmonic away from the source, flux fixes delta mass.
    radius, grav, mass = sy.symbols('r G m', positive=True)
    potential = -grav*mass/radius
    assert sy.simplify(sy.diff(radius**2*sy.diff(potential, radius), radius)) == 0
    flux = sy.simplify(4*sy.pi*radius**2*sy.diff(potential, radius))
    assert flux == 4*sy.pi*grav*mass
    ga, gb, momentum, ea, eb = sy.symbols('gA gB p EA EB', real=True)
    incoming_a = sy.Matrix([ea, momentum, 0, 0]); incoming_b = sy.Matrix([eb, -momentum, 0, 0])
    outgoing_a = sy.Matrix([ea, 0, momentum, 0]); outgoing_b = sy.Matrix([eb, 0, -momentum, 0])
    assert incoming_a+incoming_b == outgoing_a+outgoing_b
    ward = sy.expand(ga*(outgoing_a-incoming_a)+gb*(outgoing_b-incoming_b))
    assert sy.simplify(ward-(ga-gb)*sy.Matrix([0, -momentum, momentum, 0])) == sy.zeros(4, 1)
    return dict(static_einstein_tensor=True, energy_constraint='laplacian Psi = 4 pi G rho',
                newton_potential='-G m/r', newton_flux=str(flux),
                elastic_soft_ward_vector=[str(x) for x in ward],
                scope='Weak-field and soft-factor consequences conditional on the gravitational action and stated scattering hypotheses.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(microscopic_trace=microscopic_trace(), blocks=block_occupation_algebra(),
                  dispersion=dispersion(), coefficient_algebra=symbolic_brackets_and_legendre(),
                  functional_brackets=periodic_functional_brackets(),
                  physical_consequences=weak_field_and_universality())
    sources = ['GRAVITY_FROM_CLOCK_CONSTRAINTS.md', 'scripts/gravity_constraint_audit.py',
               'UnifiedTheory/Audit/KFCausalGravityConstraint.lean',
               'MICROSCOPIC_SPIN_TWO_SEED.md', 'scripts/microscopic_spin_two_audit.py',
               'BOND_TENSOR_CONSTRAINTS.md', 'LOCAL_CAUSAL_CLOCK.md', 'COLLECTIVE_WAVE_SPACETIME.md']
    report['source_sha256'] = {f: hashlib.sha256((root/f).read_bytes()).hexdigest() for f in sources}
    report['scope'] = ('Exact microscopic trace transition and symmetric-block kinematics; conditional '
                       'canonical pairing and metric/scalar constraint-algebra derivation of Einstein dynamics. '
                       'No stable microscopic sector realizing the nonlinear deformation algebra, '
                       'quantum gravitational continuum, selected spacetime, or TOE is proved.')
    (root/'data/gravity_constraint_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
