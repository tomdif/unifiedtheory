#!/usr/bin/env python3
"""Exact spin-valued energy bracket, its obstruction, and one dilation repair."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy

from microscopic_spin_two_audit import exact_cell, tensor_basis


def spin_tensor():
    old, _ = exact_cell()
    omega = old['omega']
    singlet = np.array([0., 1., -1., 0.])/np.sqrt(2)
    eta = np.kron(singlet, singlet)
    scalar = np.outer(eta, omega.conj())
    xs = [scalar+scalar.conj().T]+old['x']
    es = np.array([np.eye(3)/np.sqrt(3)]+[np.array(e, dtype=float) for e in tensor_basis()])
    active = old['projectors'][1]+np.outer(eta, eta.conj())
    spin_h = .2*active+1.2*(np.eye(16)-old['projectors'][0]-active)
    kappa, gamma = .25, .02
    cxx = kappa*np.eye(16)+gamma*sum((e[0, 0]*x for e, x in zip(es, xs)), np.zeros((16, 16), dtype=complex))
    assert np.max(abs(la.eigvalsh(cxx)-np.array([kappa-gamma]+[kappa]*14+[kappa+gamma]))) < 1e-12
    dynamic = float(la.norm(spin_h@cxx-cxx@spin_h, 2))
    assert abs(dynamic-.2*gamma) < 1e-12
    u = sy.Matrix(sy.symbols('u0:3', real=True)); v = sy.Matrix(sy.symbols('v0:3', real=True))
    symbolic_basis = [sy.eye(3)/sy.sqrt(3)]+tensor_basis()
    norm_squared = sum((u.T*e*v)[0]**2 for e in symbolic_basis)
    assert sy.expand(norm_squared-(u.dot(u)*v.dot(v)+u.dot(v)**2)/2) == 0
    tensor = [[kappa*(i == j)*np.eye(16)+gamma*sum(
        (e[i, j]*x for e, x in zip(es, xs)), np.zeros((16, 16), dtype=complex))
        for j in range(2)] for i in range(2)]
    component_commutator = float(la.norm(tensor[0][0]@tensor[0][1]-tensor[0][1]@tensor[0][0], 2))
    assert component_commutator > 1e-5
    return dict(xs=xs, es=es, spin_h=spin_h, cxx=cxx, tensor=tensor, kappa=kappa, gamma=gamma), dict(
        dimension=16, exact_bilinear_norm_identity=True,
        diagonal_stiffness_eigenvalues=la.eigvalsh(cxx).tolist(),
        onsite_stiffness_commutator_norm=dynamic,
        xx_xy_component_commutator_norm=component_commutator, lower_stiffness=kappa-gamma)


def finite_energy_commutator(cell):
    sites, cutoff, input_cutoff = 3, 6, 2
    basis = [n for n in itertools.product(range(cutoff+1), repeat=sites) if sum(n) <= cutoff]
    lookup = {n: i for i, n in enumerate(basis)}
    field_dim = len(basis)
    qs, ps = [], []
    for site in range(sites):
        create = sp.lil_matrix((field_dim, field_dim), dtype=complex)
        for col, n in enumerate(basis):
            nxt = list(n); nxt[site] += 1; nxt = tuple(nxt)
            if nxt in lookup:
                create[lookup[nxt], col] = np.sqrt(n[site]+1)
        create = create.tocsr(); annih = create.conj().T
        qs.append((annih+create)/np.sqrt(2))
        ps.append((annih-create)/(1j*np.sqrt(2)))
    difference = np.zeros((sites, sites))
    for s in range(sites):
        difference[s, (s+1) % sites] = .5
        difference[s, (s-1) % sites] = -.5
    forward = np.array([[-1., 1., 0.], [0., -1., 1.], [1., 0., -1.]])
    differences = [difference, forward]
    gradients = [[sum((dd[s, j]*qs[j] for j in range(sites)),
                      sp.csr_matrix((field_dim, field_dim))) for dd in differences] for s in range(sites)]
    identity = np.eye(16)
    coefficients = [cell['tensor']]+[[[cell['kappa']*(i == j)*identity
                     for j in range(2)] for i in range(2)] for _ in range(sites-1)]
    kron = lambda x, y: sp.kron(sp.csr_matrix(x), y, format='csr')
    mass = .3
    densities = [kron(identity, (ps[s]@ps[s]+mass**2*(qs[s]@qs[s]))/2)
                 +sum((kron(coefficients[s][i][j], gradients[s][i]@gradients[s][j]/2)
                       for i, j in itertools.product(range(2), repeat=2)),
                      sp.csr_matrix((16*field_dim, 16*field_dim), dtype=complex)) for s in range(sites)]
    densities[0] += kron(cell['spin_h'], sp.eye(field_dim, format='csr'))
    full_h = sum(densities, sp.csr_matrix((16*field_dim, 16*field_dim), dtype=complex))
    ground = float(sp.linalg.eigsh(full_h, k=1, which='SA', return_eigenvectors=False, tol=1e-10)[0])
    assert ground > 0
    input_field = np.array([i for i, n in enumerate(basis) if sum(n) <= input_cutoff])
    columns = np.concatenate([r*field_dim+input_field for r in range(16)])
    def weighted_h(lapse):
        return sum((value*h for value, h in zip(lapse, densities)), sp.csr_matrix(full_h.shape, dtype=complex))
    def stiffness(lapse):
        return [[sum((lapse[s]*differences[a][s, i]*differences[b][s, j]*coefficients[s][a][b]
                      for s, a, b in itertools.product(range(sites), range(2), range(2))),
                     np.zeros((16, 16), dtype=complex))
                 + (mass**2*lapse[i]*identity if i == j else 0)
                 for j in range(sites)] for i in range(sites)]
    rng = np.random.default_rng(8011)
    rows = []
    for case in range(6):
        n, m = rng.normal(size=(2, sites))
        hn, hm = weighted_h(n), weighted_h(m)
        actual = (hn@hm[:, columns]-hm@hn[:, columns])/1j
        an, am = stiffness(n), stiffness(m)
        expected = sp.csr_matrix(full_h.shape, dtype=complex)
        for i, j in itertools.product(range(sites), repeat=2):
            kk = m[i]*an[i][j]-n[i]*am[i][j]
            expected += kron(kk, (ps[i]@qs[j]+qs[j]@ps[i])/2)
        error = float(sp.linalg.norm(actual-expected[:, columns]))
        assert error < 1e-10
        rows.append(dict(case=case, full_output_residual=error))
    return dict(field_sites=sites, oscillator_total_cutoff=cutoff,
                oscillator_input_cutoff=input_cutoff, spin_field_dimension=16*field_dim,
                input_dimension=len(columns), truncated_oscillator_ground_energy=ground,
                rows=rows,
                scope='Three sites, one dynamical spin cell, two supplied algebraic stencils (centered and forward) probing noncommuting tensor components. This is a local algebra test, not a two-dimensional continuum lattice. Full commutators are applied before input restriction; four oscillator steps fit below the cutoff. The ground energy checks only the truncated oscillator model.')


def profile_terms():
    def wave(k, sine=False):
        k = tuple(k); nk = tuple(-x for x in k)
        return {k: -.5j if sine else .5, nk: .5j if sine else .5}
    def add(*terms):
        out = {}
        for weight, term in terms:
            for key, value in term.items(): out[key] = out.get(key, 0)+weight*value
        return out
    n = add((1., {(0, 0, 0): 1}), (.2, wave((1, 0, 0), True)))
    m = add((.3, wave((0, 1, 0))), (.2, wave((0, 0, 1), True)))
    f = add((1., wave((1, 1, 0), True)), (.2, wave((0, 0, 1))))
    g = add((1., wave((1, 0, -1))), (.3, wave((0, 2, 0), True)))
    return n, m, f, g


def stencil_consistency(cell):
    n_terms, m_terms, f_terms, g_terms = profile_terms()
    def product(a, b):
        out = {}
        for k, v in a.items():
            for l, w in b.items():
                key = tuple(x+y for x, y in zip(k, l)); out[key] = out.get(key, 0)+v*w
        return out
    def bound(terms, order=0):
        if order == 0: return sum(abs(v) for v in terms.values())
        return np.array([sum(abs(v)*abs(k[i])**order for k, v in terms.items()) for i in range(3)])
    n_bound, m_bound, f_bound = [bound(x) for x in [n_terms, m_terms, f_terms]]
    e0 = la.norm((n_bound*bound(product(m_terms, f_terms), 3)
                  +m_bound*bound(product(n_terms, f_terms), 3))/6)
    d0 = la.norm(bound(g_terms, 3))/6
    g0 = la.norm(bound(g_terms, 1))
    F0 = f_bound*(n_bound*la.norm(bound(m_terms, 1))+m_bound*la.norm(bound(n_terms, 1)))
    rows = []
    for length in [9, 17, 33, 65]:
        a = 2*np.pi/length
        grid = np.stack(np.meshgrid(*([np.arange(length)*a]*3), indexing='ij'), axis=-1).reshape(-1, 3)
        def evaluate(terms, axis=None):
            out = np.zeros(len(grid), dtype=complex)
            for k, coefficient in terms.items():
                out += coefficient*(1 if axis is None else 1j*k[axis])*np.exp(1j*(grid@k))
            assert np.max(abs(out.imag)) < 1e-12
            return out.real
        def discrete(values):
            cube = values.reshape((length,)*3)
            return np.column_stack([((np.roll(cube, -1, axis=i)-np.roll(cube, 1, axis=i))/(2*a)).ravel() for i in range(3)])
        n, m, f, g = [evaluate(t) for t in [n_terms, m_terms, f_terms, g_terms]]
        dn, dm, dg = [np.column_stack([evaluate(t, axis=i) for i in range(3)]) for t in [n_terms, m_terms, g_terms]]
        left = n[:, None]*discrete(m*f)-m[:, None]*discrete(n*f)
        target = f[:, None]*(n[:, None]*dm-m[:, None]*dn)
        dg_discrete = discrete(g)
        scalar_error = np.sum(left*dg_discrete-target*dg, axis=1)
        tensor_error = np.einsum('si,aij,sj->sa', left, cell['es'], dg_discrete)
        tensor_error -= np.einsum('si,aij,sj->sa', target, cell['es'], dg)
        # Exact norm of a sum of independent-cell star operators.
        error = abs(cell['kappa']*a**3*np.sum(scalar_error))
        error += abs(cell['gamma'])*a**3*np.sum(la.norm(tensor_error, axis=1))
        certified = (2*np.pi)**3*(cell['kappa']+abs(cell['gamma']))*a*a*(e0*(g0+a*a*d0)+F0*d0)
        assert error <= certified+1e-10
        rows.append(dict(length=length, spin_cells=length**3, spacing=a,
                         coefficient_operator_norm_error=float(error), uniform_bound=float(certified),
                         error_over_spacing_squared=float(error/a**2)))
    return dict(rows=rows, bound_constants=dict(e0=e0, d0=d0, g0=g0, F0=F0),
                scope='Exact spin-space norm of coefficient forms on smooth field profiles, not a full unbounded-current norm or a spin-field continuum theorem.')


def dilation_obstruction(cell):
    rng = np.random.default_rng(8033)
    c = cell['cxx']; sigma = 1.
    lower = 2*sigma*la.norm(c, 2)
    ratios = []
    for _ in range(30):
        raw = rng.normal(size=(16, 16))+1j*rng.normal(size=(16, 16))
        generator = (raw+raw.conj().T)/2
        defect = 1j*(generator@c-c@generator)+2*sigma*c
        norm = float(la.norm(defect, 2))
        assert norm >= lower-1e-12
        assert abs(np.trace(defect)-2*sigma*np.trace(c)) < 1e-12
        ratios.append(norm/lower)
    assert abs(la.norm(2*sigma*c, 2)-lower) < 1e-12
    return dict(arbitrary_generators=30, sharp_full_space_lower_bound=float(lower),
                minimum_random_ratio=min(ratios), zero_generator_saturates=True,
                scope='Obstruction to uniform full-space matrix dilation, not to a growing non-invariant low-occupation domain.')


def logarithmic_repair():
    cutoff, ell, kappa, sigma = 2, .4, .25, 1.
    nodes, weights = np.polynomial.legendre.leggauss(48)
    nodes, weights = (nodes+1)/2, weights/2
    rows = []
    for copies in [4, 8, 12, 16, 24, 32, 48, 64]:
        dimension = copies+1
        creation = np.diag(np.sqrt(np.arange(1, dimension)), -1)
        number = np.arange(dimension)
        collective = creation*np.sqrt(1-number/copies)[None, :]
        dressing = np.zeros(dimension); dressing[:-1] = 1/np.sqrt(1-number[:-1]/copies)
        assert la.norm(collective*dressing[None, :]-creation) < 1e-12
        q = (creation.T+creation)/np.sqrt(2)
        p = (creation.T-creation)/(1j*np.sqrt(2))
        top = np.eye(dimension)[:, -1]
        assert la.norm(q@p-p@q-1j*(np.eye(dimension)-dimension*np.outer(top, top))) < 1e-12
        eigen, vectors = la.eigh(q)
        expq = lambda value: (vectors*np.exp(-value*ell*eigen))@vectors.T
        metric = kappa*expq(1.)
        generator = 2*sigma*p/ell
        defect = 1j*(generator@metric-metric@generator)+2*sigma*metric
        integral = np.zeros((dimension, dimension))
        for s, w in zip(nodes, weights):
            integral += w*np.outer(expq(1-s)@top, expq(s)@top)
        predicted = 2*sigma*kappa*dimension*integral
        duhamel_error = float(la.norm(defect-predicted, 2))
        roundoff = 200*np.finfo(float).eps*(1+la.norm(generator, 2))*(1+la.norm(metric, 2))*dimension
        assert duhamel_error < roundoff
        compressed = float(la.norm(defect[:cutoff+1, :cutoff+1], 2))
        full_output = float(la.norm(defect[:, :cutoff+1], 2))
        x = ell*np.sqrt(2*copies); distance = copies-cutoff
        log_tail = x+distance*np.log(x)-math.lgamma(distance+1)
        certified = float(np.exp(np.log(2*sigma*kappa*dimension)+2*log_tail))
        certified_full_output = float(np.exp(np.log(2*sigma*kappa*dimension)+x+log_tail))
        assert compressed <= certified+roundoff
        assert full_output <= certified_full_output+roundoff
        # Independent infinite-oscillator matrix elements from normal ordering.
        t = -ell/np.sqrt(2)
        limiting_metric = np.zeros((dimension, cutoff+1))
        for m in range(dimension):
            for n in range(cutoff+1):
                prefactor = kappa*np.exp(t*t/2)*math.sqrt(math.factorial(m)*math.factorial(n))
                limiting_metric[m, n] = prefactor*sum(
                    t**(m+n-2*j)/(math.factorial(m-j)*math.factorial(n-j)*math.factorial(j))
                    for j in range(min(m, n)+1))
        limiting_metric_error = float(la.norm(metric[:, :cutoff+1]-limiting_metric, 2))
        first_power = copies-cutoff+1
        ratio = ell*np.sqrt(2*(cutoff+first_power+1))/(first_power+1)
        assert ratio < 1
        first_term = np.exp(first_power*np.log(ell)+.5*(first_power*np.log(2)
                            +math.lgamma(cutoff+first_power+1)-math.lgamma(cutoff+1))
                            -math.lgamma(first_power+1))
        metric_convergence_bound = float(2*kappa*first_term/(1-ratio))
        assert limiting_metric_error <= metric_convergence_bound+roundoff
        full = float(la.norm(defect, 2)); obstruction = float(2*sigma*la.norm(metric, 2))
        assert full >= obstruction-roundoff
        cg, cc = generator[:cutoff+1, :cutoff+1], metric[:cutoff+1, :cutoff+1]
        wrong_compression = float(la.norm(1j*(cg@cc-cc@cg)+2*sigma*cc, 2))
        assert wrong_compression >= 2*sigma*la.norm(cc, 2)-roundoff
        rows.append(dict(copies=copies, input_occupation=cutoff, metric_minimum=float(la.eigvalsh(metric)[0]),
                         full_space_error=full, full_space_lower_bound=obstruction,
                         compressed_error=compressed, analytic_compressed_bound=certified,
                         full_output_error_on_input=full_output,
                         analytic_full_output_bound=certified_full_output,
                         limiting_metric_represented_rows_error=limiting_metric_error,
                         analytic_full_fock_metric_convergence_bound=metric_convergence_bound,
                         numerical_roundoff_allowance=float(roundoff), duhamel_residual=duhamel_error,
                         error_if_generators_compressed_first=wrong_compression))
    return dict(rows=rows, logarithmic_scale=ell, kappa=kappa, sigma=sigma,
                scope='One positive metric component and one dilation generator on a fixed input domain. No invariant physical sector, six-component gravity algebra, or stable spin phase is established.')


def main():
    root = Path(__file__).resolve().parents[1]
    cell, spin_report = spin_tensor()
    report = dict(spin_tensor=spin_report, microscopic_energy_bracket=finite_energy_commutator(cell),
                  stencil_consistency=stencil_consistency(cell),
                  full_space_obstruction=dilation_obstruction(cell), logarithmic_repair=logarithmic_repair())
    sources = ['SPIN_CLOCK_BRACKET.md', 'scripts/spin_clock_bracket_audit.py',
               'UnifiedTheory/Audit/KFCausalSpinClockBracket.lean',
               'GRAVITY_FROM_CLOCK_CONSTRAINTS.md', 'scripts/gravity_constraint_audit.py',
               'MICROSCOPIC_SPIN_TWO_SEED.md', 'scripts/microscopic_spin_two_audit.py', 'LOCAL_CAUSAL_CLOCK.md']
    report['source_sha256'] = {f: hashlib.sha256((root/f).read_bytes()).hexdigest() for f in sources}
    report['scope'] = ('Exact spin-valued local energy commutator and uniform smooth-test coefficient estimate; '
                       'finite full-space metric-dilation obstruction and controlled single logarithmic dilation repair. '
                       'The full constraint algebra, stable gravitational spin phase, quantum continuum, and TOE remain unproved.')
    (root/'data/spin_clock_bracket_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
