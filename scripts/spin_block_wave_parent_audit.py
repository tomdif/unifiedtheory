#!/usr/bin/env python3
"""Audit an explicit spin-block parent; the note states the analytical scope.

Finite spectra validate formulas, not a joint critical limit or Einstein gravity.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla
import sympy as sy

from microscopic_spin_two_audit import exact_cell


D = 6
RNG = np.random.default_rng(20260911)


def occupations(modes, cutoff):
    def total(n, m):
        if m == 1:
            yield (n,)
        else:
            for j in range(n + 1):
                for rest in total(n - j, m - 1):
                    yield (j,) + rest
    return [v for n in range(cutoff + 1) for v in total(n, modes)]


def maximum(matrix):
    return float(np.max(np.abs(matrix.data))) if matrix.nnz else 0.


def lowest(matrix, count=1):
    values, vectors = sla.eigsh(matrix, k=count, which='SA', tol=2e-11,
                               v0=RNG.normal(size=matrix.shape[0]))
    order = np.argsort(values)
    values, vectors = values[order], vectors[:, order]
    residual = float(la.norm(matrix @ vectors - vectors * values))
    assert residual < 2e-7
    return values, vectors, residual


def collective(R):
    states = occupations(D, R)
    lookup = {v: i for i, v in enumerate(states)}
    annih = []
    for a in range(D):
        rows, cols, vals = [], [], []
        for j, v in enumerate(states):
            if v[a]:
                w = list(v)
                w[a] -= 1
                rows.append(lookup[tuple(w)])
                cols.append(j)
                vals.append(math.sqrt(v[a] * (1 - (sum(v) - 1) / R)))
        annih.append(sp.csr_matrix((vals, (rows, cols)), shape=(len(states),)*2))
    q = [(b + b.T) / math.sqrt(2) for b in annih]
    p_im = [(b - b.T) / math.sqrt(2) for b in annih]
    number = np.array([sum(v) for v in states])
    return states, q, p_im, number


def onsite(q, p_im, number, R, U, stiffness, penalty):
    size = len(number)
    h = sp.diags(penalty * number**2 / R, format='csr')
    for qa, pa in zip(q, p_im):
        h = h + stiffness / 2 * (qa @ qa) - U / 2 * (pa @ pa)
    assert h.shape == (size, size)
    return h.tocsr()


def exact_algebra():
    n, R, d, c, lam = sy.symbols('n R d c lam', positive=True)
    bb_dag = (n + d) * (1 - n / R)
    b_dag_b = n * (1 - (n - 1) / R)
    identity = 2*n*(1-n/R)+d-(d-1)*n/R
    assert sy.expand(bb_dag+b_dag_b-identity) == 0
    excess = c/2*identity + lam*n*n/R-c*n-c*d/2
    assert sy.expand(excess-((lam-c)*n*n-c*(d-1)*n/2)/R) == 0
    assert sy.expand(excess.subs(lam, c*(d+1)/2)-c*(d-1)*n*(n-1)/(2*R)) == 0
    cell, _ = exact_cell()
    singlet = np.array([0., 1., -1., 0.])/math.sqrt(2)
    embedding = np.column_stack([cell['omega'], np.kron(singlet, singlet), cell['states']])
    gram = float(la.norm(embedding.conj().T @ embedding - np.eye(7)))
    assert gram < 2e-14
    projector = embedding @ embedding.conj().T
    annih = [np.outer(embedding[:, 0], embedding[:, a].conj()) for a in range(1, 7)]
    leakage = max(float(la.norm((np.eye(16)-projector) @ b)) for b in annih)
    assert leakage < 2e-14
    return dict(collective_number_identity=True, occupation_coercivity_identity=True,
                four_qubit_active_embedding_gram_error=gram, active_leakage=leakage,
                active_cell_dimension=7, inactive_cell_dimension=9,
                scope='Symbolic scalar identities and the existing exact four-spin cell; analytical selection proof is in the note.')


def partitions(n, maximum_part=None, slots=7):
    if n == 0:
        yield ()
    elif slots:
        for first in range(min(n, maximum_part or n), 0, -1):
            for rest in partitions(n-first, first, slots-1):
                yield (first,) + rest


def exchange_gap():
    rows = []
    for R in [2, 3, 4, 8, 16, 32]:
        eigenvalues = [R*(R-1)//2-sum(v*(v-2*i+1) for i, v in enumerate(part, 1))//2
                      for part in partitions(R)]
        positive = [v for v in eigenvalues if v]
        assert eigenvalues.count(0) == 1 and min(positive) == R
        rows.append(dict(R=R, represented_partitions=len(eigenvalues), gap=min(positive), normalized_gap=1))
    return dict(cases=rows, scope='Finite partition checks of the known complete-exchange spectrum; not a replacement for the all-R proof.')


def embed_local(matrix, slot, slots, q):
    return sp.kron(sp.eye(q**slot), sp.kron(matrix, sp.eye(q**(slots-slot-1))), format='csr')


def microscopic(R, V, q=7):
    slots = R*V
    dim = q**slots
    digits = np.array(np.unravel_index(np.arange(dim), (q,)*slots)).T
    bcell = [sp.csr_matrix(([1.], ([0], [a])), shape=(q, q)) for a in range(1, 7)]
    ncell = sp.diags([0]+[1]*6+[0]*(q-7), format='csr')
    qops, pops, numbers, exchange = [], [], [], []
    for x in range(V):
        bops = [sum((embed_local(b, x*R+j, slots, q) for j in range(R)), sp.csr_matrix((dim, dim)))/math.sqrt(R)
                for b in bcell]
        qops.append([(b+b.T)/math.sqrt(2) for b in bops])
        pops.append([(b-b.T)/math.sqrt(2) for b in bops])
        numbers.append(sum((embed_local(ncell, x*R+j, slots, q) for j in range(R)), sp.csr_matrix((dim, dim))))
        cx = sp.csr_matrix((dim, dim))
        for i, j in itertools.combinations(range(x*R, (x+1)*R), 2):
            selected = np.flatnonzero((digits[:, i] < 7) & (digits[:, j] < 7))
            changed = digits[selected].copy()
            changed[:, [i, j]] = changed[:, [j, i]]
            targets = np.ravel_multi_index(changed.T, (q,)*slots)
            swap = sp.csr_matrix((np.ones(len(selected)), (targets, selected)), shape=(dim, dim))
            cx += sp.diags(np.isin(np.arange(dim), selected).astype(float)) - swap
        exchange.append(cx.tocsr())
    occ = occupations(D, R)
    lookup = {v: i for i, v in enumerate(occ)}
    active_rows = np.flatnonzero(np.all(digits < 7, axis=1))
    columns, amplitudes = [], []
    for row in active_rows:
        column, multiplicity = 0, 1
        for x in range(V):
            counts = np.bincount(digits[row, x*R:(x+1)*R], minlength=7)
            column = column*len(occ) + lookup[tuple(counts[1:])]
            multiplicity *= math.factorial(R)//math.prod(math.factorial(int(n)) for n in counts)
        columns.append(column)
        amplitudes.append(1/math.sqrt(multiplicity))
    t = sp.csr_matrix((amplitudes, (active_rows, columns)), shape=(dim, len(occ)**V))
    inactive = np.sum(digits >= 7, axis=1)
    return qops, pops, numbers, exchange, t, inactive


def microscopic_spectra():
    rows = []
    for R, V, q in [(2, 1, 7), (3, 1, 7), (4, 1, 7), (2, 2, 7), (2, 1, 16)]:
        U, r, g, penalty, Delta, delta = 1., .25, .1, 1.5, .4, 6.
        degree = V-1
        amax = r+g*degree
        J0 = (U+amax)/2+.05
        J = J0+Delta
        qs, ps, ns, cs, t, inactive = microscopic(R, V, q)
        dim = t.shape[0]
        wave = sp.csr_matrix((dim, dim))
        chart = sp.csr_matrix((dim, dim))
        for x in range(V):
            for qa, pa in zip(qs[x], ps[x]):
                wave += r/2*(qa@qa)-U/2*(pa@pa)
            chart += penalty/R*(ns[x]@ns[x])
        if V == 2:
            for a in range(D):
                diff = qs[0][a]-qs[1][a]
                wave += g/2*(diff@diff)
        ctotal = sum(cs, sp.csr_matrix((dim, dim)))
        h0 = wave+chart+J0/R*ctotal
        h = h0+Delta/R*ctotal+sp.diags(delta*inactive)
        offdiag = h0-sp.diags(h0.diagonal())
        offdiag.eliminate_zeros()
        max_positive = max(0., float(offdiag.data.max())) if offdiag.nnz else 0.
        assert max_positive < 1e-13
        iso_error = maximum(t.T@t-sp.eye(t.shape[1]))
        collective_h = t.T@h@t
        e, v, residual = lowest(h)
        ec, _, _ = lowest(collective_h)
        projection = t@t.T
        ground_leakage = float(la.norm(v-projection@v))
        invariant_error = maximum(h@t-t@collective_h)
        exchange_kernel = maximum(ctotal@t)
        assert max(iso_error, invariant_error, exchange_kernel) < 2e-12
        assert abs(e[0]-ec[0]) < 1e-9 and ground_leakage < 2e-8
        lift = 2*float(abs(h).sum(axis=1).max())+10
        excluded, _, _ = lowest(h+lift*projection)
        repair_bound = J+1.5*(U+amax)
        predicted = min(Delta, delta-repair_bound)
        assert excluded[0]-e[0] >= predicted-1e-8
        inactive_gap = None
        if q > 7:
            inactive_indices = np.flatnonzero(inactive)
            inactive_energy, _, _ = lowest(h.tocsr()[inactive_indices][:, inactive_indices])
            inactive_gap = float(inactive_energy[0]-e[0])
            assert inactive_gap >= delta-repair_bound-1e-8
        parity_values = (-1.)**sum(n.diagonal().astype(int) for n in ns)
        parity = sp.diags(parity_values)
        parity_error = maximum(h@parity-parity@h)
        assert parity_error < 1e-13
        # Independent collective construction, including all output rows.
        _, cq, cp, cn = collective(R)
        hc = onsite(cq, cp, cn, R, U, amax, penalty)
        if V == 2:
            identity = sp.eye(hc.shape[0])
            hc = sp.kron(hc, identity)+sp.kron(identity, hc)
            for qa in cq:
                hc -= g*sp.kron(qa, qa)
        compression_error = maximum(collective_h-hc)
        assert compression_error < 3e-12
        rows.append(dict(R=R, blocks=V, cell_dimension=q, full_dimension=dim,
                         collective_dimension=t.shape[1], U=U, r=r, g=g, penalty=penalty,
                         J0=J0, Delta=Delta, J=J, inactive_penalty=delta,
                         max_positive_offdiagonal=max_positive, ground_energy=float(e[0]),
                         collective_energy=float(ec[0]), ground_projection_error=ground_leakage,
                         minimum_excluded_gap=float(excluded[0]-e[0]), uniform_gap_bound=predicted,
                         minimum_inactive_gap=inactive_gap, uniform_inactive_gap_bound=delta-repair_bound,
                         eigensolver_residual=residual, full_output_invariance_error=invariant_error,
                         independent_collective_error=compression_error, parity_commutator_error=parity_error))
        print('microscopic', R, V, q, 'gap', float(excluded[0]-e[0]), flush=True)
    return dict(cases=rows, scope='Complete small microscopic Hilbert spaces, including inactive states in the 16-state case; selection for arbitrary R,V follows from the note.')


def radial(R, ell, U, r, penalty):
    ns = np.arange(ell, R+1, 2, dtype=float)
    diag = (U+r)/4*(2*ns*(1-ns/R)+D-(D-1)*ns/R)+penalty*ns**2/R
    n = ns[:-1]
    off = (r-U)/(4*R)*np.sqrt((R-n)*(R-n-1)*(n-ell+2)*(n+ell+D))
    if len(ns) == 1:
        return ns, diag, np.ones((1, 1))
    e, v = la.eigh_tridiagonal(diag, off, select='i', select_range=(0, min(1, len(ns)-1)))
    return ns, e, v


def multiplicity(ell):
    return math.comb(ell+D-1, D-1)-(math.comb(ell+D-3, D-1) if ell >= 2 else 0)


def radial_crosscheck():
    rows = []
    for R in [2, 4]:
        _, q, p, n = collective(R)
        h = onsite(q, p, n, R, 1., .25, 1.5)
        actual = la.eigvalsh(h.toarray())
        predicted = []
        for ell in range(R+1):
            ns = np.arange(ell, R+1, 2, dtype=float)
            diag = 1.25/4*(2*ns*(1-ns/R)+D-(D-1)*ns/R)+1.5*ns**2/R
            j = ns[:-1]
            off = -.75/(4*R)*np.sqrt((R-j)*(R-j-1)*(j-ell+2)*(j+ell+D))
            ev = la.eigvalsh_tridiagonal(diag, off) if len(ns)>1 else diag
            predicted.extend(np.repeat(ev, multiplicity(ell)))
        error = float(np.max(np.abs(np.sort(predicted)-actual)))
        assert error < 2e-12 and len(predicted) == math.comb(R+D, D)
        identity = sum((qa@qa-pa@pa for qa, pa in zip(q, p)), sp.csr_matrix(h.shape))
        expected = 2*n*(1-n/R)+D-(D-1)*n/R
        identity_error = maximum(identity-sp.diags(expected))
        assert identity_error < 2e-13
        rows.append(dict(R=R, dimension=len(actual), complete_radial_spectrum_error=error,
                         collective_number_identity_error=identity_error))
    return dict(cases=rows)


def radial_convergence():
    rows, controls = [], []
    for r in [.16, .25, .36]:
        errors = []
        for R in [2, 4, 8, 16, 32, 64, 128, 256]:
            U, penalty = 1., 1.5
            ns, energies, vectors = radial(R, 0, U, r, penalty)
            other = [radial(R, ell, U, r, penalty)[1][0] for ell in range(1, R+1)]
            assert min(other) > energies[0]
            vector = vectors[:, 0]
            if vector[0] < 0:
                vector = -vector
            target_energy = D*math.sqrt(U*r)/2
            target_number = D/4*(math.sqrt(U/r)+math.sqrt(r/U)-2)
            t = (math.sqrt(U)-math.sqrt(r))/(math.sqrt(U)+math.sqrt(r))
            pairs = ns/2
            target_vector = (1-t*t)**(D/4)*np.sqrt((pairs+1)*(pairs+2)/2)*t**pairs
            distance = math.sqrt(max(0., 2-2*float(vector@target_vector)))
            gap = min(min(other), energies[1])-energies[0]
            mean_n = float((vector*vector)@ns)
            residual_bound = (energies[0]-.5*D*r)/r
            assert mean_n <= residual_bound+1e-9
            errors.append(abs(float(energies[0])-target_energy))
            rows.append(dict(R=R, r=r, penalty=penalty, ground_angular_sector=0,
                             ground_energy=float(energies[0]), gaussian_energy=target_energy,
                             energy_error=errors[-1], first_gap=float(gap), gaussian_gap=math.sqrt(U*r),
                             mean_occupation=mean_n, gaussian_mean_occupation=target_number,
                             full_gaussian_state_distance=distance, occupation_bound=residual_bound))
        assert errors[-1] < errors[0]/15
        # The slowest tested regulator has distance about 0.052 at R=256.
        # This finite tolerance is a diagnostic, not the convergence theorem.
        assert rows[-1]['full_gaussian_state_distance'] < .06
    for R in [8, 32, 128]:
        sectors = [(ell, radial(R, ell, 1., .25, 0.)) for ell in range(R+1)]
        ell, (ns, energy, vectors) = min(sectors, key=lambda item: item[1][1][0])
        mean = float((vectors[:, 0]**2)@ns)
        assert energy[0] <= 1.25/4+1e-12 and energy[0] < 1.5
        controls.append(dict(R=R, penalty=0., ground_angular_sector=ell,
                             ground_energy=float(energy[0]), mean_occupation=mean,
                             occupied_fraction=mean/R, gaussian_energy=1.5,
                             top_state_trial_energy=1.25/4))
    return dict(cases=rows, scope='All angular sectors tested in the exact six-component radial reduction; numerical convergence illustrates the fixed-volume theorem.'), dict(cases=controls, scope='The unpenalized model has a competing high-occupation vacuum, already established analytically by a trial state.')


def coupled_ground():
    rows = []
    U, r, g, penalty = 1., .25, .1, 1.5
    target_energy = D/2*(math.sqrt(U*r)+math.sqrt(U*(r+2*g)))
    target_corr = math.sqrt(U)/4*(1/math.sqrt(r)-1/math.sqrt(r+2*g))
    for R in [2, 3, 4]:
        _, q, p, n = collective(R)
        h = onsite(q, p, n, R, U, r+g, penalty)
        eye = sp.eye(h.shape[0])
        full = sp.kron(h, eye, format='csr')+sp.kron(eye, h, format='csr')
        for qa in q:
            full -= g*sp.kron(qa, qa, format='csr')
        e, v, residual = lowest(full)
        corr = float(v[:, 0] @ (sp.kron(q[0], q[0])@v[:, 0]))
        assert corr > 0
        rows.append(dict(R=R, blocks=2, dimension=full.shape[0], ground_energy=float(e[0]),
                         gaussian_energy=target_energy, single_component_cross_covariance=corr,
                         gaussian_cross_covariance=target_corr, eigensolver_residual=residual))
        print('coupled', R, 'energy', float(e[0]), flush=True)
    return dict(cases=rows, scope='A genuinely coupled selected vacuum on two blocks; small R data are not a joint thermodynamic convergence test.')


def gaussian_tail():
    rows = []
    U, g = 1., .1
    qbound = math.sqrt(U)/2*(1+1/math.sqrt(g))
    pbound = math.sqrt((1+12*g)/U)/2
    M = max(qbound, pbound, .5)
    z = 1+1/(2*M)
    for L in [5, 9, 17, 33, 65]:
        r = L**-4
        k = 2*np.pi*np.fft.fftfreq(L)
        eig = r+4*g*sum(np.sin(v/2)**2 for v in np.meshgrid(k, k, k, indexing='ij'))
        vq = float(np.mean(1/np.sqrt(eig))*math.sqrt(U)/2)
        vp = float(np.mean(np.sqrt(eig))/(2*math.sqrt(U)))
        assert vq <= qbound and vp <= pbound
        mgf = (((1-z)*vq+(1+z)/2)*((1-z)*vp+(1+z)/2))**(-D/2)
        assert mgf <= 64
        eps = 1e-3
        R = math.ceil(math.log(64*L**3/eps)/math.log(z))-1
        probability_bound = 64*L**3*z**(-(R+1))
        assert probability_bound <= eps*(1+1e-12)
        rows.append(dict(L=L, blocks=L**3, regulator=r, component_q_variance=vq,
                         component_p_variance=vp, mean_total_occupation=D/2*(vq+vp-1),
                         z=z, single_block_occupation_mgf=mgf, cutoff_for_union_bound=R,
                         any_block_tail_bound=probability_bound))
    return dict(cases=rows, uniform_q_variance_bound=qbound, uniform_p_variance_bound=pbound,
                scope='Tail bound for the limiting Gaussian only. It does not prove uniform convergence of the finite-R microscopic ground state near criticality.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_algebra(), exchange_gap=exchange_gap(),
                  microscopic_spectra=microscopic_spectra(), radial_crosscheck=radial_crosscheck())
    report['radial_convergence'], report['bare_vacuum_controls'] = radial_convergence()
    report['coupled_ground'] = coupled_ground()
    report['gaussian_tail'] = gaussian_tail()
    sources = ['SPIN_BLOCK_WAVE_PARENT.md', 'scripts/spin_block_wave_parent_audit.py',
               'MICROSCOPIC_SPIN_TWO_SEED.md', 'scripts/microscopic_spin_two_audit.py',
               'AFFINE_SPIN_METRIC.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'SPATIAL_METRIC_VACUUM.md', 'REDUCED_TENSOR_HAMILTONIAN.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('An explicit at-most-two-cell parent selects the active symmetric ground sector '
                       'with a gap to excluded sectors uniform in block size and volume. A vanishing '
                       'occupation penalty controls the fixed-volume Gaussian six-wave limit. '
                       'The graph and grouping are supplied; growing complete block connectivity, '
                       'no uniform joint critical limit, no physical two-helicity reduction, and '
                       'a parity mismatch with the tested linear Einstein identification remain. No TOE or new Lean theorem is claimed.')
    target = root/'data/spin_block_wave_parent_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k:len(v['cases']) for k,v in report.items() if isinstance(v,dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), cases=counts, total_cases=sum(counts.values()),
                          source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
