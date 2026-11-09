#!/usr/bin/env python3
"""Compact gauge loops and the determinant orientation of flat Wilson lines.

Exact spin identities are separated from float64 transport diagnostics.
This does not extend the interacting weak-chart current to all torons.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s
from scipy.linalg import expm

from overlap_chirality_audit import GAMMA, GAMMA5, equal
from radial_measure_audit import RectangularOverlap, SPECIES, density, curvature
from chiral_measure_audit import inverse_sqrt

CLIFFORD = np.array([s.I*GAMMA5*g for g in GAMMA]+[GAMMA5], complex)
JSPIN = np.array(GAMMA5*GAMMA[1]*GAMMA[3], complex)


def exact_checks():
    j = GAMMA5*GAMMA[1]*GAMMA[3]
    gs = [s.I*GAMMA5*g for g in GAMMA]+[GAMMA5]
    equal(j*j.H, s.eye(4))
    equal(j*j.conjugate(), -s.eye(4))
    for a in gs:
        equal(j*a.conjugate()*j.H, a)
        equal(a.H, a)
        assert a.trace() == 0
        for b in gs:
            equal(a*b+b*a, 2*s.eye(4) if a == b else s.zeros(4))
            for c in gs:
                assert (a*b*c).trace() == 0
    u = s.symbols('u0:4', real=True)
    squared = (sum(u)-1)**2+sum(2*x-x*x for x in u)
    assert s.expand(squared-1-2*sum(u[i]*u[k] for i in range(4) for k in range(i))) == 0
    ar, ai, br, bi = s.symbols('ar ai br bi', real=True)
    a, b = ar+s.I*ai, br+s.I*bi
    transition = s.Matrix([[a, -s.conjugate(b)], [b, s.conjugate(a)]])
    assert s.expand(transition.det()-(ar*ar+ai*ai+br*br+bi*bi)) == 0
    return dict(arithmetic='exact SymPy', antiunitary_matrix=str(j),
                antiunitary_square='-I', clifford_relations=True,
                all_125_triple_traces_zero=True, pair_transition_determinant=True,
                free_gap_squared_identity=True)


class FlatFamily:
    """Momentum blocks; conjugation for J acts at fixed momentum label."""
    def __init__(self, lengths, antiperiodic=True):
        self.lengths = np.array(lengths)
        self.labels = np.array(list(itertools.product(*(range(n) for n in lengths))))
        shift = np.array([0, 0, 0, .5 if antiperiodic else 0])
        self.momenta = 2*np.pi*(self.labels+shift)/self.lengths
        self.n = len(self.labels)

    def blocks(self, theta, charge):
        k = self.momenta-charge*np.asarray(theta)/self.lengths
        coefficients = np.column_stack((np.sin(k), 3-np.cos(k).sum(axis=1)))
        radii = np.linalg.norm(coefficients, axis=1)
        h = np.einsum('na,aij->nij', coefficients, CLIFFORD)
        p = (np.eye(4)+h/radii[:, None, None])/2
        derivatives = []
        for mu in range(4):
            dc = np.zeros_like(coefficients)
            dc[:, mu] = -charge/self.lengths[mu]*np.cos(k[:, mu])
            dc[:, 4] = -charge/self.lengths[mu]*np.sin(k[:, mu])
            dn = dc/radii[:, None]-coefficients*np.sum(coefficients*dc, axis=1)[:, None]/radii[:, None]**3
            derivatives.append(np.einsum('na,aij->nij', dn, CLIFFORD)/2)
        return h, p, derivatives, float(radii.min())

    def paired_frame(self, p):
        # Choosing a pivot is a local frame chart, not a global smooth frame.
        pivot = np.argmax(np.diagonal(p, axis1=1, axis2=2).real, axis=1)
        v = p[np.arange(self.n), :, pivot]
        v = v/np.linalg.norm(v, axis=1)[:, None]
        partner = np.einsum('ij,nj->ni', JSPIN, v.conjugate())
        return np.stack((v, partner), axis=2)

    def endpoint_permutation(self, winding, charge):
        lookup = {tuple(label): k for k, label in enumerate(self.labels)}
        return np.array([lookup[tuple((label-charge*np.array(winding)) % self.lengths)]
                         for label in self.labels])


def dagger(a):
    return a.conjugate().swapaxes(-1, -2)


def det2(a):
    return a[..., 0, 0]*a[..., 1, 1]-a[..., 0, 1]*a[..., 1, 0]


def toron_loop(family, charge, theta, winding, steps=96, curved_path=False):
    initial = family.paired_frame(family.blocks(theta, charge)[1])
    frame = initial.copy()
    minimum_gram, minimum_gap = 1., np.inf
    max_pair_error = 0.
    for k in range(1, steps+1):
        t = k/steps
        point = theta+2*np.pi*t*np.array(winding)
        if curved_path:
            point = (point+np.sin(2*np.pi*t)*np.array([.31, -.27, .19, .23])
                     +(1-np.cos(2*np.pi*t))*np.array([.11, .17, -.13, .07]))
        _, p, _, gap = family.blocks(point, charge)
        projected = p@frame
        gram = dagger(frame)@projected
        values, vectors = np.linalg.eigh(gram)
        minimum_gram = min(minimum_gram, float(values.min()))
        minimum_gap = min(minimum_gap, gap)
        assert values.min() > .2
        factor = (vectors/np.sqrt(values)[:, None, :])@dagger(vectors)
        frame = projected@factor
        max_pair_error = max(max_pair_error, float(np.linalg.norm(
            frame[:, :, 1]-np.einsum('ij,nj->ni', JSPIN, frame[:, :, 0].conjugate()))))
    perm = family.endpoint_permutation(winding, charge)
    overlaps = dagger(initial[perm])@frame
    determinants = det2(overlaps)
    # Permuting blocks of two columns has sign (sign perm)^2 = +1.
    holonomy = complex(np.prod(determinants))
    error = abs(holonomy-1)
    assert error < 2e-10
    assert max_pair_error < 2e-11
    full_holonomy_error = float(np.linalg.norm(overlaps-np.eye(2)))
    return dict(lengths=family.lengths.tolist(), charge=charge, winding=list(winding),
                steps=steps, curved_path=curved_path, minimum_gram=minimum_gram,
                minimum_kernel_gap=minimum_gap, determinant_holonomy=[holonomy.real, holonomy.imag],
                determinant_error=error, paired_frame_error=max_pair_error,
                block_holonomy_distance_from_identity=full_holonomy_error)


def flat_checks():
    theta = np.array([.37, -.29, .43, .61])
    dense_rows = []
    for ap in [False, True]:
        lengths = (2, 3, 2, 3)
        family, model = FlatFamily(lengths, ap), RectangularOverlap(lengths, ap)
        fourier = np.exp(1j*np.array(model.geom.sites)@family.momenta.T)/np.sqrt(model.n)
        transform = np.kron(np.eye(4), fourier)
        q = -3
        h, p, derivatives, gap = family.blocks(theta, q)
        a = np.broadcast_to((theta/family.lengths)[:, None], (4, model.n))
        dense_h = model.kernel(np.exp(1j*a), q)
        expected = np.zeros_like(dense_h)
        expected_p = np.zeros_like(dense_h)
        for k in range(model.n):
            indices = np.arange(4)*model.n+k
            expected[np.ix_(indices, indices)] = h[k]
            expected_p[np.ix_(indices, indices)] = p[k]
        kernel_error = float(np.linalg.norm(dagger(transform)@dense_h@transform-expected))
        sp = model.operator(np.exp(1j*a), q)
        projector_error = float(np.linalg.norm(dagger(transform)@sp['p']@transform-expected_p))
        assert max(kernel_error, projector_error) < 2e-12
        ward_density = float(np.linalg.norm(density(model, sp['p'], q)))
        assert ward_density < 2e-12
        # Independent dense endpoint gauge identification, including AP time.
        endpoint_errors = []
        for mu in range(4):
            end = a.copy()
            end[mu] += 2*np.pi/lengths[mu]
            gauge = np.tile(np.exp(2j*np.pi*q*np.array(model.geom.sites)[:, mu]/lengths[mu]), 4)
            endpoint = model.kernel(np.exp(1j*end), q)
            endpoint_errors.append(float(np.linalg.norm(endpoint-gauge[:, None]*dense_h*gauge.conjugate()[None, :])))
        assert max(endpoint_errors) < 2e-12
        spin_error = max(float(np.linalg.norm(JSPIN@z.conjugate()@JSPIN.conj().T-z)) for z in p)
        maximum_curvature = max(abs(sum(curvature(p[k], derivatives[mu][k], derivatives[nu][k])
                                       for k in range(family.n))) for mu in range(4) for nu in range(mu))
        assert maximum_curvature < 1e-12
        dense_rows.append(dict(antiperiodic_time=ap, kernel_error=kernel_error,
                               projector_error=projector_error, density_norm=ward_density,
                               endpoint_gauge_errors=endpoint_errors, antiunitary_error=spin_error,
                               maximum_flat_curvature=maximum_curvature, minimum_kernel_gap=gap))
    rows = []
    for lengths, ap in [((2, 3, 2, 3), True), ((3,)*4, False)]:
        family = FlatFamily(lengths, ap)
        for _, q, _ in SPECIES:
            for mu in range(4):
                winding = [int(k == mu) for k in range(4)]
                rows.append(toron_loop(family, q, theta, winding))
        rows.append(toron_loop(family, 1, theta, [0]*4, curved_path=True))
        rows.append(toron_loop(family, 6, theta, [1, -1, 0, 1], 192, curved_path=True))
    # Determinant triviality does not force the full SU(2) transport to be identity.
    assert max(row['block_holonomy_distance_from_identity'] for row in rows) > .1
    assert max(row['block_holonomy_distance_from_identity'] for row in rows
               if row['winding'] == [0]*4) > .001
    periodic = FlatFamily((3,)*4, False)
    h, p, _, gap = periodic.blocks(np.zeros(4), 1)
    d = np.eye(4)+np.array(GAMMA5, complex)@(2*p[0]-np.eye(4))
    assert np.linalg.norm(d) < 1e-14 and gap >= 1-1e-14
    return dict(dense_operator_checks=dense_rows, loops=rows,
                maximum_determinant_error=max(row['determinant_error'] for row in rows),
                dirac_zero_mode_residual=float(np.linalg.norm(d)),
                scope='All flat holonomies analytically; finite transport diagnostics listed explicitly')


def gauge_loop_checks():
    model = RectangularOverlap((2,)*4)
    a = np.random.default_rng(2026090906).uniform(-.018, .018, (4, model.n))
    spectra = [(q, m, model.operator(np.exp(1j*a), q)) for _, q, m in SPECIES]
    total_density = sum(m*density(model, sp['p'], q) for q, m, sp in spectra)
    site = int(np.argmax(abs(total_density)))
    omega = np.eye(model.n)[site]
    ward_phase = -2*np.pi*float(omega@total_density)
    rows, compressed_phase = [], 0.
    for q, m, sp in spectra:
        v, p = sp['v'], sp['p']
        diagonal = q*np.tile(omega, 4)
        x = np.diag(1j*diagonal)
        compressed = dagger(v)@x@v
        compressed_phase += m*(-2*np.pi*np.trace(compressed).imag)
        t = .713
        gauge = np.exp(t*np.diag(x))
        frame = (gauge[:, None]*v)@expm(-t*compressed)
        pt = gauge[:, None]*p*gauge.conjugate()[None, :]
        pdot = x@pt-pt@x
        kato = pdot@pt-pt@pdot
        fdot = x@frame-frame@compressed
        horizontal_error = float(np.linalg.norm(dagger(frame)@fdot))
        ode_error = float(np.linalg.norm(fdot-kato@frame))
        assert max(horizontal_error, ode_error) < 5e-12
        rows.append(dict(charge=q, multiplicity=m, horizontal_error=horizontal_error,
                         kato_ode_error=ode_error, minimum_kernel_gap=sp['gap']))
    exact_error = abs(np.exp(1j*compressed_phase)-np.exp(1j*ward_phase))
    assert exact_error < 2e-12 and abs(ward_phase) > 1e-8
    refinements = []
    for steps in [128, 256, 512]:
        total = 1.+0j
        minimum_gram = 1.
        for q, m, sp in spectra:
            frame = sp['v'].copy()
            for k in range(1, steps+1):
                gauge = np.tile(np.exp(2j*np.pi*q*k/steps*omega), 4)
                p = gauge[:, None]*sp['p']*gauge.conjugate()[None, :]
                factor, gram_min = inverse_sqrt(dagger(frame)@p@frame)
                minimum_gram = min(minimum_gram, gram_min)
                frame = p@frame@factor
            value, _ = np.linalg.slogdet(dagger(sp['v'])@frame)
            total *= value**m
        error = abs(total-np.exp(1j*ward_phase))
        refinements.append(dict(steps=steps, phase=float(np.angle(total)), error=float(error),
                                minimum_gram=float(minimum_gram)))
    assert refinements[-1]['error'] < .09*refinements[0]['error']
    assert refinements[-1]['error'] < 1e-7
    return dict(site=site, ward_holonomy_phase=ward_phase,
                exact_kato_ward_error=float(exact_error), species=rows, direct_transport=refinements,
                scope='Compact integer on-site loops above the weak chart; holonomy need not equal one')


def toron_extension_control():
    """The zero-toron q^3 Hessian cancellation cannot just be reused at theta != 0."""
    model = RectangularOverlap((2,)*4)
    rng = np.random.default_rng(2026091001)
    directions = [rng.normal(size=(4, model.n)) for _ in range(2)]
    rows = []
    for theta in [np.zeros(4), np.array([.37, -.29, .43, .61])]:
        a = np.broadcast_to((theta/2)[:, None], (4, model.n))
        hessian = np.zeros(model.n)
        for _, q, m in SPECIES:
            sp = model.operator(np.exp(1j*a), q)
            _, _, mixed = model.projector_jet(np.exp(1j*a), q, sp, *directions)
            hessian += m*q*np.diag(mixed).real.reshape(4, model.n).sum(axis=0)
        rows.append(dict(theta=theta.tolist(), summed_density_hessian_norm=float(np.linalg.norm(hessian)),
                         total_hessian_sum=float(hessian.sum())))
    assert rows[0]['summed_density_hessian_norm'] < 1e-9
    assert rows[1]['summed_density_hessian_norm'] > 1e-5
    return dict(rows=rows, conclusion='Cubic charge cancellation at zero potential does not cancel the finite-volume Hessian at arbitrary flat holonomy')


def main():
    result = dict(exact=exact_checks(), flat=flat_checks(), gauge=gauge_loop_checks(),
                  extension_control=toron_extension_control())
    root = Path(__file__).resolve().parents[1]
    paths = ['scripts/compact_measure_holonomy_audit.py', 'scripts/radial_measure_audit.py',
             'scripts/overlap_chirality_audit.py', 'scripts/chiral_measure_audit.py',
             'scripts/gauge_dressed_measure_audit.py', 'scripts/positive_measure_audit.py',
             'UnifiedTheory/Audit/KFCausalCompactHolonomy.lean', 'COMPACT_MEASURE_HOLONOMY.md']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    target = root/'data/compact_measure_holonomy_audit.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
