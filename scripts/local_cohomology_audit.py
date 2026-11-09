#!/usr/bin/env python3
"""First local cohomological descent of the actual overlap anomaly.

The finite torus harmonic remainder is retained. This is a partial Ward
correction, not a completed chiral measure. Float64 results are diagnostics.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import numpy as np
from radial_measure_audit import RectangularOverlap, base_field, density, SPECIES, radial_current
from overlap_chirality_audit import GAMMA5


class CubicalTorus:
    """Oriented periodic cubical chains with a centered contraction.

    A k-cell is labeled by increasing directions and its head site.
    Boundary removes direction mu with sign (-1)^position and coefficient
    f(x)-f(x+mu). P0 anchors the sum; P1 retains the flux at the opposite cut.
    """
    def __init__(self, lengths):
        self.lengths = tuple(lengths)
        if not self.lengths or any(n < 2 for n in self.lengths):
            raise ValueError('Each torus length must be at least two.')
        self.dim = len(self.lengths)
        self.cells = {k: list(itertools.combinations(range(self.dim), k))
                      for k in range(self.dim+1)}

    def zero(self, degree, dtype=float):
        return {cell: np.zeros(self.lengths, dtype=dtype)
                for cell in self.cells.get(degree, [])}

    def boundary(self, chain):
        if not chain:
            return {}
        degree = len(next(iter(chain)))
        out = self.zero(degree-1, next(iter(chain.values())).dtype)
        for cell, a in chain.items():
            for position, mu in enumerate(cell):
                out[cell[:position]+cell[position+1:]] += (
                    (-1)**position*(a-np.roll(a, -1, axis=mu)))
        return out

    def p_axis(self, a, mu, degree, center):
        if degree:
            cut = (center[mu]-self.lengths[mu]//2) % self.lengths[mu]
            return np.repeat(np.take(a, [cut], axis=mu), self.lengths[mu], axis=mu)
        out = np.zeros_like(a)
        index = [slice(None)]*self.dim
        index[mu] = center[mu]
        out[tuple(index)] = a.sum(axis=mu)
        return out

    def h_axis(self, a, mu, center):
        cut = (center[mu]-self.lengths[mu]//2) % self.lengths[mu]
        z = a-self.p_axis(a, mu, 0, center)
        z = np.roll(z, -cut, axis=mu)
        out = z-np.cumsum(z, axis=mu)  # Negative strict prefix, zero at the cut.
        return np.roll(out, cut, axis=mu)

    def project(self, chain, center):
        out = {}
        for cell, a in chain.items():
            b = a.copy()
            for mu in range(self.dim):
                b = self.p_axis(b, mu, mu in cell, center)
            out[cell] = b
        return out

    def homotopy(self, chain, center):
        if not chain:
            return {}
        degree = len(next(iter(chain)))
        out = self.zero(degree+1, next(iter(chain.values())).dtype)
        for cell, a in chain.items():
            for mu in range(self.dim):
                if mu in cell:
                    continue
                b = a.copy()
                for nu in range(mu):
                    b = self.p_axis(b, nu, nu in cell, center)
                b = self.h_axis(b, mu, center)
                sign = (-1)**sum(nu < mu for nu in cell)
                out[tuple(sorted(cell+(mu,)))] += sign*b
        return out

    def check(self):
        rng = np.random.default_rng(7)
        for center in [tuple(n//2 for n in self.lengths), (0,)*self.dim]:
            for degree in range(self.dim+1):
                chain = {cell: rng.integers(-3, 4, size=self.lengths)
                         for cell in self.cells[degree]}
                dh = self.boundary(self.homotopy(chain, center))
                hd = self.homotopy(self.boundary(chain), center)
                p = self.project(chain, center)
                for cell in chain:
                    assert np.array_equal(dh.get(cell, 0)+hd.get(cell, 0),
                                          chain[cell]-p[cell]), (degree, cell)


def jacobian_resolvent(model, theta, q, count=32):
    """All link derivatives of q tr_spin P(x,x), without a Dirac inverse.

    P' = -(1/2pi) integral_0^infinity (R H' R + R^dag H' R^dag) dt,
    R=(it-H)^-1. H' is supported on one edge and its adjoint. Contracting
    the four-spin blocks obtains every Jacobian column at once.
    """
    links = np.exp(1j*theta)
    sp = model.operator(links, q)
    v, eigenvalues = sp['vectors'], sp['values']
    nodes, weights = np.polynomial.legendre.leggauss(count)
    result = np.zeros((model.n, 4*model.n))
    g5 = np.array(GAMMA5, complex)
    for u, weight in zip((nodes+1)/2, weights/2):
        angle = np.pi*u/2
        t = np.tan(angle)
        dt = np.pi/2/np.cos(angle)**2
        resolvent = (v/(1j*t-eigenvalues))@v.conj().T
        blocks = resolvent.reshape(4, model.n, 4, model.n).transpose(1, 3, 0, 2)
        for mu in range(4):
            tail = model.geom.previous[mu]
            phase = model.boundary[mu]*links[mu]**q
            he = -1j*q*phase[:, None, None]*(g5@model.geom.plus[mu])[None, :, :]
            he_adjoint = he.conj().transpose(0, 2, 1)
            # x: density site; j: edge head; a,b,c: spin indices.
            term = np.einsum('xjab,jbc,jxca->xj', blocks, he,
                             blocks[tail, :, :, :], optimize=True)
            term += np.einsum('xjab,jbc,jxca->xj', blocks[:, tail, :, :],
                              he_adjoint, blocks, optimize=True)
            result[:, mu*model.n:(mu+1)*model.n] += -q/np.pi*weight*dt*term.real
    return result, sp


def pack(chain):
    return np.concatenate([a.ravel() for a in chain.values()]) if chain else np.array([])


def unpack(torus, vector, degree):
    return {cell: a.reshape(torus.lengths) for cell, a in
            zip(torus.cells[degree], np.asarray(vector).reshape(-1, np.prod(torus.lengths)))}


def divergence(torus, current):
    return pack(torus.boundary(unpack(torus, current, 1)))


def gradient(model, omega):
    return np.array([omega-omega[tail] for tail in model.geom.previous])


def field_strength(torus, potential):
    a = np.asarray(potential).reshape(torus.dim, *torus.lengths)
    return np.concatenate([(a[nu]-np.roll(a[nu], 1, axis=mu)-a[mu]+
                            np.roll(a[mu], 1, axis=nu)).ravel()
                           for mu, nu in torus.cells[2]])


def descend(torus, kernel, potential):
    """j = theta C + r; theta = d tau + anchored(Phi), including r exactly.

    Both homotopies are centered at the density/face anchor, never a fixed
    common origin. This is needed to preserve locality of localized inputs.
    """
    sites = list(itertools.product(*(range(n) for n in torus.lengths)))
    n = len(sites)
    theta = np.empty((n, len(torus.cells[2])*n))
    harmonic = np.empty_like(kernel)
    cycle_error = 0.
    row_error = 0.
    for x, center in enumerate(sites):
        row = unpack(torus, kernel[x], 1)
        cycle_error = max(cycle_error, float(np.linalg.norm(pack(torus.boundary(row)))))
        filled = torus.homotopy(row, center)
        theta[x] = pack(filled)
        harmonic[x] = pack(torus.project(row, center))
        row_error = max(row_error, float(np.linalg.norm(
            pack(torus.boundary(filled))+harmonic[x]-kernel[x])))
    phi = theta.sum(axis=0)
    f = field_strength(torus, potential)
    anchored = np.zeros(n)
    h = np.zeros(torus.dim*n)
    for face in range(theta.shape[1]):
        anchor = face % n
        eta = theta[:, face].copy()
        eta[anchor] -= phi[face]
        h += f[face]*pack(torus.homotopy(unpack(torus, eta, 0), sites[anchor]))
        anchored[anchor] += phi[face]*f[face]
    winding = harmonic@np.asarray(potential).ravel()
    div_h = divergence(torus, h)
    remainder = anchored+winding
    phi_boundary = pack(torus.boundary(unpack(torus, phi, 2)))
    co_closed_error = float(np.linalg.norm(phi_boundary+harmonic.sum(axis=0)))
    reconstruction = kernel@np.asarray(potential).ravel()-div_h-remainder
    return dict(h=h, div_h=div_h, remainder=remainder, anchored=anchored,
                winding=winding, phi=phi, harmonic=harmonic,
                cycle_error=cycle_error, row_error=row_error,
                reconstruction_error=float(np.linalg.norm(reconstruction)),
                phi_boundary_norm=float(np.linalg.norm(phi_boundary)),
                finite_torus_constraint_error=co_closed_error)


def integrated_kernel(model, potential, species=SPECIES, field_nodes=6, resolvent_nodes=32):
    """Compute integral a'(tA) dt and integral (1-t) a'(tA) dt together."""
    nodes, weights = np.polynomial.legendre.leggauss(field_nodes)
    kernel = np.zeros((model.n, 4*model.n))
    weighted = np.zeros_like(kernel)
    average_density = np.zeros(model.n)
    gap = np.inf
    for t, weight in zip((nodes+1)/2, weights/2):
        for _, q, multiplicity in species:
            jac, sp = jacobian_resolvent(model, t*potential, q, resolvent_nodes)
            kernel += multiplicity*weight*jac
            weighted += multiplicity*weight*(1-t)*jac
            average_density += multiplicity*weight*density(model, sp['p'], q)
            gap = min(gap, sp['gap'])
    return kernel, weighted, average_density, float(gap)


def exact_chain_checks():
    rows = []
    for lengths in [(3,), (3, 4), (3, 4, 3), (3, 3, 3, 3)]:
        torus = CubicalTorus(lengths)
        torus.check()
        # Check d^2=0 independently on every applicable degree.
        rng = np.random.default_rng(72)
        for degree in range(2, torus.dim+1):
            chain = {cell: rng.integers(-5, 6, size=lengths) for cell in torus.cells[degree]}
            assert np.all(pack(torus.boundary(torus.boundary(chain))) == 0)
        rows.append(dict(lengths=lengths, all_degrees_exact=True))
    support = []
    for length in [6, 10, 16]:
        torus = CubicalTorus((length,)*4)
        center = (length//2,)*4
        face = torus.zero(2, np.int64)
        face[(0, 1)][center] = 1
        loop = torus.boundary(face)
        filled = torus.homotopy(loop, center)
        assert np.all(pack(torus.project(loop, center)) == 0)
        assert np.array_equal(pack(torus.boundary(filled)), pack(loop))
        nonzero = int(np.count_nonzero(pack(filled)))
        assert nonzero == 1
        support.append(dict(length=length, filling_nonzero_faces=nonzero))
    torus = CubicalTorus((5, 6, 3, 4))
    center = (2, 3, 1, 2)
    winding = torus.zero(1, np.int64)
    winding[(0,)][:, center[1], center[2], center[3]] = 1
    assert np.all(pack(torus.boundary(winding)) == 0)
    assert np.array_equal(pack(torus.project(winding, center)), pack(winding))
    assert np.all(pack(torus.boundary(torus.homotopy(winding, center))) == 0)
    rng = np.random.default_rng(22)
    a = rng.integers(-3, 4, size=(4, np.prod(torus.lengths)))
    face = {cell: rng.integers(-3, 4, size=torus.lengths) for cell in torus.cells[2]}
    assert pack(face)@field_strength(torus, a) == pack(torus.boundary(face))@a.ravel()
    omega = rng.integers(-3, 4, size=torus.lengths)
    gauge = np.array([omega-np.roll(omega, 1, axis=mu) for mu in range(4)])
    assert np.all(field_strength(torus, gauge) == 0)
    return dict(arithmetic='exact int64 (small bounded sums; no overflow)',
                curvature_gradient_zero=True, discrete_stokes_duality=True,
                contraction_and_boundary_squared=rows, translated_local_loop_fillings=support,
                noncontractible_cycle_retained=True)


def jacobian_checks():
    model = RectangularOverlap((2, 2, 2, 2))
    a = base_field(model)
    links = np.exp(1j*a)
    sp = model.operator(links, 6)
    exact = np.zeros((model.n, 4*model.n))
    for edge in range(4*model.n):
        e = np.zeros_like(a)
        e.flat[edge] = 1
        dp = model.projector_derivative(links, 6, sp, e)
        exact[:, edge] = 6*np.diag(dp).real.reshape(4, model.n).sum(axis=0)
    rows = []
    for count in [16, 24, 32]:
        jac, _ = jacobian_resolvent(model, a, 6, count)
        err = float(np.linalg.norm(jac-exact))
        rows.append(dict(nodes=count, error_against_spectral_derivative=err))
    assert rows[-1]['error_against_spectral_derivative'] < 1e-11
    # A non-infinitesimal real gauge change, with some links crossing principal logs.
    omega = np.random.default_rng(12).uniform(-2, 2, model.n)
    shifted, _ = jacobian_resolvent(model, a+gradient(model, omega), 6, 32)
    gauge_error = float(np.linalg.norm(shifted-jac))
    assert gauge_error < 1e-11
    return dict(reference_norm=float(np.linalg.norm(exact)), quadrature=rows,
                large_real_gauge_change_error=gauge_error)


def summarize_descent(result):
    return {name: float(np.linalg.norm(result[name])) for name in
            ['h', 'div_h', 'remainder', 'anchored', 'winding', 'phi', 'harmonic']} | {
                name: result[name] for name in ['cycle_error', 'row_error', 'reconstruction_error',
                                           'phi_boundary_norm', 'finite_torus_constraint_error']}


def actual_descent(lengths, field_nodes=6, resolvent_nodes=32, phase_check=False):
    model = RectangularOverlap(lengths)
    torus = CubicalTorus(lengths)
    # Independent fields at every site: a tiled background could hide winding effects.
    a = np.random.default_rng(2026090906).uniform(-.018, .018, (4, model.n))
    j, jw, avg, gap = integrated_kernel(model, a, field_nodes=field_nodes,
                                       resolvent_nodes=resolvent_nodes)
    anomaly = sum(m*density(model, model.operator(np.exp(1j*a), q)['p'], q)
                  for _, q, m in SPECIES)
    zero_anomaly = sum(m*density(model, model.operator(np.ones_like(a), q)['p'], q)
                       for _, q, m in SPECIES)
    result, weighted = [descend(torus, k, a) for k in [j, jw]]
    fundamental_error = float(np.linalg.norm(j@a.ravel()-anomaly))
    averaged_error = float(np.linalg.norm(jw@a.ravel()-avg))
    assert fundamental_error < 2e-11
    assert averaged_error < 2e-11
    assert result['reconstruction_error'] < 1e-11
    assert result['finite_torus_constraint_error'] < 1e-11
    assert weighted['reconstruction_error'] < 1e-11
    assert gap > .7
    report = dict(lengths=lengths, field_nodes=field_nodes, resolvent_nodes=resolvent_nodes,
                  minimum_sampled_kernel_gap=gap, density_norm=float(np.linalg.norm(anomaly)),
                  free_density_roundoff=float(np.linalg.norm(zero_anomaly)),
                  fundamental_theorem_error=fundamental_error,
                  average_density_error=averaged_error,
                  topological_column_sum_error=float(np.linalg.norm(j.sum(axis=0))),
                  first_descent=summarize_descent(result),
                  averaged_first_descent=summarize_descent(weighted))
    if phase_check:
        omega = np.random.default_rng(2026090907).uniform(-2, 2, model.n)
        bomega = gradient(model, omega)
        ashift = a+bomega
        js, jws, _, _ = integrated_kernel(model, ashift, field_nodes=field_nodes,
                                           resolvent_nodes=resolvent_nodes)
        shifted = descend(torus, js, ashift)
        shifted_w = descend(torus, jws, ashift)
        c = -float(a.ravel()@weighted['h'])
        cs = -float(ashift.ravel()@shifted_w['h'])
        expected_shift = -float(omega@weighted['div_h'])
        current_gauge = sum(m*radial_current(model, a, q, bomega, count=field_nodes)['current']
                            for _, q, m in SPECIES)
        defect_before = current_gauge+float(omega@anomaly)
        defect_after = defect_before+(cs-c)
        expected_remainder = float(omega@weighted['remainder'])
        checks = dict(kernel_gauge_error=float(np.linalg.norm(js-j)),
                      current_h_gauge_error=float(np.linalg.norm(shifted['h']-result['h'])),
                      remainder_gauge_error=float(np.linalg.norm(shifted['remainder']-result['remainder'])),
                      phase_correction=c, phase_change=cs-c,
                      predicted_phase_change=expected_shift,
                      phase_change_error=abs(cs-c-expected_shift),
                      ward_defect_before=defect_before, ward_defect_after=defect_after,
                      predicted_remaining_ward_defect=expected_remainder,
                      corrected_ward_error=abs(defect_after-expected_remainder))
        assert checks['kernel_gauge_error'] < 1e-10
        assert checks['current_h_gauge_error'] < 1e-10
        assert checks['remainder_gauge_error'] < 1e-10
        assert checks['phase_change_error'] < 1e-10
        assert checks['corrected_ward_error'] < 1e-10
        # Independent quadrature refinement controls both integrals and the correction.
        j2, jw2, _, _ = integrated_kernel(model, a, field_nodes=field_nodes+2,
                                           resolvent_nodes=resolvent_nodes+8)
        refined = descend(torus, jw2, a)
        checks['kernel_quadrature_refinement_error'] = float(np.linalg.norm(j2-j))
        checks['weighted_kernel_quadrature_refinement_error'] = float(np.linalg.norm(jw2-jw))
        checks['phase_quadrature_refinement_error'] = abs(c+float(a.ravel()@refined['h']))
        assert checks['kernel_quadrature_refinement_error'] < 1e-10
        assert checks['phase_quadrature_refinement_error'] < 1e-12
        report['phase_and_gauge_checks'] = checks
    print(json.dumps(report, indent=2), flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/local_cohomology_audit.json'))
    parser.add_argument('--lengths', type=int, nargs=4, action='append',
                        help='Override tested four-dimensional volumes (may repeat).')
    args = parser.parse_args()
    report = dict(scope='First cohomological descent only; field-strength and torus winding remainder retained',
                  exact_chain_checks=exact_chain_checks(), jacobian_checks=jacobian_checks())
    report['overlap_descent'] = [actual_descent(lengths, phase_check=(i == 0)) for i, lengths in
                                  enumerate(args.lengths or [(2, 2, 2, 2), (3, 3, 3, 3)])]
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/local_cohomology_audit.py', 'scripts/radial_measure_audit.py',
               'scripts/positive_measure_audit.py', 'scripts/gauge_dressed_measure_audit.py',
               'scripts/chiral_measure_audit.py', 'scripts/overlap_chirality_audit.py',
               'UnifiedTheory/Audit/KFCausalLocalCohomology.lean']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest()
                              for p in sources if (root/p).exists()}
    report['arithmetic'] = 'Float64 diagnostics except explicit bounded integer chain checks; no interval certificate'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print('Wrote', args.output, flush=True)


if __name__ == '__main__':
    main()
