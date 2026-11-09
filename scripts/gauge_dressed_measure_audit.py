#!/usr/bin/env python3
"""Gauge-orbit extension of a finite overlap Weyl measure.

Tree dressing is exact compact U(1) transport. Locality of the resulting
measure current and continuum/physical closure are not claimed.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s

from chiral_measure_audit import OverlapFamily, inverse_sqrt, determinant_transport
from overlap_chirality_audit import equal


SPECIES = [('Q', 1, 6), ('uc', -4, 3), ('dc', 2, 3), ('L', -3, 2), ('ec', 6, 1)]


def exact_checks():
    phases = [s.Integer(1), (3+4*s.I)/5, (5-12*s.I)/13, (8+15*s.I)/17]
    # Four-site rooted line, plus a closing chord, with rational U(1) values.
    edges = [(1, 0), (2, 1), (3, 2), (0, 3)]
    links = [phases[1], phases[2], phases[3], phases[1]*phases[2]]

    def dress(us):
        cs = [s.Integer(1)]
        for j in range(3):
            cs.append(s.simplify(us[j]*cs[-1]))
        barred = [s.simplify(us[e]*cs[t]/cs[h]) for e, (h, t) in enumerate(edges)]
        return cs, barred

    c, barred = dress(links)
    assert barred[:3] == [1, 1, 1]
    count = 0
    for gauge in itertools.product(phases, repeat=4):
        transformed = [s.simplify(gauge[h]*u/gauge[t]) for (h, t), u in zip(edges, links)]
        cg, bg = dress(transformed)
        assert all(s.simplify(a-b) == 0 for a, b in zip(bg, barred))
        assert all(s.simplify(cg[j]-gauge[j]*c[j]/gauge[0]) == 0 for j in range(4))
        count += 1
    cmat = s.diag(phases[1], phases[2])
    d = s.diag(2, 3)
    v = s.Matrix([1, 0])
    b = v
    correct = (cmat*b).H*(cmat*d*cmat.H)*(cmat*v)
    wrong = b.H*(cmat*d*cmat.H)*(cmat*v)
    equal(correct, b.H*d*v)
    assert s.simplify(wrong[0]/correct[0]) == phases[1]
    # A prefix divergence inverse has no uniform decay as a map on arbitrary sources.
    flows = []
    for radius in [1, 4, 16, 64]:
        far = 2*radius+3
        a = [s.Integer(j == 0)-s.Integer(j == far) for j in range(far+1)]
        currents = [sum(a[:j+1]) for j in range(far)]
        divergence = [currents[0]]+[currents[j]-currents[j-1] for j in range(1, far)]+[-currents[-1]]
        assert divergence == a and sum(a) == 0 and currents[radius+1] == 1
        flows.append(dict(radius=radius, source_sites=[0, far], probe_edge=radius+1, response=1))
    eta = 4*6*s.Rational(1, 48)
    rho = eta/(2*(1-eta))
    assert eta == rho == s.Rational(1, 2)
    assert 1-rho*rho == s.Rational(3, 4)
    return dict(arithmetic="exact SymPy complex rationals and integers", gauge_frames=count,
                tree_edges_normalized=True, root_phase_included=True,
                unpaired_antifermion_negative_control=str(phases[1]),
                prefix_current_dipoles=flows,
                universal_slice_bounds=dict(max_integer_charge=6, link_angle="1/48",
                                            kernel_gap="1/2", projector_distance="1/2",
                                            reference_gram="3/4",
                                            dirac_smallest_singular_value="sqrt(2)-1"),
                source_locality_scope="arbitrary zero-sum sources, not a no-go for the actual anomaly density")


class DressedOverlap:
    def __init__(self, spatial_length=2):
        self.geom = OverlapFamily(length=2)
        if spatial_length != 2:
            # A longer first spatial direction; the other three lengths stay 2.
            self.geom.sites = list(itertools.product(range(spatial_length), range(2), range(2), range(2)))
            self.geom.count = len(self.geom.sites)
            self.geom.dimension = 4*self.geom.count
            self.geom.eye = np.eye(self.geom.dimension, dtype=complex)
            self.geom.g5 = np.kron(np.diag([1, 1, -1, -1]), np.eye(self.geom.count))
            lookup = {x: j for j, x in enumerate(self.geom.sites)}
            lengths = [spatial_length, 2, 2, 2]
            self.geom.previous = [np.array([
                lookup[tuple((v-1) % lengths[k] if k == mu else v for k, v in enumerate(x))]
                for x in self.geom.sites]) for mu in range(4)]
        self.n = self.geom.count
        self.eye = self.geom.eye
        self.tree = []
        for j, x in enumerate(self.geom.sites):
            if j:
                mu = next(mu for mu in range(4) if x[mu] > 0)
                self.tree.append((mu, j, int(self.geom.previous[mu][j])))
        self.b0 = self.eye[:, np.diag(self.geom.g5).real > 0]
        self.pbar = self.b0@self.b0.conj().T
        free = self.operator(np.ones((4, self.n), complex), 1)
        self.w0 = free['v']
        self.p0 = free['p']
        self.rng = np.random.default_rng(9904009)
        self.theta = self.rng.uniform(-1/48, 1/48, (4, self.n))
        self.tangent = self.rng.uniform(-1, 1, self.theta.shape)
        for mu, j, _ in self.tree:
            self.theta[mu, j] = self.tangent[mu, j] = 0
        self.gradient = np.zeros((4*self.n, self.n-1))
        for mu in range(4):
            for j, previous in enumerate(self.geom.previous[mu]):
                if j:
                    self.gradient[mu*self.n+j, j-1] += 1
                if previous:
                    self.gradient[mu*self.n+j, previous-1] -= 1
        self.potential = np.zeros((self.n-1, 4*self.n))
        for mu, j, parent in self.tree:
            if parent:
                self.potential[j-1] = self.potential[parent-1]
            self.potential[j-1, mu*self.n+j] += 1
        self.horizontal = np.eye(4*self.n)-self.gradient@self.potential
        assert np.array_equal(self.potential@self.gradient, np.eye(self.n-1))
        assert np.array_equal(self.horizontal@self.gradient, np.zeros_like(self.gradient))

    def operator(self, links, charge):
        kernel = 3*self.eye.copy()
        for mu in range(4):
            t = np.zeros((self.n, self.n), complex)
            values = links[mu]**charge
            if mu == 3:
                # Antiperiodic fermion boundary in Euclidean time; links stay periodic.
                values = values*np.array([-1 if x[3] == 0 else 1 for x in self.geom.sites])
            t[np.arange(self.n), self.geom.previous[mu]] = values
            kernel -= np.kron(self.geom.plus[mu], t)+np.kron(self.geom.minus[mu], t.conj().T)
        h = self.geom.g5@kernel
        assert np.linalg.norm(h-h.conj().T) < 1e-12
        vals, vecs = np.linalg.eigh(h)
        v = vecs[:, vals > 0]
        p = v@v.conj().T
        d = self.eye+self.geom.g5@(2*p-self.eye)
        return dict(p=p, d=d, v=v, gap=float(np.min(np.abs(vals))), values=vals, vectors=vecs)

    def projector_derivative(self, links, charge, spectrum, direction):
        dh = np.zeros_like(self.eye)
        for mu in range(4):
            dt = np.zeros((self.n, self.n), complex)
            values = 1j*charge*direction[mu]*links[mu]**charge
            if mu == 3:
                values = values*np.array([-1 if x[3] == 0 else 1 for x in self.geom.sites])
            dt[np.arange(self.n), self.geom.previous[mu]] = values
            dh -= np.kron(self.geom.plus[mu], dt)+np.kron(self.geom.minus[mu], dt.conj().T)
        dh = self.geom.g5@dh
        vals, vecs = spectrum['values'], spectrum['vectors']
        positive = vals > 0
        mask = positive[:, None] != positive[None, :]
        divided = np.zeros((len(vals), len(vals)))
        numerator = positive.astype(float)[:, None]-positive.astype(float)[None, :]
        denominator = vals[:, None]-vals[None, :]
        divided[mask] = numerator[mask]/denominator[mask]
        return vecs@(divided*(vecs.conj().T@dh@vecs))@vecs.conj().T

    def current(self, links, charge):
        _, barred = self.compact_dressing(links)
        spectrum = self.operator(barred, charge)
        p = spectrum['p']
        gram = self.w0.conj().T@p@self.w0
        gram_inverse = np.linalg.solve(gram, np.eye(gram.shape[0]))
        ell = np.zeros(4*self.n)
        tree_indices = {mu*self.n+j for mu, j, _ in self.tree}
        for index in range(4*self.n):
            if index in tree_indices:
                continue
            direction = np.zeros((4, self.n))
            direction.flat[index] = 1
            dp = self.projector_derivative(barred, charge, spectrum, direction)
            ell[index] = -np.trace(gram_inverse@(self.w0.conj().T@p@dp@self.w0)).imag
        density = charge*np.array([sum((p-self.pbar)[spin*self.n+x, spin*self.n+x].real
                                      for spin in range(4)) for x in range(self.n)])
        current = self.horizontal.T@ell-self.potential.T@density[1:]
        assert np.linalg.norm(self.gradient.T@current+density[1:]) < 1e-12
        return dict(current=current, ell=ell, density=density, spectrum=spectrum)

    def current_contraction(self, links, charge, direction):
        """Evaluate one current contraction without constructing every coefficient."""
        _, barred = self.compact_dressing(links)
        spectrum = self.operator(barred, charge)
        p = spectrum['p']
        gram = self.w0.conj().T@p@self.w0
        tangent = (self.horizontal@direction.ravel()).reshape(4, self.n)
        dp = self.projector_derivative(barred, charge, spectrum, tangent)
        coefficient = self.w0.conj().T@p@dp@self.w0
        horizontal = -np.trace(np.linalg.solve(gram, coefficient)).imag
        density = charge*np.array([sum((p-self.pbar)[spin*self.n+x, spin*self.n+x].real
                                      for spin in range(4)) for x in range(self.n)])
        return float(horizontal-density[1:]@(self.potential@direction.ravel()))

    def compact_dressing(self, links):
        c = np.ones(self.n, complex)
        for mu, j, parent in self.tree:
            c[j] = links[mu, j]*c[parent]
        barred = np.array([links[mu]*c[previous]/c for mu, previous in enumerate(self.geom.previous)])
        return c, barred

    def gauge_links(self, links, alpha):
        return np.array([links[mu]*np.exp(1j*(alpha-alpha[previous]))
                         for mu, previous in enumerate(self.geom.previous)])

    def slice_frame(self, p):
        factor, smallest = inverse_sqrt(self.w0.conj().T@p@self.w0)
        return p@self.w0@factor, smallest

    def measure(self, links, charge, naive=False):
        c, barred = self.compact_dressing(links)
        raw = self.operator(links, charge)
        reduced = self.operator(barred, charge)
        vslice, gram_min = self.slice_frame(reduced['p'])
        cmatrix = np.kron(np.eye(4), np.diag(c**charge))
        v, b = cmatrix@vslice, cmatrix@self.b0
        matrix = b.conj().T@raw['d']@v
        invariant = self.b0.conj().T@reduced['d']@vslice
        errors = [np.linalg.norm(matrix-invariant),
                  np.linalg.norm(raw['p']-cmatrix@reduced['p']@cmatrix.conj().T),
                  np.linalg.norm(raw['d']@raw['p']-self.pbar@raw['d']),
                  np.linalg.norm(v.conj().T@v-np.eye(v.shape[1]))]
        phase, logabs = np.linalg.slogdet(matrix)
        answer = dict(matrix=matrix, phase=phase, logabs=float(logabs), v=v, b=b,
                      vslice=vslice, p=reduced['p'], c=cmatrix, gap=raw['gap'],
                      gram_min=gram_min, residual=float(max(errors)),
                      min_singular=float(np.linalg.svd(matrix, compute_uv=False)[-1]))
        if naive:
            vnaive, _ = self.slice_frame(raw['p'])
            mn = self.b0.conj().T@raw['d']@vnaive
            pn, ln = np.linalg.slogdet(mn)
            rotation = vnaive.conj().T@v
            bar_rotation = self.b0.conj().T@b
            # B0 selects gamma5-positive spin/site coordinates, so this matrix
            # is diagonal. Use its exact product formula instead of LU division.
            bar_diagonal = np.diag(bar_rotation)
            assert np.linalg.norm(bar_rotation-np.diag(bar_diagonal)) < 1e-12
            assert np.max(np.abs(np.abs(bar_diagonal)-1)) < 1e-12
            bar_phase = np.prod(bar_diagonal)
            fermion_phase, fermion_logabs = np.linalg.slogdet(rotation)
            assert abs(fermion_logabs) < 1e-10
            correction = bar_phase.conjugate()*fermion_phase
            answer.update(naive_phase=pn, correction=correction)
            assert abs(ln-logabs) < 1e-10
            assert abs(pn*correction-phase) < 1e-10
        return answer


def numerical_checks():
    model = DressedOverlap()
    links = np.exp(1j*model.theta)
    original = {q: model.measure(links, q) for _, q, _ in SPECIES}
    errors = [datum['residual'] for datum in original.values()]
    minimum_gap = min(datum['gap'] for datum in original.values())
    minimum_gram = min(datum['gram_min'] for datum in original.values())
    minimum_singular = min(datum['min_singular'] for datum in original.values())
    gauge_rows = []
    original_phase = np.prod([original[q]['phase']**m for _, q, m in SPECIES])
    original_logabs = sum(original[q]['logabs']*m for _, q, m in SPECIES)
    for trial in range(12):
        alpha = model.rng.uniform(-np.pi, np.pi, model.n)
        # Includes root transformations and phases crossing a principal-log cut.
        changed = model.gauge_links(links, alpha)
        phase, naive_phase, correction, logabs = 1+0j, 1+0j, 1+0j, 0.
        maximum = 0.
        for _, charge, multiplicity in SPECIES:
            datum = model.measure(changed, charge, naive=True)
            maximum = max(maximum, datum['residual'], float(np.linalg.norm(datum['matrix']-original[charge]['matrix'])))
            phase *= datum['phase']**multiplicity
            naive_phase *= datum['naive_phase']**multiplicity
            correction *= datum['correction']**multiplicity
            logabs += datum['logabs']*multiplicity
        errors.extend([maximum, abs(phase-original_phase), abs(logabs-original_logabs),
                       abs(naive_phase*correction-phase)])
        gauge_rows.append(dict(trial=trial, weyl_matrix_residual=maximum,
                               total_phase_error=float(abs(phase-original_phase)),
                               uncorrected_phase_change=float(np.angle(naive_phase/original_phase)),
                               phase_correction=float(np.angle(correction)),
                               total_logabs_error=float(abs(logabs-original_logabs))))
    # A moving gauge frame supplies precisely the missing vertical connection.
    charge = 6
    datum = original[charge]
    p, vs = datum['p'], datum['vslice']
    density = charge*np.array([np.trace((p-model.pbar)[np.ix_(np.arange(4)*model.n+x,
                                                          np.arange(4)*model.n+x)]).real
                              for x in range(model.n)])
    assert abs(density.sum()) < 1e-11
    # Numerical derivative in a physical slice direction, then add a gauge direction.
    velocity = model.rng.uniform(-1, 1, model.n)
    velocity[0] = 0
    conn_rows = []
    constructed = model.current(links, charge)
    full_direction = model.tangent.ravel()+model.gradient@velocity[1:]
    exact_connection = float(constructed['current']@full_direction)
    assert abs(model.current_contraction(links, charge, full_direction.reshape(4, model.n))-
               exact_connection) < 1e-12
    for step in [1e-4, 5e-5]:
        plus = model.measure(np.exp(1j*(model.theta+step*model.tangent)), charge)
        minus = model.measure(np.exp(1j*(model.theta-step*model.tangent)), charge)
        dvs = (plus['vslice']-minus['vslice'])/(2*step)
        slice_conn = (1j*np.trace(vs.conj().T@dvs)).real
        prescribed = slice_conn-float(density@velocity)
        plusg = model.measure(model.gauge_links(np.exp(1j*(model.theta+step*model.tangent)), step*velocity), charge)
        minusg = model.measure(model.gauge_links(np.exp(1j*(model.theta-step*model.tangent)), -step*velocity), charge)
        dv = (plusg['v']-minusg['v'])/(2*step)
        db = (plusg['b']-minusg['b'])/(2*step)
        measured = (1j*(np.trace(vs.conj().T@dv)-np.trace(model.b0.conj().T@db))).real
        conn_rows.append(dict(step=step, constructed_connection=float(prescribed),
                              frame_derivative_connection=float(measured), error=float(abs(prescribed-measured)),
                              explicit_current_connection=exact_connection,
                              explicit_current_error=float(abs(exact_connection-measured))))
    assert conn_rows[-1]['error'] < 1e-7
    assert conn_rows[-1]['explicit_current_error'] < 1e-7
    assert conn_rows[-1]['explicit_current_error'] < conn_rows[0]['explicit_current_error']/3
    changed_current = model.current(model.gauge_links(links, alpha), charge)
    current_gauge_residual = float(np.linalg.norm(changed_current['current']-constructed['current']))
    assert current_gauge_residual < 1e-10
    # Curl of the explicit current, independently compared to projector curvature.
    u = full_direction.reshape(4, model.n)
    v = model.rng.uniform(-1, 1, (4, model.n))
    spectrum = model.operator(links, charge)
    pu = model.projector_derivative(links, charge, spectrum, u)
    pv = model.projector_derivative(links, charge, spectrum, v)
    curvature = float((1j*np.trace(spectrum['p']@(pu@pv-pv@pu))).real)
    curl_rows = []
    for step in [2e-4, 1e-4]:
        duj = (model.current(links*np.exp(1j*step*u), charge)['current']-
               model.current(links*np.exp(-1j*step*u), charge)['current'])/(2*step)
        dvj = (model.current(links*np.exp(1j*step*v), charge)['current']-
               model.current(links*np.exp(-1j*step*v), charge)['current'])/(2*step)
        curl = float(duj@v.ravel()-dvj@u.ravel())
        curl_rows.append(dict(step=step, current_curl=curl, projector_curvature=curvature,
                              error=abs(curl-curvature)))
    assert curl_rows[-1]['error'] < 1e-7
    assert curl_rows[-1]['error'] < curl_rows[0]['error']/3
    # Full compact gauge loop at the site with largest density, excluding root.
    site = 1+int(np.argmax(np.abs(density[1:])))
    target = np.exp(-2j*np.pi*density[site])
    loop_rows = []
    for count in [64, 128, 256]:
        frames = []
        for j in range(count):
            c = np.ones(model.n, complex)
            c[site] = np.exp(2j*np.pi*charge*j/count)
            frames.append(np.kron(np.eye(4), np.diag(c))@vs)
        transport, min_overlap = determinant_transport(frames)
        loop_rows.append(dict(steps=count, phase_radians=float(np.angle(transport)),
                              connection_phase_radians=float(np.angle(target)),
                              error=float(abs(transport-target)), minimum_neighbor_overlap=min_overlap))
    # Phase may be tiny; always verify it independently, without treating noise as an anomaly.
    assert loop_rows[-1]['error'] < 2e-8
    assert loop_rows[-1]['error'] < loop_rows[0]['error']/12
    assert abs(np.angle(target)) > 1e-7
    assert max(errors) < 1e-9
    assert minimum_gap > 0.5 and minimum_gram > 0.75
    assert minimum_singular > np.sqrt(2)-1
    return dict(arithmetic="float64; no interval certification", random_seed=9904009,
                lattice="periodic 2^4 links; antiperiodic Euclidean-time fermions",
                operator_dimension=64, weyl_matrix_dimension=32,
                species=[dict(name=n, charge=q, multiplicity=m) for n, q, m in SPECIES],
                total_left_handed_components=15, slice_angle_bound="1/48",
                gauge_transformations=gauge_rows, maximum_identity_residual=float(max(errors)),
                minimum_kernel_gap=minimum_gap, minimum_reference_gram=minimum_gram,
                minimum_weyl_singular_value=minimum_singular,
                total_determinant_logabs=float(original_logabs),
                moving_frame_connection=conn_rows, gauge_loop_site=site,
                current_curl_checks=curl_rows, current_gauge_residual=current_gauge_residual,
                current_ward_residual=float(np.linalg.norm(model.gradient.T@constructed['current']+density[1:])),
                maximum_density=float(np.max(np.abs(density))),
                gauge_loop=loop_rows, phase_correction_identity=True,
                scope="gauge-saturated weak slice, index zero, supplied U(1) charges; no spacetime locality or physical QFT claim")


def locality_probe():
    """Actual-current finite-distance diagnostic, including an anomaly-free charge sum.

    Grow one spatial direction only. This is neither a four-dimensional
    continuum limit nor a proof against every possible exponential bound.
    """
    base = DressedOverlap()
    lookup = {x: j for j, x in enumerate(base.geom.sites)}
    rows = []
    for length in [4, 8, 12, 16]:
        model = DressedOverlap(spatial_length=length)
        for j, x in enumerate(model.geom.sites):
            model.theta[:, j] = .8*base.theta[:, lookup[tuple(v % 2 for v in x)]]
        for mu, j, _ in model.tree:
            model.theta[mu, j] = 0
        indices = {x: j for j, x in enumerate(model.geom.sites)}
        probe = np.zeros((4, model.n))
        probe[1, indices[(0, 1, 0, 0)]] = 1

        def response(charge, direction):
            remote = np.zeros_like(probe)
            remote[direction, indices[(length//2, 1, 0, 0)]] = 1
            values = []
            for step in [1e-3, 5e-4]:
                plus = model.current_contraction(np.exp(1j*(model.theta+step*remote)), charge, probe)
                minus = model.current_contraction(np.exp(1j*(model.theta-step*remote)), charge, probe)
                values.append((plus-minus)/(2*step))
            return values

        directions = [dict(remote_direction=mu, derivatives=response(6, mu)) for mu in range(4)]
        terms = [dict(species=name, charge=q, multiplicity=m,
                      derivatives=directions[0]['derivatives'] if q == 6 else response(q, 0))
                 for name, q, m in SPECIES]
        total = [sum(term['multiplicity']*term['derivatives'][i] for term in terms) for i in range(2)]
        assert abs(total[0]-total[1]) < 1e-8
        rows.append(dict(spatial_length=length, lattice_sites=model.n, dirac_dimension=4*model.n,
                         head_separation=length//2, mu0_minimum_endpoint_distance=length//2-1,
                         charge_six_direction_scan=directions, hypercharge_mu0_terms=terms,
                         hypercharge_mu0_total_derivatives=total))
    assert rows[-1]['charge_six_direction_scan'][0]['derivatives'][-1] > 1e-6
    assert rows[-1]['hypercharge_mu0_total_derivatives'][-1] > 1e-6
    assert all(abs(row['derivatives'][-1]) < 1e-8 for row in rows[-1]['charge_six_direction_scan'][1:])
    return dict(arithmetic="float64 central differences; no interval certification",
                lattice_family="L x 2 x 2 x 2; antiperiodic fermion time boundary",
                probe_link=dict(direction=1, head=[0, 1, 0, 0]),
                remote_head="[L/2,1,0,0]", steps=[1e-3, 5e-4], rows=rows,
                interpretation="persistent response for mu=0 in the measured range, including the hypercharge sum",
                limitations="not an asymptotic no-go or a four-dimensional continuum/locality proof; other directions decay to the numerical floor")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/gauge_dressed_measure_audit.json'))
    args = parser.parse_args()
    report = dict(exact=exact_checks(), numerical=numerical_checks(), locality=locality_probe())
    root = Path(__file__).resolve().parents[1]
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [
        'UnifiedTheory/Audit/KFCausalGaugeDressedMeasure.lean', 'scripts/gauge_dressed_measure_audit.py',
        'scripts/chiral_measure_audit.py', 'scripts/overlap_chirality_audit.py']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
