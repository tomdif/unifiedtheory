#!/usr/bin/env python3
"""Positive finite Weyl measure: consistency, slab locality, and gap limitation.

Float64 overlap diagnostics are distinct from exact controls and Lean proofs.
This removes the determinant phase and is not a physical chiral continuum.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import sympy as s

from chiral_measure_audit import determinant_transport, inverse_sqrt
from gauge_dressed_measure_audit import DressedOverlap, SPECIES


def positive_current(model, links, charge, direction, spectrum=None):
    if spectrum is None:
        spectrum = model.operator(links, charge)
    dp = model.projector_derivative(links, charge, spectrum, direction)
    dd = 2*model.geom.g5@dp
    return float(np.trace(np.linalg.solve(spectrum['d'], dd)@spectrum['p']).imag)


def direct_frame(model, links, charge, spectrum=None):
    if spectrum is None:
        spectrum = model.operator(links, charge)
    columns = np.linalg.solve(spectrum['d'], model.b0)
    factor, minimum_gram = inverse_sqrt(columns.conj().T@columns)
    frame = columns@factor
    matrix = model.b0.conj().T@spectrum['d']@frame
    errors = [np.linalg.norm(frame.conj().T@frame-np.eye(frame.shape[1])),
              np.linalg.norm(spectrum['p']@frame-frame), np.linalg.norm(matrix-factor)]
    assert max(errors) < 1e-10
    assert np.linalg.eigvalsh(factor)[0] > 0
    return dict(frame=frame, matrix=matrix, residual=float(max(errors)), minimum_gram=minimum_gram)


def exact_checks():
    phases = []
    for z in [s.Integer(2), 3+4*s.I, -5+12*s.I, -s.I]:
        omega = s.simplify(s.Abs(z)/z)
        assert s.simplify(omega*z-s.Abs(z)) == 0
        assert s.simplify(s.conjugate(omega)*omega) == 1
        phases.append(dict(z=str(z), correction=str(omega), corrected=str(s.Abs(z))))
    inverses = []
    for size in [2, 4, 8, 16, 32]:
        shift = s.zeros(size)
        shift[0, size-1] = -1
        for j in range(1, size):
            shift[j, j-1] = 1
        inv = s.Matrix(size, size, lambda i, j: s.Rational(1, 2) if j <= i else -s.Rational(1, 2))
        assert (s.eye(size)-shift)*inv == inv*(s.eye(size)-shift) == s.eye(size)
        assert all(s.Abs(v) == s.Rational(1, 2) for v in inv)
        inverses.append(dict(time_length=size, maximum_separation=size//2,
                             inverse_entry_abs="1/2", inverse_identity=True))
    # A counterterm built from individual plaquettes cannot couple these edges.
    supports = []
    for length in [4, 8, 12, 16]:
        model = DressedOverlap(spatial_length=length)
        idx = {x: j for j, x in enumerate(model.geom.sites)}
        e = (1, idx[(0, 1, 0, 0)])
        f = (0, idx[(length//2, 1, 0, 0)])
        shared = 0
        for x in range(model.n):
            for mu in range(4):
                for nu in range(mu+1, 4):
                    # Backward-oriented elementary plaquette, with link heads.
                    support = {(mu, x), (nu, int(model.geom.previous[mu][x])),
                               (mu, int(model.geom.previous[nu][x])), (nu, x)}
                    shared += int(e in support and f in support)
        assert shared == 0
        supports.append(dict(spatial_length=length, plaquettes_containing_both_edges=shared,
                             mixed_counterterm_increment=0))
    return dict(arithmetic="exact SymPy complex rationals; integer plaquette supports",
                phase_corrections=phases, antiperiodic_inverse=inverses,
                plaquette_counterterms=supports,
                limitation="inverse nondecay does not prove nonlocality of the full current")


def consistency_checks():
    model = DressedOverlap()
    rng = np.random.default_rng(2026090901)
    links = np.exp(1j*model.theta)
    q = 6
    spectrum = model.operator(links, q)
    u = rng.uniform(-1, 1, (4, model.n))
    v = rng.uniform(-1, 1, (4, model.n))
    positive = positive_current(model, links, q, u, spectrum)
    tree = model.current_contraction(links, q, u)
    basis_rows = []
    direct = direct_frame(model, links, q, spectrum)
    datum = model.measure(links, q)
    corrected = datum['v'].copy()
    corrected[:, 0] *= datum['phase'].conjugate()
    corrected_matrix = datum['b'].conj().T@spectrum['d']@corrected
    corrected_phase, corrected_logabs = np.linalg.slogdet(corrected_matrix)
    assert abs(corrected_phase-1) < 1e-10
    assert abs(corrected_logabs-datum['logabs']) < 1e-10
    for step in [2e-4, 1e-4]:
        plus = model.measure(links*np.exp(1j*step*u), q)
        minus = model.measure(links*np.exp(-1j*step*u), q)
        phase_derivative = np.angle(plus['phase']*minus['phase'].conjugate())/(2*step)
        vp, vm = plus['v'].copy(), minus['v'].copy()
        vp[:, 0] *= plus['phase'].conjugate()
        vm[:, 0] *= minus['phase'].conjugate()
        fp = direct_frame(model, links*np.exp(1j*step*u), q)['frame']
        fm = direct_frame(model, links*np.exp(-1j*step*u), q)['frame']
        direct_connection = float((1j*np.trace(direct['frame'].conj().T@(fp-fm)/(2*step))).real)
        connection = float((1j*(np.trace(corrected.conj().T@(vp-vm)/(2*step))-
                                np.trace(datum['b'].conj().T@(plus['b']-minus['b'])/(2*step)))).real)
        basis_rows.append(dict(step=step, positive_current=positive,
                               tree_plus_phase_derivative=tree+float(phase_derivative),
                               corrected_frame_connection=connection,
                               phase_relation_error=abs(positive-tree-phase_derivative),
                               frame_connection_error=abs(positive-connection),
                               direct_frame_connection=direct_connection,
                               direct_frame_error=abs(positive-direct_connection)))
    assert basis_rows[-1]['phase_relation_error'] < 1e-7
    assert basis_rows[-1]['frame_connection_error'] < 1e-7
    assert basis_rows[-1]['direct_frame_error'] < 1e-7
    # Full coefficient vector makes the Ward equation independent of one gauge tangent.
    coefficients = []
    for j in range(4*model.n):
        direction = np.zeros_like(u)
        direction.flat[j] = 1
        coefficients.append(positive_current(model, links, q, direction, spectrum))
    density = q*np.array([sum((spectrum['p']-model.pbar)[spin*model.n+x, spin*model.n+x].real
                              for spin in range(4)) for x in range(model.n)])
    ward = float(np.linalg.norm(model.gradient.T@np.array(coefficients)+density[1:]))
    assert ward < 1e-10
    alpha = rng.uniform(-np.pi, np.pi, model.n)
    gauge_error = abs(positive-positive_current(model, model.gauge_links(links, alpha), q, u))
    assert gauge_error < 1e-10
    pu = model.projector_derivative(links, q, spectrum, u)
    pv = model.projector_derivative(links, q, spectrum, v)
    curvature = float((1j*np.trace(spectrum['p']@(pu@pv-pv@pu))).real)
    curl_rows = []
    for step in [2e-4, 1e-4, 5e-5]:
        dujv = (positive_current(model, links*np.exp(1j*step*u), q, v)-
                positive_current(model, links*np.exp(-1j*step*u), q, v))/(2*step)
        dvju = (positive_current(model, links*np.exp(1j*step*v), q, u)-
                positive_current(model, links*np.exp(-1j*step*v), q, u))/(2*step)
        curl_rows.append(dict(step=step, curl=dujv-dvju, projector_curvature=curvature,
                              error=abs(dujv-dvju-curvature)))
    assert curl_rows[-1]['error'] < 5e-8
    assert curl_rows[-1]['error'] < curl_rows[0]['error']/3
    direct_rows = []
    transformed_links = model.gauge_links(links, alpha)
    for name, charge, multiplicity in SPECIES:
        before = direct_frame(model, links, charge)
        after = direct_frame(model, transformed_links, charge)
        g = np.kron(np.eye(4), np.diag(np.exp(1j*charge*alpha)))
        gb = model.b0.conj().T@g@model.b0
        covariance = float(np.linalg.norm(after['frame']-g@before['frame']@gb.conj().T))
        phase, logabs = np.linalg.slogdet(before['matrix'])
        old = model.measure(links, charge)
        assert covariance < 1e-10 and abs(phase-1) < 1e-10
        assert abs(logabs-old['logabs']) < 1e-10
        direct_rows.append(dict(species=name, charge=charge, multiplicity=multiplicity,
                                matrix_residual=before['residual'], gauge_covariance_residual=covariance,
                                phase_error=float(abs(phase-1)), logabs_error=abs(float(logabs)-old['logabs'])))
    # A physical field-space circle, not only a pure-gauge loop.
    # Include both moving bases through conjugate antifermion transport.
    loop_rows = []
    radius = .006
    for count in [32, 64, 128]:
        fermions, antifermions = [], []
        integral = 0.
        min_singular = np.inf
        for k in range(count):
            t = 2*np.pi*k/count
            theta = model.theta+radius*(np.cos(t)*u+np.sin(t)*v)
            direction = radius*(-np.sin(t)*u+np.cos(t)*v)
            loop_links = np.exp(1j*theta)
            m = model.measure(loop_links, q)
            vf = m['v'].copy()
            vf[:, 0] *= m['phase'].conjugate()
            fermions.append(vf)
            antifermions.append(m['b'])
            integral += 2*np.pi/count*positive_current(model, loop_links, q, direction)
            min_singular = min(min_singular, m['min_singular'])
        pf, overlap = determinant_transport(fermions)
        # B stays in the same fixed subspace. Its adjacent rotations are
        # diagonal; multiply their diagonal phases, avoiding diagonal LU.
        pb = 1+0j
        for k in range(count):
            rotation = antifermions[(k+1) % count].conj().T@antifermions[k]
            diagonal = np.diag(rotation)
            assert np.linalg.norm(rotation-np.diag(diagonal)) < 1e-12
            assert np.max(np.abs(np.abs(diagonal)-1)) < 1e-12
            pb *= np.prod(diagonal)
        transport = pf*pb.conjugate()
        error = float(abs(transport-np.exp(1j*integral)))
        loop_rows.append(dict(steps=count, current_integral=integral,
                              transport_phase=float(np.angle(transport)), error=error,
                              minimum_neighbor_overlap=overlap, minimum_weyl_singular=min_singular))
    assert loop_rows[-1]['error'] < 1e-8
    assert loop_rows[-1]['error'] < loop_rows[0]['error']/12
    return dict(arithmetic="float64; no interval certification", random_seed=2026090901,
                lattice="2^4 links, antiperiodic time fermions", charge=q,
                corrected_determinant_phase_error=float(abs(corrected_phase-1)),
                determinant_logabs_error=abs(float(corrected_logabs)-datum['logabs']),
                direct_basis_species=direct_rows, basis_checks=basis_rows, ward_residual=ward, gauge_residual=gauge_error,
                curvature_checks=curl_rows, contractible_loop=loop_rows)


def locality_checks(root):
    baseline_path = root/'data/gauge_dressed_measure_audit.json'
    baseline = json.loads(baseline_path.read_text())['locality']['rows']
    base = DressedOverlap()
    lookup = {x: j for j, x in enumerate(base.geom.sites)}
    rows = []
    for length, old in zip([4, 8, 12, 16], baseline):
        assert old['spatial_length'] == length
        model = DressedOverlap(spatial_length=length)
        for j, x in enumerate(model.geom.sites):
            model.theta[:, j] = .8*base.theta[:, lookup[tuple(v % 2 for v in x)]]
        for mu, j, _ in model.tree:
            model.theta[mu, j] = 0
        idx = {x: j for j, x in enumerate(model.geom.sites)}
        probe = np.zeros((4, model.n))
        remote = np.zeros_like(probe)
        probe[1, idx[(0, 1, 0, 0)]] = 1
        remote[0, idx[(length//2, 1, 0, 0)]] = 1
        terms = []
        for name, q, multiplicity in SPECIES:
            derivatives = []
            for step in [1e-3, 5e-4]:
                plus = positive_current(model, np.exp(1j*(model.theta+step*remote)), q, probe)
                minus = positive_current(model, np.exp(1j*(model.theta-step*remote)), q, probe)
                derivatives.append((plus-minus)/(2*step))
            terms.append(dict(species=name, charge=q, multiplicity=multiplicity, derivatives=derivatives))
        total = [sum(t['multiplicity']*t['derivatives'][j] for t in terms) for j in range(2)]
        old_value = old['hypercharge_mu0_total_derivatives'][-1]
        # Recompute the actual tree-current sum at the final volume to verify
        # that the comparison still uses precisely the same field and edges.
        if length == 16:
            tree_total = 0.
            step = 5e-4
            for _, q, multiplicity in SPECIES:
                plus = model.current_contraction(np.exp(1j*(model.theta+step*remote)), q, probe)
                minus = model.current_contraction(np.exp(1j*(model.theta-step*remote)), q, probe)
                tree_total += multiplicity*(plus-minus)/(2*step)
            assert abs(tree_total-old_value) < 1e-10
        assert abs(total[0]-total[1]) < 1e-8
        rows.append(dict(spatial_length=length, minimum_endpoint_distance=length//2-1,
                         positive_current_terms=terms, positive_hypercharge_derivatives=total,
                         previous_tree_hypercharge_derivative=old_value,
                         absolute_response_reduction=abs(old_value/total[-1])))
    assert abs(rows[-1]['positive_hypercharge_derivatives'][-1]) < 1e-9
    assert rows[-1]['absolute_response_reduction'] > 1000
    assert all(abs(rows[j+1]['positive_hypercharge_derivatives'][-1]) <
               abs(rows[j]['positive_hypercharge_derivatives'][-1]) for j in range(3))
    gaps = [dict(time_length=t, free_dirac_gap=float(2*np.sin(np.pi/(2*t))),
                 inverse_entry_abs=.5) for t in [2, 4, 8, 16, 32, 64, 128]]
    return dict(arithmetic="float64 central differences; no interval certification",
                lattice_family="L x 2 x 2 x 2; time length remains 2 in locality scan",
                steps=[1e-3, 5e-4], rows=rows, free_time_gap_scan=gaps,
                final_tree_sum_recomputed=tree_total,
                limitation="slab diagnostic and gapped-domain locality, not a massless 4D continuum or full-current no-go")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/positive_measure_audit.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = dict(exact=exact_checks(), consistency=consistency_checks(), locality=locality_checks(root))
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [
        'UnifiedTheory/Audit/KFCausalPositiveMeasure.lean', 'scripts/positive_measure_audit.py',
        'scripts/gauge_dressed_measure_audit.py', 'scripts/chiral_measure_audit.py',
        'scripts/overlap_chirality_audit.py', 'data/gauge_dressed_measure_audit.json']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
