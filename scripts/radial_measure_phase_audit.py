#!/usr/bin/env python3
"""Independent loop and determinant-phase checks for the radial measure current."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

from radial_measure_audit import RectangularOverlap, base_field, SPECIES, radial_current, positive_current
from chiral_measure_audit import inverse_sqrt, determinant_transport


def phase_checks():
    model = RectangularOverlap([2, 2, 2, 2])
    theta = base_field(model)
    rng = np.random.default_rng(2026090903)
    u, v = [rng.uniform(-1, 1, theta.shape) for _ in range(2)]
    free = model.operator(np.ones_like(theta, dtype=complex), 1)
    w0 = free['v']
    b0 = model.eye[:, np.diag(model.geom.g5).real > 0]
    radius = .006
    loop_rows = []
    for count in [32, 64, 128]:
        frames = []
        integral = 0.
        for k in range(count):
            phi = 2*np.pi*k/count
            field = theta+radius*(np.cos(phi)*u+np.sin(phi)*v)
            tangent = radius*(-np.sin(phi)*u+np.cos(phi)*v)
            sp = model.operator(np.exp(1j*field), 6)
            factor, _ = inverse_sqrt(w0.conj().T@sp['p']@w0)
            frames.append(sp['p']@w0@factor)
            integral += 2*np.pi/count*radial_current(model, field, 6, tangent, count=8)['current']
        transport, overlap = determinant_transport(frames)
        loop_rows.append(dict(steps=count, radial_current_integral=integral,
                              kato_transport_phase=float(np.angle(transport)),
                              error=float(abs(transport-np.exp(1j*integral))),
                              minimum_neighbor_overlap=overlap))
    assert loop_rows[-1]['error'] < 1e-9
    assert loop_rows[-1]['error'] < loop_rows[0]['error']/12
    # Along a radial ray J_rad(A)[A]=0. Its relative determinant phase is
    # therefore the integral of Im Tr(D^-1 dD P), where this test's D is invertible.
    # Independent direct rotations approximate the radial Kato basis.
    nodes, weights = np.polynomial.legendre.leggauss(8)
    phase_terms = []
    reference_phase, _ = np.linalg.slogdet(b0.conj().T@free['d']@w0)
    for name, q, multiplicity in SPECIES:
        integral = sum(weight/2*positive_current(model, np.exp(1j*(t+1)/2*theta), q, theta)
                       for t, weight in zip(nodes, weights))
        transport_rows = []
        for count in [32, 64, 128]:
            frame = w0.copy()
            for k in range(1, count+1):
                sp = model.operator(np.exp(1j*k/count*theta), q)
                factor, _ = inverse_sqrt(frame.conj().T@sp['p']@frame)
                frame = sp['p']@frame@factor
            phase, _ = np.linalg.slogdet(b0.conj().T@sp['d']@frame)
            relative = phase*reference_phase.conjugate()
            transport_rows.append(dict(steps=count, determinant_phase=float(np.angle(relative)),
                                       error=float(abs(relative-np.exp(1j*integral)))))
        assert transport_rows[-1]['error'] < 1e-10
        phase_terms.append(dict(species=name, charge=q, multiplicity=multiplicity,
                                radial_phase_integral=float(integral), transports=transport_rows))
    total = sum(row['multiplicity']*row['radial_phase_integral'] for row in phase_terms)
    assert abs(total) > 1e-9
    return dict(contractible_loop=loop_rows, radial_determinant_phase_terms=phase_terms,
                total_hypercharge_radial_determinant_phase=total,
                interpretation="nonconstant determinant phase retained on this ray; physical continuum equivalence is not established")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/radial_measure_phase_audit.json'))
    args = parser.parse_args()
    report = phase_checks()
    report['arithmetic'] = 'float64 quadrature and direct-rotation refinement; no interval certificate'
    root = Path(__file__).resolve().parents[1]
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [
        'UnifiedTheory/Audit/KFCausalRadialMeasure.lean', 'scripts/radial_measure_phase_audit.py',
        'scripts/radial_measure_audit.py', 'scripts/positive_measure_audit.py',
        'scripts/gauge_dressed_measure_audit.py', 'scripts/chiral_measure_audit.py',
        'scripts/overlap_chirality_audit.py']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
