#!/usr/bin/env python3
"""Compare actual overlap fermions with continuum reference calculations.

Flat temporal holonomy is a nontrivial compact background with F=0. Its
vacuum-normalized weight has no field-dependent local curvature counterterm.
The continuum temporal product is evaluated first, leaving an exponentially
convergent spatial sum. Curved finite-lattice checks retain the complex phase.
These computations do not certify a general interacting continuum limit.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import time

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def continuum_toron(h: float, cutoff: int = 6) -> dict:
    """One Weyl fermion on a 2pi four-torus, AP time, A_time=h.

    The charge is incorporated into h. The answer is the real logarithm
    of the vacuum-normalized weight, not the negative effective action.
    """
    if abs(h) >= .5:
        raise ValueError("Use the invertible reference chart |h| < 1/2")
    theta = 2 * math.pi * h
    value, current = [], []
    for p in itertools.product(range(-cutoff, cutoff + 1), repeat=3):
        radius = math.sqrt(sum(n*n for n in p))
        e = math.exp(-2 * math.pi * radius)
        value.append(math.log1p(2*e*(math.cos(theta)-1)/(1+e)**2))
        current.append(-4*math.pi*e*math.sin(theta)/(1+2*e*math.cos(theta)+e*e))
    # There are (2k+1)^3-(2k-1)^3 = 24k^2+2 sites in max-norm shell k.
    # Euclidean radius >= k. Bound every omitted term and sum the geometric
    # k^2 series exactly. These are analytic truncation bounds; float rounding
    # in the displayed sums is separate and is not interval-certified.
    r, m = math.exp(-2*math.pi), cutoff + 1
    shell = r**m * (24*(m*m/(1-r)+2*m*r/(1-r)**2+r*(1+r)/(1-r)**3)+2/(1-r))
    denominator = (1-r**m)**2
    return dict(log_weight=math.fsum(value), current=math.fsum(current),
                spatial_cutoff=cutoff, log_tail_bound=4*shell/denominator,
                current_tail_bound=4*math.pi*shell/denominator)


def lattice_toron(n: int, h: float) -> dict:
    """Exact free overlap dispersion, the same mass-one kernel as the repo."""
    if n < 2 or n % 2:
        raise ValueError("An even lattice length >= 2 is required")
    a = 2*math.pi/n
    labels = np.arange(-n//2, n//2, dtype=float)
    spatial = a*labels
    c = 1-np.cos(spatial)
    s = np.sin(spatial)**2
    base = c[:, None, None]+c[None, :, None]+c[None, None, :]-1
    spatial_s = s[:, None, None]+s[None, :, None]+s[None, None, :]
    values, currents = [], []
    for label in labels + .5:
        t, t0 = a*(label-h), a*label
        b, b0 = base+1-math.cos(t), base+1-math.cos(t0)
        ss, ss0 = spatial_s+math.sin(t)**2, spatial_s+math.sin(t0)**2
        w, w0 = np.sqrt(b*b+ss), np.sqrt(b0*b0+ss0)
        # Avoid cancellation of w+b at small physical momenta.
        plus = np.where(b < 0, ss/(w-b), w+b)
        plus0 = np.where(b0 < 0, ss0/(w0-b0), w0+b0)
        logratio = np.log(plus/plus0)-np.log(w/w0)
        derivative = -a*math.sin(t)*(ss-b*math.cos(t))/(w*w*plus)
        values.append(float(np.sum(logratio, dtype=np.longdouble)))
        currents.append(float(np.sum(derivative, dtype=np.longdouble)))
    return dict(n=n, spacing=a, log_weight=math.fsum(values), current=math.fsum(currents))


def dense_operator_control() -> dict:
    """Check Fourier reduction against the existing full position-space D."""
    from radial_measure_audit import RectangularOverlap
    rows = []
    for n in (2, 4):
        model = RectangularOverlap((n,)*4)
        a, h = 2*math.pi/n, .13
        theta = np.zeros((4, model.n)); theta[3] = a*h
        direction = np.zeros_like(theta); direction[3] = a
        free = model.operator(np.ones_like(theta, dtype=complex), 1)
        actual = model.operator(np.exp(1j*theta), 1)
        _, log0 = np.linalg.slogdet(free['d'])
        _, log1 = np.linalg.slogdet(actual['d'])
        dp = model.projector_derivative(np.exp(1j*theta), 1, actual, direction)
        dd = 2*model.geom.g5@dp
        current = .5*np.trace(np.linalg.solve(actual['d'], dd))
        reduced = lattice_toron(n, h)
        errors = [abs(.5*(log1-log0)-reduced['log_weight']),
                  abs(current-reduced['current'])]
        assert max(errors) < 2e-9
        rows.append(dict(n=n, log_weight_error=errors[0], current_error=errors[1]))
    return dict(passed=True, rows=rows)


def complex_chirality_control() -> dict:
    """Independently build both chiral blocks on curved U(1) backgrounds."""
    from radial_measure_audit import RectangularOverlap
    from chiral_measure_audit import inverse_sqrt
    model = RectangularOverlap((2,)*4)
    free = model.operator(np.ones((4, model.n), dtype=complex), 1)
    starts = [free['vectors'][:, free['positive']], free['vectors'][:, ~free['positive']]]
    g5 = np.diag(model.geom.g5).real
    codomains = [model.eye[:, g5 > 0], model.eye[:, g5 < 0]]
    references = [np.linalg.slogdet(b.conj().T@free['d']@v)
                  for b, v in zip(codomains, starts)]
    rng = np.random.default_rng(261029019)
    rows = []
    for sample in range(4):
        theta = rng.uniform(-.018, .018, (4, model.n))
        data = model.operator(np.exp(1j*theta), 6)
        weights = []
        for p, v0, b, (ref_phase, ref_log) in zip(
                [data['p'], model.eye-data['p']], starts, codomains, references):
            factor, _ = inverse_sqrt(v0.conj().T@p@v0)
            v = p@v0@factor
            phase, logabs = np.linalg.slogdet(b.conj().T@data['d']@v)
            weights.append((phase*ref_phase.conjugate(), logabs-ref_log))
        minus, plus = weights
        phase_error = abs(plus[0]-minus[0].conjugate())
        modulus_error = abs(plus[1]-minus[1])
        assert max(phase_error, modulus_error) < 2e-10
        rows.append(dict(sample=sample, negative_chirality_phase=float(np.angle(minus[0])),
                         positive_chirality_phase=float(np.angle(plus[0])),
                         conjugation_error=float(phase_error), modulus_error=float(modulus_error),
                         kernel_gap=data['gap']))
    assert max(abs(row['negative_chirality_phase']) for row in rows) > 1e-8
    return dict(passed=True, rows=rows,
                scope='Direct-rotation finite-chart phases, not the completed cohomology measure or a continuum phase test.')


def toron_convergence(lengths: list[int], holonomies: list[float]) -> dict:
    rows = []
    for h in holonomies:
        continuum = continuum_toron(h)
        for n in lengths:
            lattice = lattice_toron(n, h)
            rows.append(dict(h=h, **lattice, continuum_log_weight=continuum['log_weight'],
                             continuum_current=continuum['current'],
                             log_error=abs(lattice['log_weight']-continuum['log_weight']),
                             current_error=abs(lattice['current']-continuum['current'])))
    return dict(rows=rows, reference_tail_bounds=continuum_toron(0),
                scope='Sampled flat-background refinement, not a uniform estimate over curved fields.')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'data/chiral_continuum_comparison.json')
    parser.add_argument('--lengths', type=int, nargs='+', default=[8, 12, 16, 24, 32, 48, 64])
    parser.add_argument('--holonomies', type=float, nargs='+', default=[.05, .13, .24])
    parser.add_argument('--skip-dense', action='store_true')
    args = parser.parse_args()
    started = time.time()
    report = dict(schema_version=1, source_paper='https://arxiv.org/abs/2610.29019v2',
                  physics_convention='ell=2pi; AP fourth/time direction; mass-one Wilson kernel; one Weyl species',
                  arithmetic='float64 with analytic continuum spatial-tail bounds; no interval rounding certificate',
                  complex_chirality=complex_chirality_control())
    if not args.skip_dense:
        report['position_space_cross_check'] = dense_operator_control()
    report['flat_holonomy'] = toron_convergence(args.lengths, args.holonomies)
    report['elapsed_seconds'] = time.time()-started
    sources = ['scripts/chiral_continuum_comparison.py', 'scripts/radial_measure_audit.py',
               'scripts/chiral_measure_audit.py', 'scripts/overlap_chirality_audit.py']
    report['source_sha256'] = {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
