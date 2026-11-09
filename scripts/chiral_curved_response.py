#!/usr/bin/env python3
"""Fifth-order complex response on an explicitly curved external U(1) field.

The field varies in coordinates 0 and 1. Coordinates 2 and 3 are Fourier
decomposed; coordinate 3 has antiperiodic fermions. Exact link integrals feed
the repository's mass-one Wilson/overlap operator. A Cauchy coefficient extracts
[t^4] d_t log W_+(t A), hence five times [t^5] log W_+(t A).

The continuum coefficient is Tr((D_0^+)^{-1} V^+)^5, computed as a sparse
Galerkin trace with symmetric momentum cutoffs. It is ultraviolet convergent;
finite cutoff differences here are diagnostics, not rigorous error bounds.
The overlap calculation uses the dynamical trace in a radial Kato frame.
The repository's completed cohomology phase is NOT included: convergence of
that correction remains a separate obligation for the full measure.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy import linalg, sparse

from overlap_chirality_audit import GAMMA, GAMMA5

ROOT = Path(__file__).resolve().parents[1]
PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], complex)
GAMMAS = np.array([np.array(g, complex) for g in GAMMA])
G5 = np.array(GAMMA5, complex)
# A_mu(x) = sum(c exp(i k.x) + conjugate(c exp(i k.x))).
TERMS = [(0, (1, 0), -.05j), (0, (1, 1), .02),
         (1, (0, 1), -.035j), (1, (2, -1), .015),
         (2, (1, 0), .045), (2, (1, 1), -.03j),
         (3, (0, 1), .04), (3, (2, -1), -.025j)]


def coefficient_record(value: complex) -> dict:
    return dict(current_t4_real=float(value.real), current_t4_imag=float(value.imag),
                log_weight_t5_real=float(value.real/5), log_weight_t5_imag=float(value.imag/5))


def continuum_fifth(cutoff: int) -> complex:
    """Symmetric spatial integers and symmetric temporal half-integers."""
    if cutoff < 1:
        raise ValueError('The momentum cutoff must be positive')
    labels = np.arange(-cutoff, cutoff+1)
    points = list(itertools.product(labels, repeat=2))
    index = {p:i for i, p in enumerate(points)}
    count = len(points)
    pieces = []
    for mu in range(4):
        rows, cols, values = [], [], []
        for component, k, c in TERMS:
            if mu != component:
                continue
            for freq, z in [(k, c), (tuple(-x for x in k), np.conj(c))]:
                for j, p in enumerate(points):
                    target = tuple(x+y for x, y in zip(p, freq))
                    if target in index:
                        rows.append(index[target]); cols.append(j); values.append(z)
        field = sparse.csr_matrix((values, (rows, cols)), shape=(count, count))
        spin = -1j*PAULI[mu] if mu < 3 else np.eye(2)
        pieces.append(sparse.kron(field, spin, format='csr'))
    vertex = sum(pieces)
    total = 0j
    for p2 in labels:
        for p3 in np.arange(-cutoff-1, cutoff+1)+.5:
            blocks = []
            for p0, p1 in points:
                d = 1j*(p0*PAULI[0]+p1*PAULI[1]+p2*PAULI[2])-p3*np.eye(2)
                blocks.append(np.linalg.inv(d))
            k = sparse.block_diag(blocks, format='csr')@vertex
            k2, k3 = k@k, (k@k)@k
            # Trace(K^2 K^3); ordinary transpose, not conjugate transpose.
            total += k2.multiply(k3.T).sum()
    return complex(total)


class BlockOverlap:
    def __init__(self, length: int):
        if length < 2 or length % 2:
            raise ValueError('Use an even lattice length >= 2')
        self.length = length
        self.spacing = a = 2*np.pi/length
        self.sites = sites = np.array(list(itertools.product(range(length), repeat=2)))
        self.count = count = length*length
        indices = {tuple(p):i for i, p in enumerate(sites)}
        theta = np.zeros((4, count), complex)
        for mu, k, c in TERMS:
            wave = np.exp(1j*a*(sites@np.array(k)))
            kmu = k[mu] if mu < 2 else 0
            integral = (1-np.exp(-1j*kmu*a))/(1j*kmu) if kmu else a
            term = c*integral*wave
            theta[mu] += term+np.conj(term)
        self.theta = theta.real
        self.previous = [np.array([indices[tuple((v-1) % length if i == mu else v
                                                 for i, v in enumerate(x))]
                                   for x in sites]) for mu in range(2)]
        self.g5 = np.kron(G5, np.eye(count))
        self.eye = np.eye(4*count)
        self.plus = [(np.eye(4)+g)/2 for g in GAMMAS]
        self.minus = [np.eye(4)-p for p in self.plus]

    def current(self, z: complex, k2: float, k3: float) -> complex:
        count = self.count
        w = 3*self.eye.astype(complex)
        dw = np.zeros_like(w)
        for mu in range(4):
            values = np.exp(1j*z*self.theta[mu])
            derivatives = 1j*self.theta[mu]
            if mu < 2:
                t = np.zeros((count, count), complex); ti = np.zeros_like(t)
                dt = np.zeros_like(t); dti = np.zeros_like(t)
                ix = np.arange(count)
                t[ix, self.previous[mu]] = values
                ti[self.previous[mu], ix] = 1/values
                dt[ix, self.previous[mu]] = derivatives*values
                dti[self.previous[mu], ix] = -derivatives/values
            else:
                values = values*np.exp(-1j*(k2 if mu == 2 else k3))
                t, ti = np.diag(values), np.diag(1/values)
                dt, dti = np.diag(derivatives*values), np.diag(-derivatives/values)
            w -= np.kron(self.plus[mu], t)+np.kron(self.minus[mu], ti)
            dw -= np.kron(self.plus[mu], dt)+np.kron(self.minus[mu], dti)
        h, dh = self.g5@w, self.g5@dw
        values, vectors = linalg.eig(h, check_finite=False)
        if np.min(abs(values.real)) < .1:
            raise ArithmeticError('Complex kernel too close to the sign-function cut')
        inverse = linalg.inv(vectors, check_finite=False)
        signs = np.where(values.real > 0, 1., -1.)
        divided = np.zeros((len(values), len(values)), complex)
        mask = signs[:, None] != signs[None, :]
        denominator = values[:, None]-values[None, :]
        numerator = signs[:, None]-signs[None, :]
        divided[mask] = numerator[mask]/denominator[mask]
        epsilon = (vectors*signs)@inverse
        depsilon = vectors@(divided*(inverse@dh@vectors))@inverse
        d, dd = self.eye+self.g5@epsilon, self.g5@depsilon
        response = linalg.solve(d.T, dd.T, check_finite=False).T
        # Codomain P_minus corresponds to the positive continuum Weyl domain.
        return complex(np.trace(response[2*count:, 2*count:]))

    def total_current(self, z: complex) -> complex:
        n, a = self.length, self.spacing
        return sum(self.current(z, a*n2, a*(n3+.5))
                   for n2 in range(-n//2, n-n//2) for n3 in range(-n//2, n-n//2))

    def fifth(self, angles: int = 12, radius: float = 1., jobs: int = 1) -> complex:
        if angles <= 4 or not np.isfinite(radius) or radius <= 0:
            raise ValueError('Use more than four angles and a finite positive radius')
        if jobs < 1:
            raise ValueError('The worker count must be positive')
        if jobs > 1:
            with ProcessPoolExecutor(max_workers=min(jobs, angles)) as pool:
                return sum(pool.map(_cauchy_angle,
                                    [(self.length, j, angles, radius) for j in range(angles)]))
        total = 0j
        for j in range(angles):
            phi = 2*np.pi*j/angles
            total += self.total_current(radius*np.exp(1j*phi))*np.exp(-4j*phi)/angles/radius**4
        return total


def _cauchy_angle(arguments: tuple[int, int, int, float]) -> complex:
    n, j, angles, radius = arguments
    phi = 2*np.pi*j/angles
    return (BlockOverlap(n).total_current(radius*np.exp(1j*phi))
            * np.exp(-4j*phi)/angles/radius**4)


def position_space_check() -> dict:
    """Independent full 4D matrix against the partial Fourier calculation."""
    from radial_measure_audit import RectangularOverlap
    n, amplitude = 2, .4
    block, full = BlockOverlap(n), RectangularOverlap((n,)*4)
    index = {tuple(x):i for i, x in enumerate(block.sites)}
    theta = np.array([block.theta[:, index[tuple(x[:2])]] for x in full.geom.sites]).T
    links = np.exp(1j*amplitude*theta)
    spectrum = full.operator(links, 1)
    dp = full.projector_derivative(links, 1, spectrum, theta)
    dd = 2*full.geom.g5@dp
    response = np.linalg.solve(spectrum['d'].T, dd.T).T
    dense = np.trace(response[2*full.n:, 2*full.n:])
    reduced = block.total_current(amplitude)
    error = abs(dense-reduced)
    assert error < 2e-10
    return dict(passed=True, amplitude=amplitude, current_error=float(error),
                dense_current_real=float(dense.real), dense_current_imag=float(dense.imag))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lengths', nargs='*', type=int, default=[4, 6, 8])
    parser.add_argument('--cutoffs', nargs='*', type=int, default=[4, 8, 12, 16])
    parser.add_argument('--angles', type=int, default=12)
    parser.add_argument('--radius', type=float, default=1.)
    parser.add_argument('--jobs', type=int, default=1,
                        help='Independent Cauchy-angle workers; use one BLAS thread per worker')
    parser.add_argument('--output', type=Path, default=ROOT/'data/chiral_curved_response.json')
    args = parser.parse_args()
    if not args.lengths and not args.cutoffs:
        parser.error('Supply at least one lattice length or momentum cutoff')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = dict(schema_version=1, source_paper='https://arxiv.org/abs/2610.29019v2',
                  coefficient='[t^4] d_t log W_+(tA) = 5 [t^5] log W_+(tA)',
                  spacing='ell=2pi, a=2pi/N, antiperiodic fourth/time direction',
                  fourier_terms=[dict(component=mu, frequency=k, real=float(complex(c).real),
                                      imag=float(complex(c).imag)) for mu, k, c in TERMS],
                  supplied_generation_fifth_charge_moment=4320,
                  completed_measure_phase_included=False,
                  uniform_continuum_comparison_proved=False,
                  position_space_control=position_space_check(), continuum=[], overlap=[])
    sources = ['scripts/chiral_curved_response.py', 'scripts/overlap_chirality_audit.py',
               'scripts/radial_measure_audit.py']
    report['source_sha256'] = {p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}
    for cutoff in args.cutoffs:
        started = time.time()
        row = dict(cutoff=cutoff, **coefficient_record(continuum_fifth(cutoff)),
                   seconds=time.time()-started)
        report['continuum'].append(row); print(json.dumps(row), flush=True)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    for n in args.lengths:
        started = time.time()
        row = dict(n=n, angles=args.angles, radius=args.radius, jobs=args.jobs,
                   **coefficient_record(BlockOverlap(n).fifth(args.angles, args.radius, args.jobs)),
                   seconds=time.time()-started)
        report['overlap'].append(row); print(json.dumps(row), flush=True)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
