#!/usr/bin/env python3
"""Search the existing finite models for an occupation/energy spectral bridge.

Exact SymPy calculations and floating-point probes are reported separately.
Lean supplies the basis-independent obstruction in KFCausalOccupationSpectralSearch.
This script does not certify a continuum limit or a quantum normal-form theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from constraint_reduced_spin_model import ConstraintReducedSpinModel, Parameters


def exact_capacity_one():
    eye = sy.eye(7)
    ladders = []
    for a in range(6):
        matrix = sy.zeros(7)
        matrix[0, a + 1] = 1
        ladders.append(matrix)
    clock = ladders[0] + ladders[0].H
    half = eye + clock / 2 + clock * clock / 8
    inverse_half = eye - clock / 2 + clock * clock / 8
    skew = lambda a: ladders[a] - ladders[a].H
    momentum = -sy.I * (skew(1) + skew(2))
    matter_momentum = -sy.I * (skew(3) + skew(4) + skew(5))
    gradient = -sy.I * (skew(1) - skew(2))
    matter_gradient = -sy.I * (skew(3) - skew(4))
    gram = lambda a: a.H * a
    static = (gram(half) + gram(momentum * inverse_half)
              + gram(matter_momentum * inverse_half)) / 2
    growing = (gram(gradient * inverse_half) + gram(matter_gradient * inverse_half)) / 2
    neutral = [0, 1, 6]
    block = (static + growing).extract(neutral, neutral)
    expected = sy.Matrix([[sy.Rational(413, 64), -sy.Rational(63, 32), 0],
                          [-sy.Rational(63, 32), sy.Rational(241, 128), 0], [0, 0, 1]])
    assert block == expected
    eigenvalues = sorted(block.eigenvals(), key=float)
    assert len(eigenvalues) == 3
    assert all(multiplicity == 1 for multiplicity in block.eigenvals().values())
    a, b = sy.symbols('a b')
    assert sy.solve(list(block * block - a * block - b * sy.eye(3)), [a, b]) == []
    return dict(matrix=[[str(x) for x in row] for row in block.tolist()],
                eigenvalues=[str(x) for x in eigenvalues],
                eigenvalues_numeric=[float(x) for x in eigenvalues],
                multiplicities=[1, 1, 1],
                occupation_multiplicities=[1, 2],
                no_affine_idempotent_similarity=True,
                static_growing_commutator=[[str(x) for x in row] for row in
                    (static * growing - growing * static).extract(neutral, neutral).tolist()])


def numerical_case(capacity, order, time):
    params = Parameters(R=capacity, hbar=2, correction='exact', mass2=0,
                        quartic=0, vacuum=0, flavors=6, functional_order=order)
    model = ConstraintReducedSpinModel(params)
    index = model.physical
    matrix = model.matrix(time, physical=True)
    total = model.number[index]
    charged = model.states[index, 1:5].sum(axis=1)
    scale = max(float(la.norm(matrix)), 1.)
    commutator = lambda grade: float(la.norm((grade[:, None] - grade[None, :]) * matrix) / scale)
    occupation_defect = commutator(total)
    charged_defect = commutator(charged)
    assert la.norm(matrix - matrix.conj().T) / scale < 1e-12
    assert occupation_defect > 1e-3
    if time == 0:
        assert charged_defect < 1e-12
    elif capacity >= 2:
        assert charged_defect > 1e-3
    values = la.eigvalsh(matrix)
    if capacity == 1 and order == 2 and time == 0:
        assert np.allclose(values, exact_capacity_one()['eigenvalues_numeric'], atol=1e-12)
    return dict(capacity=capacity, functional_order=order, time=time,
                neutral_dimension=len(index), eigenvalues=values.tolist(),
                relative_total_occupation_commutator=occupation_defect,
                relative_charged_occupation_commutator=charged_defect,
                evidence='floating-point finite-model probe; not a universal theorem')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('data/occupation_spectral_search.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    paths = ['scripts/occupation_spectral_search.py', 'scripts/constraint_reduced_spin_model.py',
             'scripts/quantum_areal_spin_model.py', 'scripts/holomorphic_tensor_phase_audit.py']
    report = dict(exact_capacity_one=exact_capacity_one(),
                  parameters=dict(hbar=2, correction='exact', mass2=0, quartic=0, vacuum=0),
                  numerical_cases=[numerical_case(r, order, t)
                                   for r in (1, 2, 3) for order in (2, None) for t in (0., .25)],
                  candidate='Free, fixed-clock charged oscillator sector after canonical squeezing.',
                  remaining_obligations=[
                      'Intertwine the actual closed quantum Hamiltonian and its domains with the normal form.',
                      'Construct the complete neutral Hermite basis and its charged energy degeneracies.',
                      'Handle continuous clock and homogeneous momentum variables; establish a suitable trace.',
                      'Control mass/quartic/vacuum terms and the extra generator of a time-dependent squeeze.'],
                  source_sha256={p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths})
    target = root / args.output
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Exact capacity-one spectrum and {len(report["numerical_cases"])} finite probes passed: {target}')


if __name__ == '__main__':
    main()
