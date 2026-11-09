#!/usr/bin/env python3
"""Audit a supplied local Weyl-walk law, including its unwanted mirror cone.

Symbolic equalities and Gaussian-rational stencil checks are exact.
Continuum convergence checks use floating point and are labeled separately.
This is a free-field benchmark on a chosen lattice, not a completed TOE.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as s

I2 = s.eye(2)
PAULI = (s.Matrix([[0, 1], [1, 0]]),
         s.Matrix([[0, -s.I], [s.I, 0]]), s.diag(1, -1))
X, Y, Z = PAULI
MOMENTA = s.symbols("x y z", real=True)


def equal(a, b):
    difference = a-b
    assert all(s.trigsimp(s.expand_complex(v)) == 0 for v in difference), difference


def rotations(q):
    return [s.cos(k)*I2-s.I*s.sin(k)*p for k, p in zip(q, PAULI)]


def walk(q):
    rx, ry, rz = rotations(q)
    return rz*ry*rx


def coefficients(q):
    cx, cy, cz = [s.cos(k) for k in q]
    sx, sy, sz = [s.sin(k) for k in q]
    return cx*cy*cz+sx*sy*sz, s.Matrix([
        sx*cy*cz-cx*sy*sz, cx*sy*cz+sx*cy*sz, cx*cy*sz-sx*sy*cz])


def symbolic_checks():
    x, y, z = MOMENTA
    a = s.symbols("a", real=True)
    u = walk(MOMENTA)
    d, v = coefficients(MOMENTA)
    h = x*X+y*Y+z*Z
    for r in rotations(MOMENTA):
        equal(r.H*r, I2)
    equal(u, d*I2-s.I*sum((v[j]*p for j, p in enumerate(PAULI)), s.zeros(2)))
    equal(h*h, (x*x+y*y+z*z)*I2)
    equal(s.diff(walk([a*k for k in MOMENTA]), a).subs(a, 0), -s.I*h)
    equal(walk([k+s.pi/2 for k in MOMENTA]), walk([x, -y, z]))
    equal(s.diff(walk([a*k+s.pi/2 for k in MOMENTA]), a).subs(a, 0),
          -s.I*(x*X-y*Y+z*Z))
    reverse = rotations([a*k for k in MOMENTA])
    equal(s.diff(reverse[0]*reverse[1]*reverse[2], a).subs(a, 0), -s.I*h)
    assert s.trigsimp(d*d+(v.T*v)[0]) == 1
    # The update-order freedom changes an actual Born probability, not
    # just an unobservable global phase of the unitary matrix.
    q_witness = (s.pi/4, s.pi/4, 0)
    forward = walk(q_witness)
    rx, ry, rz = rotations(q_witness)
    backward = rx*ry*rz
    rho_plus_x, measure_zero = s.ones(2)/2, s.diag(1, 0)
    probabilities = [s.simplify((measure_zero*u*rho_plus_x*u.H).trace())
                     for u in (forward, backward)]
    assert probabilities == [0, s.Rational(1, 2)]
    # Reversal alone is related to a simultaneous spatial/spin rotation.
    # Check that equivalence and provide a stronger, rotation-invariant
    # discriminator in the broader class of finite-range unitary laws.
    hadamard = (X+Z)/s.sqrt(2)
    equal(hadamard*walk([z, -y, x])*hadamard,
          rotations(MOMENTA)[0]*rotations(MOMENTA)[1]*rotations(MOMENTA)[2])
    ax, ay, _ = rotations([a*k for k in MOMENTA])
    loop_a = ay*ax*ay.H*ax.H
    equal(loop_a.subs(a, 0), I2)
    equal(s.diff(loop_a, a).subs(a, 0), s.zeros(2))
    modified = ry*rx*ry.H*rx.H*forward
    modified_trace = s.simplify(modified.trace())
    assert modified_trace == 0
    rotation_checks = 0
    for permutation in itertools.permutations(q_witness):
        for signs in itertools.product((-1, 1), repeat=3):
            q_rotated = [sign*k for sign, k in zip(signs, permutation)]
            assert s.simplify(walk(q_rotated).trace()) == 1
            rotation_checks += 1
    return dict(axis_unitarity_checks=3, explicit_symbol=True,
                weyl_generator=True, hamiltonian_square=True,
                exact_mirror_identity=True, opposite_mirror_generator=True,
                reversed_order_has_same_generator=True,
                reversed_order_zero_outcome_probabilities=list(map(str, probabilities)),
                reversal_is_coordinate_and_spin_equivalent=True,
                commutator_loop_zero_generator=True,
                modified_law_trace_witness=str(modified_trace),
                original_trace_under_signed_axis_permutations="1",
                signed_axis_permutation_checks=rotation_checks,
                quaternion_normalization=True)


def stencil_checks():
    stencil = {}
    for signs in itertools.product((-1, 1), repeat=3):
        ps = [(I2+sign*p)/2 for sign, p in zip(signs, PAULI)]
        stencil[signs] = ps[2]*ps[1]*ps[0]
    checks = 0
    for shift in itertools.product((-2, 0, 2), repeat=3):
        right, left = s.zeros(2), s.zeros(2)
        for d, matrix in stencil.items():
            other = tuple(d[j]+shift[j] for j in range(3))
            if other in stencil:
                right += matrix.H*stencil[other]
                left += matrix*stencil[other].H
        target = I2 if shift == (0, 0, 0) else s.zeros(2)
        equal(right, target)
        equal(left, target)
        checks += 2
    # Fourier transform of the actual position-space stencil.
    symbol = s.zeros(2)
    for signs, matrix in stencil.items():
        phase = s.prod(s.cos(k)-s.I*sign*s.sin(k)
                       for sign, k in zip(signs, MOMENTA))
        symbol += matrix*phase
    equal(symbol, walk(MOMENTA))
    assert all(any(v != 0 for v in matrix) for matrix in stencil.values())
    return dict(nonzero_displacements=len(stencil), max_coordinate_displacement=1,
                exact_unitarity_correlation_checks=checks,
                stencil_fourier_symbol_matches=True,
                coefficients={str(d): [[str(v) for v in matrix.row(j)] for j in range(2)]
                              for d, matrix in stencil.items()})


def node_checks():
    _, vector = coefficients(MOMENTA)
    jacobian = vector.jacobian(MOMENTA)
    nodes = []
    representatives = {}
    reciprocal_shifts = [(0, 0, 0), (2, 2, 0), (2, 0, 2), (0, 2, 2)]
    for grid in itertools.product((-2, -1, 0, 1), repeat=3):
        q = [s.pi*g/2 for g in grid]
        d, v = coefficients(q)
        if v != s.zeros(3, 1):
            continue
        assert d in (-1, 1)
        equal(walk(q), d*I2)
        # Factor out the central step sign before defining the local generator.
        velocity = d*jacobian.subs(dict(zip(MOMENTA, q)))
        chirality = int(velocity.det())
        assert chirality in (-1, 1)
        representative = min(tuple((grid[j]+shift[j]+2) % 4-2 for j in range(3))
                             for shift in reciprocal_shifts)
        key = str(representative)
        item = dict(momentum_over_pi=[str(s.Rational(g, 2)) for g in grid],
                    step_sign=int(d), quasienergy="0" if d == 1 else "pi",
                    relative_velocity=[[str(v) for v in velocity.row(j)] for j in range(3)],
                    chirality=chirality, bcc_class=key)
        nodes.append(item)
        representatives.setdefault(key, []).append(item)
    assert len(nodes) == 16 and len(representatives) == 4
    summary = []
    for key, members in representatives.items():
        assert len(members) == 4
        assert len({(m["step_sign"], m["chirality"]) for m in members}) == 1
        summary.append(dict(representative=key, cube_copies=4,
                            quasienergy=members[0]["quasienergy"],
                            chirality=members[0]["chirality"]))
    for energy in ("0", "pi"):
        assert sum(n["chirality"] for n in nodes if n["quasienergy"] == energy) == 0
        assert sum(n["chirality"] for n in summary if n["quasienergy"] == energy) == 0
    return dict(cube_nodes=nodes, inequivalent_bcc_nodes=summary,
                cube_node_count=16, single_bcc_sector_node_count=4,
                chirality_sum_at_each_quasienergy=0,
                completeness="analytic classification in WEYL_WALK_CONTINUUM.md; grid verifies its candidates")


NP_PAULI = [np.array(p, dtype=complex) for p in PAULI]


def numeric_walk(q, reverse=False):
    result = np.eye(2, dtype=complex)
    rotations_np = [np.cos(k)*np.eye(2)-1j*np.sin(k)*p for k, p in zip(q, NP_PAULI)]
    for r in (reversed(rotations_np) if reverse else rotations_np):
        result = r@result
    return result


def continuum_checks():
    momenta = [(1., 0., 0.), (0.2, -0.3, 0.4), (1., 1., 1.),
               (-0.7, 0.4, 0.9), (2., -1., 0.5)]
    rows = []
    for k in momenta:
        h = sum((q*p for q, p in zip(k, NP_PAULI)), np.zeros((2, 2), complex))
        radius = np.linalg.norm(k)
        for t in (0.25, 1., 2.):
            exact = np.cos(t*radius)*np.eye(2)-1j*np.sin(t*radius)*h/radius
            for n in (4, 8, 16, 32, 64, 128, 256):
                actual = np.linalg.matrix_power(numeric_walk(np.array(k)*t/n), n)
                error = float(np.linalg.norm(actual-exact, ord=2))
                bound = t*t*sum(abs(q) for q in k)**2/n
                assert error <= bound+2e-12
                rows.append(dict(momentum=list(k), time=t, steps=n,
                                 operator_norm_error=error, analytic_upper_bound=bound))
    q = np.array((0.2, 0.3, 0.4))
    order_difference = float(np.linalg.norm(numeric_walk(q)-numeric_walk(q, reverse=True), ord=2))
    assert order_difference > 0.1
    return dict(arithmetic="complex128 numerical checks; analytic uniform bound proved in note",
                checked_cases=len(rows), results=rows,
                same_continuum_different_update_order_norm_difference=order_difference,
                maximum_error_bound_ratio=max(r["operator_norm_error"]/r["analytic_upper_bound"] for r in rows))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = dict(scope="specified three-dimensional free quantum walk; Weyl limit plus mirror species",
                  sympy_version=s.__version__, numpy_version=np.__version__,
                  symbolic=symbolic_checks(), position_stencil=stencil_checks(),
                  spectrum=node_checks(), continuum_numerical=continuum_checks())
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/weyl_walk_audit.py", "UnifiedTheory/Audit/KFCausalWeylWalk.lean"]
    result["source_sha256"] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("position_stencil", "spectrum", "continuum_numerical")}, indent=2))
    print("Exact stencil checks:", result["position_stencil"]["exact_unitarity_correlation_checks"])
    print("Inequivalent BCC nodes:", result["spectrum"]["single_bcc_sector_node_count"])
    print("Numerical continuum checks:", result["continuum_numerical"]["checked_cases"])
    print("All exact and numerical checks passed within their stated scope.")


if __name__ == "__main__":
    main()
