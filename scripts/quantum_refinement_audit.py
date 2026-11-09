#!/usr/bin/env python3
"""Exact finite audit of quantum refinement and its autonomy boundary.

These are tensor-system models and counterexamples, not a spacetime or TOE.
All matrix arithmetic uses SymPy exact rationals and Gaussian rationals.
"""
import argparse
import hashlib
import json
from pathlib import Path

import sympy as s


def canonical(a):
    return a.applyfunc(s.expand)


def same(a, b):
    assert canonical(a-b) == s.zeros(*a.shape)


def unit(n, i, j):
    a = s.zeros(n)
    a[i, j] = 1
    return a


def units(n):
    return [unit(n, i, j) for i in range(n) for j in range(n)]


def tensor(a, b):
    return canonical(s.kronecker_product(a, b))


def conjugate(u, a):
    return canonical(u*a*u.H)


def marginal(a, retained, discarded):
    return s.Matrix(retained, retained, lambda i, j:
                    sum(a[i*discarded+k, j*discarded+k] for k in range(discarded)))


def unitary(n, choice):
    phase = s.diag(*[s.I**j for j in range(n)])
    rotation = s.eye(n)
    rotation[:2, :2] = s.Matrix([[s.Rational(3, 5), -s.Rational(4, 5)],
                                [s.Rational(4, 5), s.Rational(3, 5)]])
    u = phase if choice == 0 else phase*rotation
    same(u.H*u, s.eye(n))
    return canonical(u)


def product_audit():
    result = []
    for retained, discarded in ((2, 2), (2, 3), (3, 2), (3, 3)):
        operator_checks = state_checks = 0
        for uc in range(2):
            for wc in range(2):
                u, w = unitary(retained, uc), unitary(discarded, wc)
                q = tensor(u, w)
                same(q.H*q, s.eye(retained*discarded))
                for a in units(retained):
                    lift = tensor(a, s.eye(discarded))
                    same(q.H*lift*q, tensor(u.H*a*u, s.eye(discarded)))
                    operator_checks += 1
                for rho in units(retained*discarded):
                    same(marginal(conjugate(q, rho), retained, discarded),
                         conjugate(u, marginal(rho, retained, discarded)))
                    state_checks += 1
                for step in range(5):
                    same(q**step, tensor(u**step, w**step))
        # Independent linear-system computation of the full commutant dimension.
        lifts = [tensor(a, s.eye(discarded)) for a in units(retained)]
        basis = units(retained*discarded)
        columns = []
        for t in basis:
            column = []
            for a in lifts:
                column.extend(a*t-t*a)
            columns.append(s.Matrix(column))
        constraints = s.Matrix.hstack(*columns)
        nullity = len(basis)-constraints.rank()
        assert nullity == discarded**2
        result.append(dict(retained=retained, discarded=discarded,
                           unitary_pairs=4, observable_basis_checks=operator_checks,
                           full_matrix_input_checks=state_checks,
                           commutant_dimension=nullity))
    return result


def witnesses():
    zero = s.diag(1, 0)
    plus = s.ones(2)/2
    mixed = s.eye(2)/2
    x = s.Matrix([[0, 1], [1, 0]])
    phase = s.diag(1, s.I)
    cnot = s.Matrix([[1, 0, 0, 0], [0, 1, 0, 0],
                     [0, 0, 0, 1], [0, 0, 1, 0]])
    same(cnot.H*cnot, s.eye(4))
    # Two admitted unitary laws make opposite predictions for the same experiment.
    predictions = [(zero*conjugate(u, zero)).trace() for u in (phase, x)]
    assert predictions == [1, 0]
    # Same retained input, different discarded preparations, different future.
    input_zero, input_plus = tensor(plus, zero), tensor(plus, plus)
    same(marginal(input_zero, 2, 2), marginal(input_plus, 2, 2))
    out_zero = marginal(conjugate(cnot, input_zero), 2, 2)
    out_plus = marginal(conjugate(cnot, input_plus), 2, 2)
    same(out_zero, mixed)
    same(out_plus, plus)
    assert [(x*a).trace() for a in (out_zero, out_plus)] == [0, 1]
    # On the explicit product preparation, one step is a complete dephasing channel.
    dephase = lambda rho: sum((p*rho*p for p in (zero, s.eye(2)-zero)), s.zeros(2))
    for a in units(2):
        same(marginal(conjugate(cnot, tensor(a, zero)), 2, 2), dephase(a))
    # Reusing the same environment retains memory; iterating the reduced map is wrong.
    actual_two_steps = marginal(conjugate(cnot**2, input_zero), 2, 2)
    markov_two_steps = dephase(dephase(plus))
    same(actual_two_steps, plus)
    same(markov_two_steps, mixed)
    # Entangling encoding and decoding preserve the whole logical qubit.
    encoded = conjugate(cnot, input_zero)
    same(encoded, s.Matrix([[1, 0, 0, 1], [0, 0, 0, 0],
                            [0, 0, 0, 0], [1, 0, 0, 1]])/2)
    decode = lambda a: marginal(conjugate(cnot.H, a), 2, 2)
    same(decode(encoded), plus)
    u, w = unitary(2, 1), s.diag(1, -1)
    fine_evolution = conjugate(cnot, tensor(u, w))
    for rho in units(4):
        same(decode(conjugate(fine_evolution, rho)), conjugate(u, decode(rho)))
    return dict(admitted_laws_same_experiment_probabilities=list(map(str, predictions)),
                environment_dependence_X_expectations=["0", "1"],
                actual_two_step_X="1", reduced_map_iterated_X="0",
                encoded_state="Bell pair", decoded_purity=str((decode(encoded)**2).trace()),
                ordinary_marginal_purity=str((marginal(encoded, 2, 2)**2).trace()),
                encoded_autonomy_full_matrix_checks=16)


def finite_tower():
    """Consistency certificates for an explicit normalized positive product-state tower."""
    logical = s.Matrix([[s.Rational(1, 2), s.I/2], [-s.I/2, s.Rational(1, 2)]])
    ancilla = s.diag(1, 0)
    state = logical
    rows = []
    for depth in range(5):
        same(state*state, state)
        same(state.H, state)
        assert state.trace() == 1
        if depth < 4:
            fine = tensor(state, ancilla)
            same(marginal(fine, state.rows, 2), state)
        rows.append(dict(depth=depth, dimension=state.rows, trace="1", purity="1"))
        state = tensor(state, ancilla)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = product_audit()
    counterexamples = witnesses()
    tower = finite_tower()
    root = Path(__file__).resolve().parent.parent
    sources = ["scripts/quantum_refinement_audit.py",
               "UnifiedTheory/Audit/KFCausalQuantumRefinement.lean",
               "UnifiedTheory/LayerB/PartialTrace.lean"]
    result = dict(scope="finite quantum refinement and underdetermination; no TOE or spacetime derivation",
                  arithmetic="exact symbolic rational complex matrices", sympy_version=s.__version__,
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources},
                  product_models=rows, counterexamples=counterexamples, finite_tower=tower)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(rows, indent=2))
    print(json.dumps(counterexamples, indent=2))
    print("All exact checks passed; infinite observable-algebra extension is analytic in the proof note.")


if __name__ == "__main__":
    main()
