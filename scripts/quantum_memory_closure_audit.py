#!/usr/bin/env python3
"""Exact sufficient-memory audit for a specified CNOT interaction.

The memory algebra is derived by closure, not selected by fitting outputs.
Adaptive measurement histories are compared with full joint evolution.
This is a finite model and does not derive spacetime, gravity, or matter.
"""
import argparse
import hashlib
import json
from pathlib import Path

import sympy as s
from quantum_refinement_audit import canonical, conjugate, marginal, same, tensor, unit, units

ID = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Z = s.diag(1, -1)
P0, P1 = s.diag(1, 0), s.diag(0, 1)
PP, PM = (ID+X)/2, (ID-X)/2
J = tensor(ID, X)
Q = s.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])


def reduce(rho):
    return canonical((rho+J*rho*J)/2)


def blocks(rho):
    return tuple(marginal(conjugate(tensor(ID, p), rho), 2, 2) for p in (PP, PM))


def encode(pair):
    return tensor(pair[0], PP)+tensor(pair[1], PM)


def flatten(a):
    return s.Matrix(list(a))


def independent_add(basis, candidate):
    candidate = canonical(candidate)
    cols = [flatten(a) for a in basis]
    if s.Matrix.hstack(*cols, flatten(candidate)).rank() > len(basis):
        basis.append(candidate)
        return True
    return False


def algebra_closure():
    basis = []
    for a in units(2):
        independent_add(basis, tensor(a, ID))
    seed_dimension = len(basis)
    for a in list(basis):
        independent_add(basis, Q.H*a*Q)
    one_time_dimension = len(basis)
    dimensions = [one_time_dimension]
    while True:
        old = list(basis)
        for a in old:
            independent_add(basis, a.H)
            independent_add(basis, Q.H*a*Q)
            for b in old:
                independent_add(basis, a*b)
        if len(basis) == len(old):
            break
        dimensions.append(len(basis))
    assert seed_dimension == 4 and one_time_dimension == 6 and len(basis) == 8
    space = s.Matrix.hstack(*[flatten(a) for a in basis])
    for a in basis:
        same(reduce(a), a)
    projection = s.Matrix.hstack(*[flatten(reduce(a)) for a in units(4)])
    assert projection.rank() == 8
    same(projection**2, projection)
    assert space.row_join(projection).rank() == 8
    # Center within the derived algebra: exactly the conserved binary record.
    columns = []
    for a in basis:
        column = []
        for b in basis:
            column.extend(a*b-b*a)
        columns.append(s.Matrix(column))
    center_dimension = len(basis)-s.Matrix.hstack(*columns).rank()
    assert center_dimension == 2
    assert space.row_join(flatten(J)).rank() == 8
    return dict(system_algebra_dimension=seed_dimension,
                one_time_observable_span_dimension=one_time_dimension,
                closure_dimensions=dimensions, closed_algebra_dimension=len(basis),
                projection_rank=projection.rank(), center_dimension=center_dimension)


def structural_checks():
    same(Q.H*Q, s.eye(4))
    same(Q*J, J*Q)
    same(J*J, s.eye(4))
    pplus, pminus = tensor(ID, PP), tensor(ID, PM)
    same(pplus.H*pplus+pminus.H*pminus, s.eye(4))
    same(tensor(X, ID)*(Q.H*tensor(X, ID)*Q), J)
    checks = 0
    ops = [Q]+[tensor(k, ID) for k in units(2)]
    for rho in units(4):
        same(reduce(rho), conjugate(pplus, rho)+conjugate(pminus, rho))
        same(encode(blocks(rho)), reduce(rho))
        same(marginal(reduce(rho), 2, 2), marginal(rho, 2, 2))
        assert reduce(rho).trace() == rho.trace()
        pair = blocks(rho)
        same(reduce(conjugate(Q, rho)), encode((pair[0], conjugate(Z, pair[1]))))
        for k in ops:
            same(reduce(conjugate(k, rho)), conjugate(k, reduce(rho)))
            checks += 1
    return dict(full_matrix_basis_inputs=16, commuting_branch_operators=len(ops),
                intertwining_checks=checks, conditional_block_update_checks=16)


def examples():
    plus = s.ones(2)/2
    bell = conjugate(Q, tensor(plus, P0))
    uncorrelated = tensor(ID/2, P0)
    # These states agree on the system AND on the bare record probabilities.
    same(marginal(bell, 2, 2), marginal(uncorrelated, 2, 2))
    for p in (PP, PM):
        assert (tensor(ID, p)*bell).trace() == (tensor(ID, p)*uncorrelated).trace() == s.Rational(1, 2)
    next_X = [(tensor(X, ID)*conjugate(Q, rho)).trace() for rho in (bell, uncorrelated)]
    assert next_X == [1, 0]
    # The exact retained memory survives the apparent first-step dephasing.
    pair = blocks(tensor(plus, P0))
    observations = []
    for step in range(7):
        observations.append(str((X*(pair[0]+pair[1])).trace()))
        pair = pair[0], conjugate(Z, pair[1])
    assert observations == ["1", "0", "1", "0", "1", "0", "1"]
    return dict(same_system_and_record_marginals_next_X=list(map(str, next_X)),
                record_probabilities=["1/2", "1/2"],
                retained_memory_X_history=observations)


def preparations():
    vectors = [s.Matrix([1, 0, 0, 0]), s.Matrix([0, 0, 0, 1]),
               s.Matrix([1, 0, 0, 1]), s.Matrix([1, 0, 0, s.I]),
               s.Matrix([1, 1, 1, 1]), s.Matrix([1, s.I, 1, -s.I])]
    states = [canonical(v*v.H/(v.H*v)[0]) for v in vectors]
    states.append(s.eye(4)/4)
    states.append(states[2]/3+2*states[0]/3)
    return states


def adaptive_histories(depth=5):
    rotation = s.Matrix([[s.Rational(3, 5), -s.Rational(4, 5)],
                         [s.Rational(4, 5), s.Rational(3, 5)]])
    instruments = [(P0, P1), (PP, PM), (P0*rotation, P1*rotation)]
    for instrument in instruments:
        same(sum((k.H*k for k in instrument), s.zeros(2)), ID)
    branch_checks = 0
    normalization_checks = 0
    nonzero_branches = 0
    for initial in preparations():
        assert initial.trace() == 1
        branches = [((), initial, blocks(initial))]
        for step in range(depth):
            next_branches = []
            for record, full, pair in branches:
                evolved = conjugate(Q, full)
                # Choose the next physical instrument using prior recorded outcomes.
                instrument = instruments[(sum(record)+step) % len(instruments)]
                for outcome, k in enumerate(instrument):
                    actual = conjugate(tensor(k, ID), evolved)
                    predicted = (conjugate(k, pair[0]), conjugate(k, conjugate(Z, pair[1])))
                    same(reduce(actual), encode(predicted))
                    same(marginal(actual, 2, 2), predicted[0]+predicted[1])
                    probability = actual.trace()
                    assert probability == (predicted[0]+predicted[1]).trace()
                    assert probability.is_real and probability >= 0
                    nonzero_branches += int(bool(probability > 0))
                    branch_checks += 1
                    next_branches.append((record+(outcome,), actual, predicted))
            branches = next_branches
            assert sum(full.trace() for _, full, _ in branches) == 1
            normalization_checks += 1
    return dict(initial_states=len(preparations()), max_interaction_rounds=depth,
                adaptive_instruments=len(instruments), branch_checks=branch_checks,
                nonzero_branches=int(nonzero_branches), normalized_trees=normalization_checks,
                arithmetic="unnormalized branch states; no conditioning on zero-probability events")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    algebra = algebra_closure()
    structure = structural_checks()
    witnesses = examples()
    histories = adaptive_histories()
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/quantum_memory_closure_audit.py", "scripts/quantum_refinement_audit.py",
             "UnifiedTheory/Audit/KFCausalQuantumMemoryClosure.lean",
             "UnifiedTheory/Audit/KFCausalQuantumRefinement.lean"]
    result = dict(scope="derived sufficient memory for specified finite CNOT dynamics; no TOE closure",
                  arithmetic="exact rational complex matrices", sympy_version=s.__version__,
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},
                  algebra=algebra, structural_checks=structure, counterexamples=witnesses,
                  adaptive_histories=histories)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    print("All exact closure, conditional-memory, and adaptive-history checks passed.")


if __name__ == "__main__":
    main()
