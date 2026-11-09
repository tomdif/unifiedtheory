#!/usr/bin/env python3
"""Exact S3 quantum rotor/link dynamics and Gauss-law audit.

Two regular matter rotors and one quantum link: 216 total basis states,
six gauge-invariant states. This is a finite model, not chiral matter,
a continuous gauge-group limit, gravity, or a completed TOE.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import sympy as s


def clean(a):
    return s.SparseMatrix(a.applyfunc(s.expand))


def equal(a, b):
    d = clean(a-b)
    assert not d.todok(), "Exact matrix equality failed"


def norm2(v):
    return s.expand((v.H*v)[0])


def group_data():
    elements = list(itertools.permutations(range(3)))
    index = {p: i for i, p in enumerate(elements)}
    product = [[index[tuple(a[b[j]] for j in range(3))] for b in elements] for a in elements]
    identity = index[(0, 1, 2)]
    inverse = [next(j for j in range(6) if product[i][j] == identity) for i in range(6)]
    transpositions = [i for i, p in enumerate(elements) if sum(p[j] == j for j in range(3)) == 1]
    assert len(transpositions) == 3
    a, b = transpositions[:2]
    assert product[a][b] != product[b][a]
    return elements, product, inverse, identity, transpositions


def gauge_commutes(a, permutation):
    """Check G A G^-1 = A through a permutation of every nonzero entry."""
    entries = clean(a).todok()
    transformed = {(permutation[i], permutation[j]): v for (i, j), v in entries.items()}
    assert transformed == entries


def reduced_link_state(psi):
    amplitudes = s.Matrix(36, 6, lambda m, u: psi[6*m+u, 0])
    # Rows are the two matter registers, columns the link.
    return clean(amplitudes.T*amplitudes.conjugate()/norm2(psi))


def audit():
    elements, mul, inv, identity, transpositions = group_data()
    configs = list(itertools.product(range(6), repeat=3))  # left matter, right matter, link
    lookup = {c: i for i, c in enumerate(configs)}
    relative = [mul[mul[inv[l]][u]][r] for l, r, u in configs]
    dimension = len(configs)
    eye = s.SparseMatrix(s.eye(dimension))
    small_eye = s.SparseMatrix(s.eye(6))
    w = s.SparseMatrix(dimension, 6, {(i, relative[i]): s.Rational(1, 6) for i in range(dimension)})
    equal(w.H*w, small_eye)
    physical = clean(w*w.H)
    equal(physical*physical, physical)
    equal(physical.H, physical)
    assert physical.trace() == 6

    gauges = []
    average_entries = {}
    for h, k in itertools.product(range(6), repeat=2):
        permutation = [lookup[(mul[h][l], mul[k][r], mul[mul[h][u]][inv[k]])]
                       for l, r, u in configs]
        assert len(set(permutation)) == dimension
        assert all(relative[permutation[i]] == relative[i] for i in range(dimension))
        gauges.append(permutation)
        for source, dest in enumerate(permutation):
            average_entries[dest, source] = average_entries.get((dest, source), 0)+s.Rational(1, 36)
    equal(s.SparseMatrix(dimension, dimension, average_entries), physical)
    orbits = [{p[i] for p in gauges} for i in range(dimension)]
    for i in range(dimension):
        assert len(orbits[i]) == 36
        assert orbits[i] == {j for j in range(dimension) if relative[j] == relative[i]}

    # Central convolution by the S3 transposition conjugacy class.
    c_entries, small_c_entries = {}, {}
    for source, (l, r, u) in enumerate(configs):
        for tau in transpositions:
            c_entries[lookup[l, r, mul[tau][u]], source] = s.Rational(1, 3)
    for source in range(6):
        for tau in transpositions:
            small_c_entries[mul[tau][source], source] = s.Rational(1, 3)
    c = s.SparseMatrix(dimension, dimension, c_entries)
    cr = s.SparseMatrix(6, 6, small_c_entries)
    equal(c.H, c)
    equal(c*c*c, c)
    equal(cr*cr*cr, cr)
    electric = clean(eye-c*c-s.I*c)
    electric_r = clean(small_eye-cr*cr-s.I*cr)
    equal(electric.H*electric, eye)
    equal(electric*electric.H, eye)

    alignment = s.SparseMatrix(dimension, dimension,
                              {(i, i): 1 for i, r in enumerate(relative) if r == identity})
    alignment_r = s.SparseMatrix(6, 6, {(identity, identity): 1})
    interaction = clean(eye+(s.I-1)*alignment)
    interaction_r = clean(small_eye+(s.I-1)*alignment_r)
    full = clean(electric*interaction)
    reduced = clean(electric_r*interaction_r)
    equal(interaction.H*interaction, eye)
    equal(full.H*full, eye)
    equal(full*full.H, eye)
    equal(c*w, w*cr)
    equal(full*w, w*reduced)
    equal(w.H*full*w, reduced)
    equal(alignment*w, w*alignment_r)
    commutator = clean(c*alignment-alignment*c)
    assert commutator.todok()
    matter_mean = s.SparseMatrix(dimension, dimension,
        {(lookup[new_l, r, u], source): s.Rational(1, 6)
         for source, (l, r, u) in enumerate(configs) for new_l in range(6)})
    equal(matter_mean*electric, electric*matter_mean)
    for permutation in gauges:
        for operator in [c, interaction, full, matter_mean]:
            gauge_commutes(operator, permutation)

    sectors = [clean((cr*cr+cr)/2), clean((cr*cr-cr)/2), clean(small_eye-cr*cr)]
    for p in sectors:
        equal(p.H, p)
        equal(p*p, p)
    for j, p in enumerate(sectors):
        for q in sectors[j+1:]:
            equal(p*q, s.zeros(6))
    assert [p.trace() for p in sectors] == [1, 1, 4]
    for p, phase in zip(sectors, [-s.I, s.I, 1]):
        equal(electric_r*p, phase*p)

    # A physical product of uniform rotor/link states; work unnormalized
    # to keep all amplitudes Gaussian rational and divide every probability.
    phi = s.ones(6, 1)
    initial = clean(w*phi)
    after_interaction = clean(interaction*initial)
    after_step = clean(full*initial)
    assert norm2(initial) == norm2(after_interaction) == norm2(after_step) == 6
    link_before = reduced_link_state(initial)
    link_after = reduced_link_state(after_interaction)
    link_after_step = reduced_link_state(after_step)
    uniform_link = s.ones(6, 6)/6
    electric_before = s.expand((uniform_link*link_before).trace())
    electric_after = s.expand((uniform_link*link_after).trace())
    assert electric_before == 1 and electric_after == s.Rational(13, 18)
    purity_before = s.expand((link_before*link_before).trace())
    purity_after = s.expand((link_after*link_after).trace())
    assert purity_before == 1 and purity_after == s.Rational(29, 54)
    equal(link_after_step, link_after)
    align_before = s.expand((initial.H*alignment*initial)[0]/norm2(initial))
    align_after = s.expand((after_step.H*alignment*after_step)[0]/norm2(after_step))
    assert align_before == s.Rational(1, 6) and align_after == s.Rational(5, 54)
    sector_weights = [s.expand(((interaction_r*phi).H*p*(interaction_r*phi))[0]/6) for p in sectors]
    assert sector_weights == [s.Rational(13, 18), s.Rational(1, 18), s.Rational(2, 9)]
    # Field evolution affects a gauge-invariant matter observable at the
    # next interaction. The link-local gate alone cannot change that observable.
    feedback = clean(interaction*after_step)
    frozen = clean(interaction*after_interaction)
    matter_feedback = s.expand((feedback.H*matter_mean*feedback)[0]/norm2(feedback))
    matter_frozen = s.expand((frozen.H*matter_mean*frozen)[0]/norm2(frozen))
    assert matter_feedback == s.Rational(73, 81) and matter_frozen == s.Rational(4, 9)

    # A unitary but improperly undressed matter interaction violates Gauss.
    bad_interaction = s.SparseMatrix(s.diag(*[s.I if l == r else 1 for l, r, _ in configs]))
    equal(bad_interaction.H*bad_interaction, eye)
    bad_state = clean(bad_interaction*initial)
    leakage = s.expand(norm2(bad_state-physical*bad_state)/norm2(bad_state))
    assert leakage == s.Rational(5, 18)

    # Exact full-register/reduced comparison for every finite measurement
    # branch through five rounds. The same link register is reused.
    seeds = [small_eye[:, identity], small_eye[:, transpositions[0]], phi]
    full_outcomes = [alignment, eye-alignment]
    reduced_outcomes = [alignment_r, small_eye-alignment_r]
    histories, nonzero, normalization_trees = 0, 0, 0
    for seed in seeds:
        branches = [(clean(w*seed), clean(seed))]
        initial_norm = norm2(seed)
        for depth in range(5):
            next_branches = []
            total_weight = 0
            for full_state, reduced_state in branches:
                full_evolved = clean(full*full_state)
                reduced_evolved = clean(reduced*reduced_state)
                for p, pr in zip(full_outcomes, reduced_outcomes):
                    branch, branch_r = clean(p*full_evolved), clean(pr*reduced_evolved)
                    equal(branch, w*branch_r)
                    equal(physical*branch, branch)
                    weight = norm2(branch)
                    assert weight == norm2(branch_r)
                    histories += 1
                    nonzero += int(weight != 0)
                    total_weight += weight
                    next_branches.append((branch, branch_r))
            assert s.expand(total_weight) == initial_norm
            normalization_trees += 1
            branches = next_branches

    return dict(
        scope="specified finite S3 gauge theory with regular rotor matter; no chiral/continuum/GR closure",
        arithmetic="exact Gaussian-rational amplitudes and normalized rational probabilities",
        group=dict(name="S3", order=6, elements=elements, transposition_indices=transpositions,
                   noncommuting_witness=transpositions[:2], electric_sector_dimensions=[1, 1, 4]),
        hilbert_space=dict(matter_registers=2, quantum_link_registers=1, register_dimension=6,
                           total_dimension=dimension, physical_dimension=6, gauge_frames=36, orbit_size=36),
        exact_checks=dict(gauge_action_configuration_checks=36*dimension,
                          gauge_operator_commutation_checks=36*4,
                          gauss_projector_equals_group_average=True,
                          electric_cubic_identity=True, two_sided_step_unitarity=True,
                          physical_subspace_intertwining=True,
                          branch_comparisons=histories, nonzero_branches=nonzero,
                          rounds_per_initial_state=5, initial_states=3,
                          normalization_trees=normalization_trees),
        dynamics=dict(link_uniform_sector_before=str(electric_before),
                      link_uniform_sector_after_interaction=str(electric_after),
                      link_purity_before=str(purity_before), link_purity_after_interaction=str(purity_after),
                      relative_alignment_before=str(align_before), relative_alignment_after_step=str(align_after),
                      matter_uniform_sector_after_feedback=str(matter_feedback),
                      matter_uniform_sector_without_electric_step=str(matter_frozen),
                      electric_sector_weights_after_interaction=[str(v) for v in sector_weights],
                      undressed_unitary_gauss_leakage=str(leakage)),
        reduced_step=[[str(v) for v in reduced.row(i)] for i in range(6)],
        limitations=["Finite regular rotor matter is not a Weyl fermion or the Standard Model.",
                     "The one-edge audit contains no magnetic plaquette or spatial continuum limit.",
                     "Gauge group, graph, couplings, and gate order remain supplied.",
                     "The discrete step is unitary; conservation of a supplied continuous-time Hamiltonian is not asserted."])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = audit()
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/dynamical_gauge_audit.py", "UnifiedTheory/Audit/KFCausalDynamicalGauge.lean",
             "UnifiedTheory/Audit/KFCausalGaugeWalk.lean"]
    result["sympy_version"] = s.__version__
    result["source_sha256"] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    print("All exact dynamical-gauge checks passed within their stated scope.")


if __name__ == "__main__":
    main()
