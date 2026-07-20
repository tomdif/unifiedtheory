#!/usr/bin/env python3
"""Local generalization audit for the complete chiral causal-growth law.

This mirrors the signature law formalized in
`UnifiedTheory/Audit/KFCausalSetCompleteChiralLaw.lean`:

    A_lambda(omega, m) = lambda^(omega * (omega - 1)) (sign * i)^m.

The script is not part of the proof.  It is a reproducible finite stress test
of the proved all-rank law.  It

* exhausts one representative of every unlabeled finite poset through rank 6;
* checks exact signature identities and both chiralities;
* tests canonical, shifted, sparse, transcendental-running, rational-critical,
  and harmonic multiplicity-corrected couplings;
* audits positivity and absolute-value unimodality of the real parent-polynomial
  coefficients;
* samples higher-rank naturally labelled posets through rank 12;
* tests structured chain/antichain/two-layer families through rank 16; and
* scans the harmonic antichain sector ratio and conditioning through rank 200;
* reproduces the old C8-below-A6 zero before testing the interacting repair.

Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import time
from collections import defaultdict
from dataclasses import asdict, dataclass
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Iterable, Iterator


getcontext().prec = 90


Relation = tuple[int, ...]  # successor bit masks for a strict finite order


@dataclass
class CouplingMetrics:
    parents: int = 0
    precursor_slots: int = 0
    zero_partitions: int = 0
    min_partition_abs: Decimal | None = None
    max_partition_condition: Decimal = Decimal(0)
    max_born_concentration: Decimal = Decimal(0)
    min_born_effective_slots: Decimal | None = None
    min_timid_born_share: Decimal | None = None
    max_timid_born_share: Decimal = Decimal(0)
    sum_timid_born_share: Decimal = Decimal(0)
    min_timid_quantum_measure: Decimal | None = None
    max_timid_quantum_measure: Decimal = Decimal(0)
    sum_timid_quantum_measure: Decimal = Decimal(0)
    max_normalization_error: Decimal = Decimal(0)

    def observe(
        self,
        partition_abs: Decimal,
        condition: Decimal,
        born_concentration: Decimal,
        born_effective_slots: Decimal,
        timid_born_share: Decimal,
        timid_quantum_measure: Decimal,
        normalization_error: Decimal,
        slots: int,
    ) -> None:
        self.parents += 1
        self.precursor_slots += slots
        if partition_abs == 0:
            self.zero_partitions += 1
        if self.min_partition_abs is None or partition_abs < self.min_partition_abs:
            self.min_partition_abs = partition_abs
        self.max_partition_condition = max(self.max_partition_condition, condition)
        self.max_born_concentration = max(
            self.max_born_concentration, born_concentration
        )
        if (
            self.min_born_effective_slots is None
            or born_effective_slots < self.min_born_effective_slots
        ):
            self.min_born_effective_slots = born_effective_slots
        self.max_timid_born_share = max(
            self.max_timid_born_share, timid_born_share
        )
        if (
            self.min_timid_born_share is None
            or timid_born_share < self.min_timid_born_share
        ):
            self.min_timid_born_share = timid_born_share
        self.sum_timid_born_share += timid_born_share
        self.max_timid_quantum_measure = max(
            self.max_timid_quantum_measure, timid_quantum_measure
        )
        if (
            self.min_timid_quantum_measure is None
            or timid_quantum_measure < self.min_timid_quantum_measure
        ):
            self.min_timid_quantum_measure = timid_quantum_measure
        self.sum_timid_quantum_measure += timid_quantum_measure
        self.max_normalization_error = max(
            self.max_normalization_error, normalization_error
        )


def decimal_json(value: object) -> object:
    if isinstance(value, Decimal):
        return format(value, ".18E")
    if isinstance(value, dict):
        return {key: decimal_json(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [decimal_json(item) for item in value]
    return value


def liouville_number(base: int = 2) -> Decimal:
    """Mathlib's `liouvilleNumber base`, including both 0! and 1! terms."""

    total = Decimal(0)
    for index in range(10):
        exponent = math.factorial(index)
        term = Decimal(1) / (Decimal(base) ** exponent)
        total += term
        if term < Decimal(10) ** (-(getcontext().prec + 5)):
            break
    return +total


def decimal_nth_root(value: Decimal, degree: int) -> Decimal:
    if degree <= 1:
        return value
    estimate = Decimal(str(float(value) ** (1.0 / degree)))
    degree_decimal = Decimal(degree)
    for _ in range(getcontext().prec + 10):
        updated = (
            Decimal(degree - 1) * estimate
            + value / (estimate ** (degree - 1))
        ) / degree_decimal
        if updated == estimate:
            break
        estimate = updated
    return +estimate


def running_coupling(reference: Decimal, rank: int) -> Decimal:
    """Keeps the full-vs-one-missing ancestor ratio rank-independent."""

    return decimal_nth_root(reference, max(1, rank - 1))


def relation_edges(relation: Relation) -> tuple[tuple[int, int], ...]:
    edges: list[tuple[int, int]] = []
    for source, successors in enumerate(relation):
        bits = successors
        while bits:
            low = bits & -bits
            target = low.bit_length() - 1
            edges.append((source, target))
            bits ^= low
    return tuple(edges)


def is_transitive(relation: Relation) -> bool:
    for source, successors in enumerate(relation):
        bits = successors
        while bits:
            low = bits & -bits
            middle = low.bit_length() - 1
            if relation[middle] & ~successors:
                return False
            bits ^= low
    return True


def relation_from_natural_mask(n: int, mask: int) -> Relation:
    relation = [0] * n
    bit = 0
    for source in range(n):
        for target in range(source + 1, n):
            if mask & (1 << bit):
                relation[source] |= 1 << target
            bit += 1
    return tuple(relation)


def permutation_edge_maps(n: int) -> tuple[tuple[int, ...], ...]:
    maps: list[tuple[int, ...]] = []
    for permutation in itertools.permutations(range(n)):
        maps.append(
            tuple(
                1 << (permutation[source] * n + permutation[target])
                for source in range(n)
                for target in range(n)
            )
        )
    return tuple(maps)


def canonical_relation_key(
    relation: Relation, edge_maps: tuple[tuple[int, ...], ...]
) -> int:
    n = len(relation)
    edge_indices = tuple(source * n + target for source, target in relation_edges(relation))
    if not edge_indices:
        return 0
    best: int | None = None
    for edge_map in edge_maps:
        code = 0
        for edge_index in edge_indices:
            code |= edge_map[edge_index]
        if best is None or code < best:
            best = code
    assert best is not None
    return best


def exhaustive_unlabeled_posets(max_rank: int) -> dict[int, list[Relation]]:
    representatives: dict[int, list[Relation]] = {}
    for n in range(max_rank + 1):
        edge_maps = permutation_edge_maps(n)
        classes: dict[int, Relation] = {}
        pair_count = n * (n - 1) // 2
        for mask in range(1 << pair_count):
            relation = relation_from_natural_mask(n, mask)
            if not is_transitive(relation):
                continue
            key = canonical_relation_key(relation, edge_maps)
            classes.setdefault(key, relation)
        representatives[n] = list(classes.values())
    return representatives


def predecessor_masks(relation: Relation) -> tuple[int, ...]:
    n = len(relation)
    predecessors = [0] * n
    for source, successors in enumerate(relation):
        bits = successors
        while bits:
            low = bits & -bits
            target = low.bit_length() - 1
            predecessors[target] |= 1 << source
            bits ^= low
    return tuple(predecessors)


def downsets(relation: Relation) -> Iterator[int]:
    n = len(relation)
    predecessors = predecessor_masks(relation)
    for subset in range(1 << n):
        valid = True
        bits = subset
        while bits:
            low = bits & -bits
            element = low.bit_length() - 1
            if predecessors[element] & ~subset:
                valid = False
                break
            bits ^= low
        if valid:
            yield subset


def maximal_count(relation: Relation, subset: int) -> int:
    total = 0
    bits = subset
    while bits:
        low = bits & -bits
        element = low.bit_length() - 1
        if relation[element] & subset == 0:
            total += 1
        bits ^= low
    return total


def phase_power(maximal: int, chirality: int) -> tuple[int, int]:
    exponent = (chirality * maximal) % 4
    return ((1, 0), (0, 1), (-1, 0), (0, -1))[exponent]


def signature(relation: Relation, subset: int) -> tuple[int, int, int]:
    omega = bin(subset).count("1")
    maximal = maximal_count(relation, subset)
    exponent = omega * (omega - 1)
    return omega, maximal, exponent


def partition_coefficients(
    relation: Relation, chirality: int = 1
) -> tuple[dict[int, int], dict[int, int], list[tuple[int, int, int, int]]]:
    real: dict[int, int] = defaultdict(int)
    imag: dict[int, int] = defaultdict(int)
    slots: list[tuple[int, int, int, int]] = []
    for subset in downsets(relation):
        omega, maximal, exponent = signature(relation, subset)
        phase_re, phase_im = phase_power(maximal, chirality)
        real[exponent] += phase_re
        imag[exponent] += phase_im
        slots.append((subset, exponent, phase_re, phase_im))
    return dict(real), dict(imag), slots


def evaluate_polynomial(coefficients: dict[int, int], coupling: Decimal) -> Decimal:
    value = Decimal(0)
    for exponent, coefficient in coefficients.items():
        if coefficient == 0:
            continue
        power = Decimal(1) if exponent == 0 else coupling**exponent
        value += Decimal(coefficient) * power
    return +value


def complex_abs(real: Decimal, imag: Decimal) -> Decimal:
    return (real * real + imag * imag).sqrt()


def decimal_close(left: Decimal, right: Decimal, digits: int = 75) -> bool:
    scale = max(Decimal(1), abs(left), abs(right))
    return abs(left - right) <= (Decimal(10) ** -digits) * scale


def evaluate_parent(
    relation: Relation, coupling: Decimal, chirality: int = 1
) -> dict[str, object]:
    real_coeffs, imag_coeffs, slots = partition_coefficients(relation, chirality)
    partition_re = evaluate_polynomial(real_coeffs, coupling)
    partition_im = evaluate_polynomial(imag_coeffs, coupling)
    partition_abs = complex_abs(partition_re, partition_im)

    raw_l1 = Decimal(0)
    raw_l2 = Decimal(0)
    raw_l4 = Decimal(0)
    largest_l2 = Decimal(0)
    timid_l2 = Decimal(0)
    slot_re = Decimal(0)
    slot_im = Decimal(0)
    full_subset = (1 << len(relation)) - 1

    for subset, exponent, phase_re, phase_im in slots:
        magnitude = Decimal(1) if exponent == 0 else abs(coupling) ** exponent
        square = magnitude * magnitude
        raw_l1 += magnitude
        raw_l2 += square
        raw_l4 += square * square
        largest_l2 = max(largest_l2, square)
        if subset == full_subset:
            timid_l2 = square
        slot_re += magnitude * Decimal(phase_re)
        slot_im += magnitude * Decimal(phase_im)

    if partition_abs == 0:
        condition = Decimal("Infinity")
        normalization_error = Decimal("Infinity")
        timid_quantum_measure = Decimal("Infinity")
    else:
        condition = raw_l1 / partition_abs
        normalized_re = (
            slot_re * partition_re + slot_im * partition_im
        ) / (partition_abs * partition_abs)
        normalized_im = (
            slot_im * partition_re - slot_re * partition_im
        ) / (partition_abs * partition_abs)
        normalization_error = complex_abs(normalized_re - 1, normalized_im)
        timid_quantum_measure = timid_l2 / (partition_abs * partition_abs)

    if raw_l2 == 0:
        born_concentration = Decimal(0)
        timid_share = Decimal(0)
        effective_slots = Decimal(0)
    else:
        born_concentration = largest_l2 / raw_l2
        timid_share = timid_l2 / raw_l2
        effective_slots = raw_l2 * raw_l2 / raw_l4

    return {
        "partition_re": partition_re,
        "partition_im": partition_im,
        "partition_abs": partition_abs,
        "condition": condition,
        "born_concentration": born_concentration,
        "born_effective_slots": effective_slots,
        "timid_born_share": timid_share,
        "timid_quantum_measure": timid_quantum_measure,
        "normalization_error": normalization_error,
        "slots": len(slots),
        "real_coefficients": real_coeffs,
        "imag_coefficients": imag_coeffs,
    }


def evaluate_antichain_rank_profile(rank: int, displacement: Decimal) -> dict[str, Decimal]:
    """Evaluate an antichain in O(rank) using its exact binomial precursor count."""
    coupling = Decimal(1) + displacement / Decimal(rank + 1)
    return evaluate_antichain_at_coupling(rank, coupling)


def harmonic_number_decimal(rank: int) -> Decimal:
    return sum((Decimal(1) / Decimal(index) for index in range(1, rank + 1)), Decimal(0))


def harmonic_corrected_coupling(rank: int) -> Decimal:
    if rank <= 1:
        return Decimal(2)
    return Decimal(1) + harmonic_number_decimal(rank) / Decimal(2 * (rank - 1))


def evaluate_antichain_at_coupling(rank: int, coupling: Decimal) -> dict[str, Decimal]:
    """Evaluate an antichain at an explicitly supplied pair coupling."""
    partition_re = Decimal(0)
    partition_im = Decimal(0)
    raw_l1 = Decimal(0)
    raw_l2 = Decimal(0)
    for omega in range(rank + 1):
        magnitude = coupling ** (omega * (omega - 1))
        multiplicity = Decimal(math.comb(rank, omega))
        term = multiplicity * magnitude
        raw_l1 += term
        raw_l2 += multiplicity * magnitude * magnitude
        phase = omega % 4
        if phase == 0:
            partition_re += term
        elif phase == 1:
            partition_im += term
        elif phase == 2:
            partition_re -= term
        else:
            partition_im -= term
    partition_abs = complex_abs(partition_re, partition_im)
    condition = raw_l1 / partition_abs
    timid_born_share = coupling ** (2 * rank * (rank - 1)) / raw_l2
    slot_one_missing_to_timid_born_ratio = (
        Decimal(rank) / coupling ** (4 * (rank - 1))
        if rank > 0
        else Decimal(0)
    )
    coherent_one_missing_to_timid_born_ratio = (
        Decimal(rank * rank) / coupling ** (4 * (rank - 1))
        if rank > 0
        else Decimal(0)
    )
    return {
        "coupling": coupling,
        "partition_abs": partition_abs,
        "condition": condition,
        "log_condition_per_rank": condition.ln() / Decimal(rank),
        "slot_timid_born_share": timid_born_share,
        "slot_one_missing_to_timid_born_ratio":
            slot_one_missing_to_timid_born_ratio,
        "coherent_one_missing_to_timid_born_ratio":
            coherent_one_missing_to_timid_born_ratio,
    }


def update_metrics(metrics: CouplingMetrics, result: dict[str, object]) -> None:
    metrics.observe(
        partition_abs=result["partition_abs"],
        condition=result["condition"],
        born_concentration=result["born_concentration"],
        born_effective_slots=result["born_effective_slots"],
        timid_born_share=result["timid_born_share"],
        timid_quantum_measure=result["timid_quantum_measure"],
        normalization_error=result["normalization_error"],
        slots=result["slots"],
    )


def transitive_closure(relation: Relation) -> Relation:
    closed = list(relation)
    for source in range(len(closed) - 1, -1, -1):
        bits = closed[source]
        while bits:
            low = bits & -bits
            target = low.bit_length() - 1
            closed[source] |= closed[target]
            bits ^= low
    return tuple(closed)


def random_natural_poset(n: int, probability: float, rng: random.Random) -> Relation:
    relation = [0] * n
    for source in range(n):
        for target in range(source + 1, n):
            if rng.random() < probability:
                relation[source] |= 1 << target
    return transitive_closure(tuple(relation))


def random_posets(
    n: int, count_per_probability: int, rng: random.Random
) -> list[Relation]:
    relations: set[Relation] = set()
    for probability in (0.08, 0.2, 0.4, 0.7):
        attempts = 0
        target = count_per_probability
        before = len(relations)
        while len(relations) - before < target and attempts < target * 30:
            relations.add(random_natural_poset(n, probability, rng))
            attempts += 1
    return sorted(relations)


def chain(n: int) -> Relation:
    return tuple(sum(1 << target for target in range(source + 1, n)) for source in range(n))


def antichain(n: int) -> Relation:
    return tuple(0 for _ in range(n))


def two_layer(n: int) -> Relation:
    lower = n // 2
    upper_mask = sum(1 << target for target in range(lower, n))
    return tuple(upper_mask if source < lower else 0 for source in range(n))


def chain_below_antichain(chain_size: int, antichain_size: int) -> Relation:
    n = chain_size + antichain_size
    relation = [0] * n
    upper_mask = sum(1 << target for target in range(chain_size, n))
    for source in range(chain_size):
        chain_above = sum(1 << target for target in range(source + 1, chain_size))
        relation[source] = chain_above | upper_mask
    return tuple(relation)


def check_signature_identities(max_omega: int, couplings: dict[str, Decimal]) -> dict[str, int]:
    factorization_checks = 0
    composition_checks = 0
    sign_checks = 0
    for omega in range(max_omega + 1):
        ordered = omega * (omega - 1)
        unordered = math.comb(omega, 2)
        assert ordered == 2 * unordered
        for maximal in range(omega + 1):
            phase = phase_power(maximal, 1)
            for coupling in couplings.values():
                left = coupling**ordered
                right = (coupling * coupling) ** unordered
                assert decimal_close(left, right)
                factorization_checks += 1
                assert (-coupling) ** ordered == left
                sign_checks += 1
            assert phase_power(maximal, -1) == (phase[0], -phase[1])
    for omega_1 in range(max_omega + 1):
        for omega_2 in range(max_omega + 1):
            lhs = math.comb(omega_1 + omega_2, 2)
            rhs = math.comb(omega_1, 2) + math.comb(omega_2, 2) + omega_1 * omega_2
            assert lhs == rhs
            composition_checks += 1
    return {
        "factorization_checks": factorization_checks,
        "sign_redundancy_checks": sign_checks,
        "composition_checks": composition_checks,
    }


def metrics_to_dict(metrics: CouplingMetrics) -> dict[str, object]:
    result = asdict(metrics)
    if metrics.parents:
        result["mean_timid_born_share"] = (
            metrics.sum_timid_born_share / Decimal(metrics.parents)
        )
        result["mean_timid_quantum_measure"] = (
            metrics.sum_timid_quantum_measure / Decimal(metrics.parents)
        )
    return decimal_json(result)


def evaluate_family(
    relations: Iterable[Relation], couplings: dict[str, Decimal]
) -> dict[str, object]:
    metrics = {name: CouplingMetrics() for name in couplings}
    chirality_checks = 0
    sign_checks = 0
    constant_coefficient_checks = 0
    coefficient_structure = {
        "parents": 0,
        "parents_with_negative_real_coefficient": 0,
        "parents_with_mixed_real_signs": 0,
        "parents_with_nonunimodal_abs_real_coefficients": 0,
        "parents_with_real_partition_zero_at_one": 0,
        "parents_with_complex_partition_zero_at_one": 0,
    }
    for relation in relations:
        plus_re, plus_im, _ = partition_coefficients(relation, 1)
        minus_re, minus_im, _ = partition_coefficients(relation, -1)
        assert plus_re == minus_re
        assert plus_im == {exponent: -value for exponent, value in minus_im.items()}
        assert plus_re.get(0, 0) == 1
        constant_coefficient_checks += 1
        chirality_checks += 1
        nonzero_real = [
            value for _, value in sorted(plus_re.items()) if value != 0
        ]
        abs_real = [abs(value) for value in nonzero_real]
        peak = max(range(len(abs_real)), key=abs_real.__getitem__)
        abs_real_unimodal = (
            all(abs_real[index] <= abs_real[index + 1] for index in range(peak))
            and all(
                abs_real[index] >= abs_real[index + 1]
                for index in range(peak, len(abs_real) - 1)
            )
        )
        has_negative = any(value < 0 for value in nonzero_real)
        has_positive = any(value > 0 for value in nonzero_real)
        real_at_one = sum(plus_re.values())
        imag_at_one = sum(plus_im.values())
        coefficient_structure["parents"] += 1
        coefficient_structure["parents_with_negative_real_coefficient"] += int(
            has_negative
        )
        coefficient_structure["parents_with_mixed_real_signs"] += int(
            has_negative and has_positive
        )
        coefficient_structure[
            "parents_with_nonunimodal_abs_real_coefficients"
        ] += int(not abs_real_unimodal)
        coefficient_structure["parents_with_real_partition_zero_at_one"] += int(
            real_at_one == 0
        )
        coefficient_structure[
            "parents_with_complex_partition_zero_at_one"
        ] += int(real_at_one == 0 and imag_at_one == 0)
        for name, coupling in couplings.items():
            result = evaluate_parent(relation, coupling, 1)
            reflected = evaluate_parent(relation, -coupling, 1)
            assert result["partition_re"] == reflected["partition_re"]
            assert result["partition_im"] == reflected["partition_im"]
            sign_checks += 1
            update_metrics(metrics[name], result)
    return {
        "couplings": {name: metrics_to_dict(value) for name, value in metrics.items()},
        "chirality_conjugation_checks": chirality_checks,
        "coupling_sign_checks": sign_checks,
        "constant_coefficient_checks": constant_coefficient_checks,
        "real_coefficient_structure": coefficient_structure,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-rank", type=int, default=6)
    parser.add_argument("--random-max-rank", type=int, default=12)
    parser.add_argument("--structured-max-rank", type=int, default=16)
    parser.add_argument("--random-per-density", type=int, default=32)
    parser.add_argument("--seed", type=int, default=20260719)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/chiral_growth_generalization/summary.json"),
    )
    args = parser.parse_args()

    started = time.perf_counter()
    canonical = liouville_number(2)
    shifted = canonical + 1
    subcritical = canonical - 1
    fixed_couplings = {
        "canonical_lambda": canonical,
        "shifted_lambda": shifted,
        "subcritical_lambda": subcritical,
        "sparse_lambda": Decimal(0),
    }

    def couplings_at(rank: int) -> dict[str, Decimal]:
        return {
            **fixed_couplings,
            "running_lambda": running_coupling(canonical, rank),
            "rational_critical_lambda": Decimal(rank + 2) / Decimal(rank + 1),
            "harmonic_corrected_lambda": harmonic_corrected_coupling(rank),
        }

    signature_checks = check_signature_identities(
        args.structured_max_rank,
        {
            "canonical": canonical,
            "shifted": shifted,
            "subcritical": subcritical,
        },
    )

    exhaustive_started = time.perf_counter()
    exhaustive = exhaustive_unlabeled_posets(args.exhaustive_rank)
    expected_counts = {0: 1, 1: 1, 2: 2, 3: 5, 4: 16, 5: 63, 6: 318}
    exhaustive_results: dict[str, object] = {}
    for rank, representatives in exhaustive.items():
        if rank in expected_counts:
            assert len(representatives) == expected_counts[rank]
        exhaustive_results[str(rank)] = {
            "unlabeled_posets": len(representatives),
            "coupling_values": decimal_json(couplings_at(rank)),
            **evaluate_family(representatives, couplings_at(rank)),
        }
    exhaustive_seconds = time.perf_counter() - exhaustive_started

    rng = random.Random(args.seed)
    random_results: dict[str, object] = {}
    for rank in range(args.exhaustive_rank + 1, args.random_max_rank + 1):
        relations = random_posets(rank, args.random_per_density, rng)
        random_results[str(rank)] = {
            "distinct_natural_posets": len(relations),
            "coupling_values": decimal_json(couplings_at(rank)),
            **evaluate_family(relations, couplings_at(rank)),
        }

    structured_results: dict[str, object] = {}
    for rank in range(args.exhaustive_rank + 1, args.structured_max_rank + 1):
        families = {
            "chain": chain(rank),
            "antichain": antichain(rank),
            "two_layer": two_layer(rank),
        }
        structured_results[str(rank)] = {
            name: evaluate_family([relation], couplings_at(rank))
            for name, relation in families.items()
        }

    obstruction = chain_below_antichain(8, 6)
    old_re, old_im, old_slots = partition_coefficients(obstruction, 1)
    old_partition = (
        sum(old_re.values()),
        sum(old_im.values()),
    )
    assert old_partition == (0, 0)
    interacting_obstruction = {
        name: evaluate_parent(obstruction, coupling, 1)
        for name, coupling in couplings_at(14).items()
    }
    for result in interacting_obstruction.values():
        assert result["partition_abs"] > 0
    obstruction_results = {
        "rank": 14,
        "precursor_slots": len(old_slots),
        "old_character_partition": {"real": 0, "imag": 0},
        "interacting": decimal_json(interacting_obstruction),
    }

    endpoint = {}
    one_event_parent = antichain(1)
    for name, coupling in couplings_at(1).items():
        plus = evaluate_parent(one_event_parent, coupling, 1)
        endpoint[name] = {
            "partition_re": decimal_json(plus["partition_re"]),
            "partition_im": decimal_json(plus["partition_im"]),
        }
    assert len(set(json.dumps(value, sort_keys=True) for value in endpoint.values())) == 1

    antichain_scan_ranks = (20, 40, 80, 120, 160, 200)
    antichain_critical_scan = {
        name: {
            str(rank): decimal_json(evaluate_antichain_rank_profile(rank, value))
            for rank in antichain_scan_ranks
        }
        for name, value in {
            "c_half_kappa_one": Decimal(1) / Decimal(2),
            "c_one_kappa_two": Decimal(1),
            "c_two_kappa_four": Decimal(2),
        }.items()
    }
    harmonic_corrected_scan = {
        str(rank): decimal_json(
            evaluate_antichain_at_coupling(rank, harmonic_corrected_coupling(rank))
        )
        for rank in antichain_scan_ranks
    }

    output = {
        "model": "complete chiral causal growth",
        "law": "lambda^(omega*(omega-1)) * (chirality*i)^m",
        "effective_law": "g^choose(omega,2) * (chirality*i)^m, g=lambda^2",
        "precision_digits": getcontext().prec,
        "configuration": {
            "exhaustive_rank": args.exhaustive_rank,
            "random_max_rank": args.random_max_rank,
            "structured_max_rank": args.structured_max_rank,
            "random_per_density": args.random_per_density,
            "seed": args.seed,
        },
        "fixed_coupling_values": decimal_json(fixed_couplings),
        "running_coupling": {
            "formula": "lambda_n = canonical_lambda^(1/max(1,n-1))",
            "purpose": "keeps lambda_n^(2(n-1)) = canonical_lambda^2",
            "values_by_rank": {
                str(rank): decimal_json(running_coupling(canonical, rank))
                for rank in range(args.structured_max_rank + 1)
            },
        },
        "rational_critical_family": {
            "representative_formula": "lambda_n = (n+2)/(n+1)",
            "general_formula": "lambda_n(a,b) = 1 + (a/b)/(n+1)",
            "effective_scaling_limit": "(n+1)(g_n-1) -> 2a/b",
            "proved_partition_bound":
                "|Z_C| >= (b(n+1))^(-n(n-1))",
        },
        "harmonic_multiplicity_corrected_schedule": {
            "formula": "lambda_0=lambda_1=2; lambda_n=1+H_n/(2(n-1))",
            "proved_limit":
                "rank^2/lambda_rank^(4(rank-1)) -> exp(-2*EulerMascheroniConstant)",
            "coarse_graining":
                "isomorphic antichain slots add coherently before Born squaring",
            "antichain_scan": harmonic_corrected_scan,
        },
        "signature_checks": signature_checks,
        "endpoint_check": endpoint,
        "exhaustive": exhaustive_results,
        "random_higher_rank": random_results,
        "structured_higher_rank": structured_results,
        "old_obstruction": obstruction_results,
        "antichain_critical_scan": antichain_critical_scan,
        "timing_seconds": {
            "exhaustive": round(exhaustive_seconds, 6),
            "total": round(time.perf_counter() - started, 6),
        },
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(decimal_json(output), indent=2) + "\n")
    print(json.dumps(decimal_json(output["timing_seconds"]), indent=2))
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
