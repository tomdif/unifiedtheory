#!/usr/bin/env python3
"""Exact audit of harmonic chiral amplitudes on unlabeled child fibers.

This is a finite diagnostic for the remaining hypothesis in
`KFCausalBornShellGeneralLaw.lean`: whenever a parent has more than one
physical unlabeled child, are its harmonic-critical aggregated amplitudes
nonuniform on that support?

Unlike the broader decimal stress test, this script:

* evaluates the harmonic coupling as an exact `Fraction`;
* evaluates amplitudes in Q(i) as pairs of exact fractions; and
* coherently aggregates all precursor downsets that produce isomorphic
  unlabeled children before comparing amplitudes.

The script is evidence, not part of the Lean proof boundary.
"""

from __future__ import annotations

import argparse
import json
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from chiral_growth_generalization import (
    Relation,
    canonical_relation_key,
    downsets,
    exhaustive_unlabeled_posets,
    permutation_edge_maps,
    phase_power,
    signature,
)


GaussianRational = tuple[Fraction, Fraction]


def harmonic_number(rank: int) -> Fraction:
    return sum((Fraction(1, index) for index in range(1, rank + 1)), Fraction(0))


def harmonic_pair_coupling(rank: int) -> Fraction:
    if rank <= 1:
        return Fraction(2)
    return Fraction(1) + harmonic_number(rank) / (2 * (rank - 1))


def child_relation(parent: Relation, precursor: int) -> Relation:
    """Adjoin one new maximal event above exactly `precursor`."""

    rank = len(parent)
    newborn = 1 << rank
    return tuple(
        successors | (newborn if precursor & (1 << source) else 0)
        for source, successors in enumerate(parent)
    ) + (0,)


def gaussian_add(left: GaussianRational, right: GaussianRational) -> GaussianRational:
    return left[0] + right[0], left[1] + right[1]


def raw_amplitude(
    parent: Relation, precursor: int, coupling: Fraction, chirality: int
) -> GaussianRational:
    _, maximal, exponent = signature(parent, precursor)
    phase_real, phase_imag = phase_power(maximal, chirality)
    magnitude = coupling**exponent
    return magnitude * phase_real, magnitude * phase_imag


def aggregated_child_amplitudes(
    parent: Relation,
    coupling: Fraction,
    chirality: int,
    child_edge_maps: tuple[tuple[int, ...], ...],
    child_key_cache: dict[Relation, int],
) -> dict[int, GaussianRational]:
    aggregated: dict[int, GaussianRational] = defaultdict(
        lambda: (Fraction(0), Fraction(0))
    )
    for precursor in downsets(parent):
        child = child_relation(parent, precursor)
        key = child_key_cache.get(child)
        if key is None:
            key = canonical_relation_key(child, child_edge_maps)
            child_key_cache[child] = key
        aggregated[key] = gaussian_add(
            aggregated[key], raw_amplitude(parent, precursor, coupling, chirality)
        )
    return dict(aggregated)


def relation_code(relation: Relation) -> list[int]:
    return list(relation)


def fraction_json(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def gaussian_json(value: GaussianRational) -> dict[str, str]:
    return {"real": fraction_json(value[0]), "imag": fraction_json(value[1])}


def audit(max_rank: int) -> dict[str, object]:
    representatives = exhaustive_unlabeled_posets(max_rank)
    ranks: dict[str, object] = {}
    first_uniform_branching: dict[str, object] | None = None
    first_chirality_mismatch: dict[str, object] | None = None
    total_parents = 0
    total_branching = 0
    total_child_classes = 0

    for rank, parents in representatives.items():
        coupling = harmonic_pair_coupling(rank)
        child_edge_maps = permutation_edge_maps(rank + 1)
        child_key_cache: dict[Relation, int] = {}
        branching = 0
        uniform_branching = 0
        min_children: int | None = None
        max_children = 0
        min_distinct_amplitudes: int | None = None
        max_fiber_multiplicity = 0

        for parent_index, parent in enumerate(parents):
            plus = aggregated_child_amplitudes(
                parent, coupling, 1, child_edge_maps, child_key_cache
            )
            minus = aggregated_child_amplitudes(
                parent, coupling, -1, child_edge_maps, child_key_cache
            )
            child_count = len(plus)
            total_parents += 1
            total_child_classes += child_count
            min_children = child_count if min_children is None else min(min_children, child_count)
            max_children = max(max_children, child_count)

            conjugate_plus = {key: (value[0], -value[1]) for key, value in plus.items()}
            if minus != conjugate_plus and first_chirality_mismatch is None:
                first_chirality_mismatch = {
                    "rank": rank,
                    "parent_index": parent_index,
                    "parent_successor_masks": relation_code(parent),
                }

            amplitude_values = set(plus.values())
            distinct_count = len(amplitude_values)
            min_distinct_amplitudes = (
                distinct_count
                if min_distinct_amplitudes is None
                else min(min_distinct_amplitudes, distinct_count)
            )
            precursor_count = sum(1 for _ in downsets(parent))
            max_fiber_multiplicity = max(
                max_fiber_multiplicity, precursor_count - child_count + 1
            )

            if child_count > 1:
                branching += 1
                total_branching += 1
                if distinct_count == 1:
                    uniform_branching += 1
                    if first_uniform_branching is None:
                        first_uniform_branching = {
                            "rank": rank,
                            "parent_index": parent_index,
                            "parent_successor_masks": relation_code(parent),
                            "coupling": fraction_json(coupling),
                            "child_count": child_count,
                            "aggregated_amplitude": gaussian_json(next(iter(amplitude_values))),
                        }

        ranks[str(rank)] = {
            "harmonic_pair_coupling": fraction_json(coupling),
            "unlabeled_parents": len(parents),
            "branching_parents": branching,
            "uniform_branching_parents": uniform_branching,
            "min_child_classes": min_children,
            "max_child_classes": max_children,
            "min_distinct_aggregated_amplitudes": min_distinct_amplitudes,
            "cached_labeled_children": len(child_key_cache),
            "max_fiber_multiplicity_upper_proxy": max_fiber_multiplicity,
        }

    return {
        "claim_tested": (
            "every parent with more than one physical unlabeled child has "
            "nonuniform harmonic-critical aggregated amplitudes"
        ),
        "arithmetic": "exact Q(i)",
        "max_exhaustive_rank": max_rank,
        "total_unlabeled_parents": total_parents,
        "total_branching_parents": total_branching,
        "total_child_classes": total_child_classes,
        "first_uniform_branching_counterexample": first_uniform_branching,
        "chirality_conjugation_failure": first_chirality_mismatch,
        "ranks": ranks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-rank", type=int, default=5)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    started = time.perf_counter()
    result = audit(args.max_rank)
    result["elapsed_seconds"] = time.perf_counter() - started
    serialized = json.dumps(result, indent=2, sort_keys=True)
    print(serialized)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized + "\n", encoding="utf-8")
    return int(result["first_uniform_branching_counterexample"] is not None)


if __name__ == "__main__":
    raise SystemExit(main())
