#!/usr/bin/env python3
"""Exact finite analogue of correcting a residual while preserving moments.

Protect the joint law of ancestor count and hits on the parent's maximal
frontier. Change the remaining probabilities to reduce a shape observable:
the number of newly created intervals with exactly one internal event.
This observable is not claimed to be the Gate-3 defect or an Einstein action.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

from flint import ctx

from microscopic_selection_audit import (
    canonical_relation_key, child_relation, coherent_lift, downsets,
    exhaustive_unlabeled_posets, insertion_probabilities, permutation_edge_maps,
)


def protected_step(p, record, defect):
    groups = defaultdict(list)
    for key in p:
        groups[record[key]].append(key)
    mass = {h: sum(p[key] for key in keys) for h, keys in groups.items()}
    means = {h: sum(p[key]*defect[key] for key in keys)/mass[h]
             for h, keys in groups.items()}
    residual = {key: defect[key]-means[record[key]] for key in p}
    epsilon = Fraction(1, 2)/(1+max(abs(r) for r in residual.values()))
    q = {key: p[key]*(1-epsilon*residual[key]) for key in p}
    assert all(probability > 0 for probability in q.values())
    assert sum(q.values()) == 1
    for h, keys in groups.items():
        assert sum(q[key] for key in keys) == mass[h]
        assert sum(p[key]*residual[key] for key in keys) == 0
    variance = sum(p[key]*residual[key]**2 for key in p)
    before = sum(p[key]*defect[key] for key in p)
    after = sum(q[key]*defect[key] for key in p)
    assert before-after == epsilon*variance
    # At least half the original probability remains at each child.
    assert all(q[key] >= p[key]/2 for key in p)
    mean_horizon = sum(p[key]*record[key][1] for key in p)
    leakage = sum(p[key]*(record[key][1]-mean_horizon)*residual[key]**2 for key in p)
    return q, {"step": str(epsilon), "conditional_variance": str(variance),
               "defect_before": str(before), "defect_after": str(after),
               "exact_decrease": str(before-after),
               "uncorrected_exponential_horizon_second_derivative": str(leakage),
               "strict_descent": variance > 0, "exponential_leakage_nonzero": leakage != 0,
               "protected_records": len(groups), "children": len(p)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 256
    rows = []
    summary = {}
    for n, parents in exhaustive_unlabeled_posets(5).items():
        maps = permutation_edge_maps(n+1)
        counts = {"parents": len(parents), "strict_descent": 0,
                  "zero_conditional_variance": 0, "uncorrected_exponential_leakage": 0}
        for parent in parents:
            raw = insertion_probabilities(parent)
            p, record, defect = {}, {}, {}
            for past in downsets(parent):
                key = canonical_relation_key(child_relation(parent, past), maps)
                omega = bin(past).count("1")
                frontier_hits = sum(1 for i, row in enumerate(parent)
                                    if row == 0 and past & (1 << i))
                new_intervals = sum(1 for i in range(n) if past & (1 << i)
                                    and bin(parent[i] & past).count("1") == 1)
                assert key not in record or record[key] == (omega, frontier_hits)
                assert key not in defect or defect[key] == new_intervals
                record[key], defect[key] = (omega, frontier_hits), new_intervals
                p[key] = p.get(key, Fraction(0))+raw[past]
            q, stats = protected_step(p, record, defect)
            # The new law preserves the old coarse-volume distribution exactly.
            for omega in range(n+1):
                assert sum(q[key] for key in q if record[key][0] == omega) == Fraction(1, n+1)
            assert sum(q[key]*record[key][0] for key in q) == Fraction(n, 2)
            coherent_lift(q)
            counts["strict_descent"] += stats["strict_descent"]
            counts["zero_conditional_variance"] += not stats["strict_descent"]
            counts["uncorrected_exponential_leakage"] += stats["exponential_leakage_nonzero"]
            rows.append({"rank": n, "successor_masks": list(parent), **stats})
        summary[str(n)] = counts
    source = Path(__file__).resolve().parent
    names = [Path(__file__).name, "microscopic_selection_audit.py", "harmonic_born_geometry_drift.py",
             "harmonic_child_nonuniformity.py", "chiral_growth_generalization.py"]
    result = {"scope": "finite protected selection; no claimed physical action or continuum limit",
              "arithmetic": "exact Fraction probability identities; 256-bit Arb coherent/Born lift",
              "protected_record": ["ancestor count", "hits on maximal parent frontier"],
              "defect": "number of new intervals with exactly one internal event",
              "source_sha256": {name: hashlib.sha256((source/name).read_bytes()).hexdigest()
                                for name in names},
              "ranks": summary, "parents": rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(summary, indent=2))
    print("Exact protected distributions, positivity, descent identity, and amplitude lifts passed.")


if __name__ == "__main__":
    main()
