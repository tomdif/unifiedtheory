#!/usr/bin/env python3
"""Sharp bounded-contrast cut optimization and its actual birth realization.

The 81:1 example is calibrated to one statistic, not a derivation of 4D.
Exact certificates control every allowed cut law. Independent LP and vertex
checks validate the optimizer; exact causal audits check birth normalization,
protected records, and Arb scalar coherent/Born lifts.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from flint import ctx
from scipy.optimize import linprog

from microscopic_selection_audit import (
    canonical_relation_key, child_relation, coherent_lift, downsets,
    exhaustive_unlabeled_posets, insertion_probabilities, permutation_edge_maps,
)
from protected_selection_audit import protected_step


def threshold_mean(n, A, m):
    L = n+1
    return (F(L*n)+(A-1)*m*(m-1))/(2*(L+(A-1)*m))


def optimal_cut(n, A):
    A = F(A)
    assert A >= 1
    # Floating point proposes nearby integers; the exact dual certificate
    # below validates global optimality independently of that proposal.
    center = int((n+1)/(1+math.sqrt(float(A))))
    candidates = range(max(0, center-2), min(n+1, center+3)+1)
    mean, m = min((threshold_mean(n, A, m), m) for m in candidates)
    cutoff = (mean.numerator+mean.denominator-1)//mean.denominator
    assert 0 <= cutoff <= n+1
    # The threshold centered at its mean has exactly zero dual objective.
    assert threshold_mean(n, A, cutoff) == mean
    return mean, m


def cut_probabilities(n, A):
    mean, m = optimal_cut(n, A)
    weights = {j: F(A) if j < m else F(1) for j in range(n+1)}
    partition = sum(weights.values())
    p = {j: weights[j]/partition for j in weights}
    assert sum(p.values()) == 1
    assert sum(j*p[j] for j in p) == mean
    return p, mean, m


def independent_lp(n, A):
    # Variables are normalized probabilities p_0,...,p_n and a scale t.
    # t <= p_j <= A*t is equivalent to positive max/min contrast <= A.
    c = np.array(list(range(n+1))+[0.0])
    rows = []
    for j in range(n+1):
        low, high = np.zeros(n+2), np.zeros(n+2)
        low[j], low[-1] = -1, 1
        high[j], high[-1] = 1, -float(A)
        rows.extend((low, high))
    result = linprog(c, A_ub=np.array(rows), b_ub=np.zeros(len(rows)),
                     A_eq=np.array([[1.0]*(n+1)+[0.0]]), b_eq=[1.0],
                     bounds=(0, None), method="highs")
    assert result.success, result.message
    return result.fun


def audit_cut_optimization():
    ratios = [F(1), F(2), F(9, 4), F(4), F(9), F(25), F(81), F(225)]
    lp_count, vertex_count, certificate_count = 0, 0, 0
    for A in ratios:
        for n in list(range(25))+[50, 100, 250]:
            mean, _ = optimal_cut(n, A)
            actual = independent_lp(n, A)
            assert abs(actual-float(mean)) <= 1e-8*(1+n)
            lp_count += 1
        for n in range(4097):
            mean, m = optimal_cut(n, A)
            assert 0 <= mean <= F(n, 2)
            certificate_count += 1
    for A in (F(2), F(9), F(81)):
        for n in range(10):
            mean, _ = optimal_cut(n, A)
            for bits in itertools.product((0, 1), repeat=n+1):
                weights = [A if bit else F(1) for bit in bits]
                assert sum(j*w for j, w in enumerate(weights))/sum(weights) >= mean
                vertex_count += 1
    # Verify the square identity with exact arithmetic, including nonsquare
    # rational contrasts represented by rational s with A=s^2.
    for s in (F(1), F(3, 2), F(2), F(3), F(5), F(9), F(15)):
        for n in list(range(50))+[100, 1000, 10000, 1000000]:
            A, L = s*s, n+1
            mean, m = optimal_cut(n, A)
            remainder = (s-1)*(L-(1+s)*m)**2/(2*(1+s)*(L+(A-1)*m))
            assert mean == F(L)/(1+s)-F(1, 2)+remainder
            assert remainder >= 0
    # Rigidity/regret tests use interior, nonmonotone weights, not just vertices.
    for n in range(1, 30):
        A = F(81)
        mean, _ = optimal_cut(n, A)
        w = [1+(A-1)*F((17*j+7) % 31, 30) for j in range(n+1)]
        actual = sum(j*w[j] for j in range(n+1))/sum(w)
        slack = sum((A-w[j])*(mean-j) if j < mean else (w[j]-1)*(j-mean)
                    for j in range(n+1))
        assert sum(w)*(actual-mean) == slack >= 0
    rows = []
    for n in (9, 49, 99, 999, 9999, 99999, 999999):
        mean, m = optimal_cut(n, F(81))
        assert mean == F(n-4, 10)  # Exact saturation at n+1 divisible by 10.
        rows.append(dict(rank=n, threshold=m, mean_ancestors=str(mean),
                         mean_ancestor_fraction=str(mean/n)))
    return dict(dual_certificates=certificate_count, independent_LP_checks=lp_count,
                all_vertex_checks=vertex_count, eighty_one_ratio=rows)


def audit_actual_births():
    rows, total, corrected = [], 0, 0
    for n, parents in exhaustive_unlabeled_posets(5).items():
        maps = permutation_edge_maps(n+1)
        cut, mean, threshold = cut_probabilities(n, F(81))
        for parent in parents:
            reference = insertion_probabilities(parent)
            p, record, defect = {}, {}, {}
            for past in downsets(parent):
                omega = bin(past).count("1")
                mass = reference[past]*(n+1)*cut[omega]
                key = canonical_relation_key(child_relation(parent, past), maps)
                h = (omega, sum(1 for i, row in enumerate(parent)
                                if row == 0 and past & (1 << i)))
                g = sum(1 for i in range(n) if past & (1 << i)
                        and bin(parent[i] & past).count("1") == 1)
                assert key not in record or record[key] == h
                assert key not in defect or defect[key] == g
                p[key] = p.get(key, F(0))+mass
                record[key], defect[key] = h, g
            assert sum(p.values()) == 1 and all(prob > 0 for prob in p.values())
            q, stats = protected_step(p, record, defect)
            for j in cut:
                assert sum(p[key] for key in p if record[key][0] == j) == cut[j]
                assert sum(q[key] for key in q if record[key][0] == j) == cut[j]
            assert sum(q[key]*record[key][0] for key in q) == mean
            coherent_lift(p)
            coherent_lift(q)
            total += 1
            corrected += stats["strict_descent"]
            rows.append(dict(rank=n, successor_masks=list(parent),
                             mean_ancestors=str(mean), cutoff=threshold,
                             shape_improvement=stats["exact_decrease"]))
    # Explicit strict raw classical Bell counterexample survives the calibration.
    one, _, _ = cut_probabilities(1, F(81))
    two, _, _ = cut_probabilities(2, F(81))
    before = (two[1]/2)/two[0]
    after = one[1]/one[0]
    assert before == F(1, 162) and after == F(1, 81)
    return dict(parents=total, strict_shape_improvements=corrected, records=rows,
                bell_singleton_to_empty_before=str(before),
                bell_singleton_to_empty_after_spectator_deletion=str(after))


def audit_same_statistic_wrong_geometry():
    rows = []
    for length in (2, 5, 10, 20, 50):
        n = 10*length
        parent = tuple(sum(1 << j for j in range(i+1, (i//length+1)*length))
                       for i in range(n))
        relations = sum(bin(row).count("1") for row in parent)
        assert relations == 10*length*(length-1)//2
        fraction = F(relations, n*(n-1)//2)
        assert fraction == F(length-1, 10*length-1)
        rows.append(dict(events=n, ordering_fraction=str(fraction),
                         longest_chain=length, connected_components=10))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 256
    optimization = audit_cut_optimization()
    births = audit_actual_births()
    counterexample = audit_same_statistic_wrong_geometry()
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/causal_cut_contrast_audit.py", "scripts/microscopic_selection_audit.py",
             "scripts/protected_selection_audit.py", "scripts/harmonic_born_geometry_drift.py",
             "scripts/harmonic_child_nonuniformity.py", "scripts/chiral_growth_generalization.py",
             "UnifiedTheory/Audit/KFCausalBornCutWeightEnvelope.lean"]
    result = dict(scope="sharp ordering-statistic constraint, not a physical 4D law",
                  exact_arithmetic="Fraction certificates and probability laws; Arb lifts at 256 bits",
                  independent_numerical_check="SciPy HiGHS linear programming",
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},
                  optimization=optimization, actual_births=births,
                  disjoint_ten_chain_counterexample=counterexample)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print({key: value for key, value in optimization.items() if key != "eighty_one_ratio"})
    print("Actual births:", births["parents"], "parents;", births["strict_shape_improvements"],
          "strict shape improvements; all cut laws and coherent/Born lifts pass.")
    print("Sharp finite bounds and 81:1 saturation checked through rank 1,000,000.")
    print("Bell counterexample: 1/162 versus 1/81. Matching one statistic does not imply 4D.")


if __name__ == "__main__":
    main()
