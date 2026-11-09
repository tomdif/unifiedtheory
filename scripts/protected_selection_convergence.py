#!/usr/bin/env python3
"""Sharp protected-selection floors and actual bridge-census convergence.

Exact finite probabilities; Arb checks scalar coherent/Born lifts. The census
selection reconstructs a given order's transport. It does not generate that
order through causal births. Growing-bank results use a specified algorithm
which updates every existing record once per added record.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path

from flint import ctx

from microscopic_selection_audit import (
    canonical_relation_key, child_relation, coherent_lift, downsets,
    exhaustive_unlabeled_posets, insertion_probabilities, permutation_edge_maps,
)


def expectation(p, score):
    return sum((p[key]*score[key] for key in p), F(0))


def record_groups(p, record):
    groups = defaultdict(list)
    for key in p:
        groups[record[key]].append(key)
    return groups


def recordwise_optimum(p, record, score):
    """Sharp floor and a tie-invariant minimizer with the same record law.

    Within each record, retain only its minimum-score children, distributing
    mass among them proportionally to p. The exact lower-envelope certificate
    bounds every admissible law, not only a selected family of updates.
    """
    assert all(value > 0 for value in p.values()) and sum(p.values()) == 1
    groups = record_groups(p, record)
    q = dict.fromkeys(p, F(0))
    floor = F(0)
    for keys in groups.values():
        mass = sum(p[key] for key in keys)
        minimum = min(score[key] for key in keys)
        winners = [key for key in keys if score[key] == minimum]
        winning_mass = sum(p[key] for key in winners)
        floor += mass*minimum
        for key in winners:
            q[key] = mass*p[key]/winning_mass
        assert sum(q[key] for key in keys) == mass
        assert all(score[key] >= minimum for key in keys)
    assert sum(q.values()) == 1 and expectation(q, score) == floor
    assert floor <= expectation(p, score)
    # A positive mixture preserves all records and approaches the sharp floor.
    mixed = {key: (q[key]+p[key])/2 for key in p}
    assert all(value > 0 for value in mixed.values())
    assert expectation(mixed, score) == (floor+expectation(p, score))/2
    coherent_lift(mixed)
    return floor, q


def positive_law_below(p, optimum, score, floor, target):
    """Explicit full-support strict descent whenever the sharp floor allows it."""
    assert floor < target
    excess = expectation(p, score)-floor
    theta = min(F(1, 2), (target-floor)/(2*excess)) if excess else F(1, 2)
    q = {key: (1-theta)*optimum[key]+theta*p[key] for key in p}
    assert all(value > 0 for value in q.values())
    assert expectation(q, score) < target
    coherent_lift(q)
    return q


def interval_count(parent):
    """Count ordered endpoints whose open interval has exactly one event."""
    return sum(1 for i in range(len(parent)) for j in range(len(parent))
               if parent[i] & (1 << j)
               and sum(1 for k in range(len(parent))
                       if parent[i] & (1 << k) and parent[k] & (1 << j)) == 1)


def density(count, rank):
    # A triple contributes at most one such interval; no dimension is assumed.
    return F(count, comb(rank, 3)) if rank >= 3 else F(0)


def audit_birth_floors():
    rows, summary = [], {}
    for n, parents in exhaustive_unlabeled_posets(5).items():
        maps = permutation_edge_maps(n+1)
        counts = dict(parents=len(parents), absolute_descent_feasible=0,
                      strictly_positive_absolute_drift_floor=0,
                      density_descent_feasible=0, improves_over_reference=0)
        for parent in parents:
            raw = insertion_probabilities(parent)
            parent_count = interval_count(parent)
            p, record, score = {}, {}, {}
            for past in downsets(parent):
                child = child_relation(parent, past)
                key = canonical_relation_key(child, maps)
                h = (bin(past).count("1"), sum(1 for i, row in enumerate(parent)
                                              if row == 0 and past & (1 << i)))
                child_count = interval_count(child)
                increment = sum(1 for i in range(n) if past & (1 << i)
                                and bin(parent[i] & past).count("1") == 1)
                # Independent endpoint census verifies the growth decomposition.
                assert child_count == parent_count+increment
                assert key not in record or record[key] == h
                assert key not in score or score[key] == child_count
                record[key], score[key] = h, F(child_count)
                p[key] = p.get(key, F(0))+raw[past]
            floor, optimum = recordwise_optimum(p, record, score)
            absolute_drift = floor-parent_count
            assert absolute_drift >= 0
            counts["absolute_descent_feasible"] += absolute_drift < 0
            dscore = {key: density(value, n+1) for key, value in score.items()}
            dfloor, doptimum = recordwise_optimum(p, record, dscore)
            parent_density = density(parent_count, n)
            feasible = dfloor < parent_density
            if feasible:
                q = positive_law_below(p, doptimum, dscore, dfloor, parent_density)
                for keys in record_groups(p, record).values():
                    assert sum(q[key] for key in keys) == sum(p[key] for key in keys)
            counts["strictly_positive_absolute_drift_floor"] += absolute_drift > 0
            counts["density_descent_feasible"] += feasible
            counts["improves_over_reference"] += floor < expectation(p, score)
            rows.append(dict(rank=n, successor_masks=list(parent),
                             parent_interval_count=parent_count,
                             minimum_expected_child_count=str(floor),
                             minimum_absolute_drift=str(absolute_drift),
                             parent_density=str(parent_density),
                             minimum_expected_child_density=str(dfloor),
                             density_descent_feasible=feasible))
        summary[str(n)] = counts
    return dict(summary=summary, parents=rows)


PROFILES = ((2, -1, -1), (-1, 2, -1), (-1, -1, 2))
TRANSPORTS = {"e01": (1, 0, 2), "e02": (0, 2, 1),
              "e13": (0, 1, 2), "e23": (0, 1, 2), "e30": (0, 1, 2)}
CANDIDATES = tuple(itertools.permutations(range(3)))


def relative(sigma, tau):
    inverse = tuple(sigma.index(i) for i in range(3))
    return tuple(inverse[tau[i]] for i in range(3))


def census_defect(sigma, tau):
    """Original profile inner-product definition, independently cross-checked."""
    rel = relative(sigma, tau)
    score = sum(sum(x*y for x, y in zip(PROFILES[i], PROFILES[rel[i]]))
                for i in range(3))
    defect = 18-score
    assert defect == 9*(3-sum(rel[i] == i for i in range(3)))
    return F(defect)


def parity(permutation):
    return sum(permutation[i] > permutation[j]
               for i in range(3) for j in range(i+1, 3)) % 2


def conditional_power(p, record, weights, k):
    q = {}
    for keys in record_groups(p, record).values():
        mass = sum(p[key] for key in keys)
        partition = sum(p[key]*weights[key]**k for key in keys)
        for key in keys:
            q[key] = mass*p[key]*weights[key]**k/partition
        assert sum(q[key] for key in keys) == mass
    assert sum(q.values()) == 1 and all(value > 0 for value in q.values())
    return q


def audit_census():
    # Unequal edge masses test preservation beyond a uniform special case.
    edge_mass = {edge: F(i, 15) for i, edge in enumerate(TRANSPORTS, 1)}
    p, edge_record, parity_record, score, weights = {}, {}, {}, {}, {}
    for edge, sigma in TRANSPORTS.items():
        distribution = Counter()
        for tau in CANDIDATES:
            key = (edge, tau)
            p[key] = edge_mass[edge]/6
            edge_record[key] = edge
            parity_record[key] = (edge, parity(relative(sigma, tau)))
            score[key] = census_defect(sigma, tau)
            weights[key] = 1-score[key]/36
            assert F(1, 4) <= weights[key] <= 1
            distribution[str(score[key])] += 1
        assert distribution == {"0": 1, "18": 3, "27": 2}
    edge_floor, _ = recordwise_optimum(p, edge_record, score)
    parity_floor, _ = recordwise_optimum(p, parity_record, score)
    assert edge_floor == 0 and parity_floor == 9
    ordinary, protected, rows = p, p, []
    for k in range(65):
        q = conditional_power(p, edge_record, weights, k)
        qp = conditional_power(p, parity_record, weights, k)
        assert q == ordinary and qp == protected  # Actual iterates vs closed form.
        t = F(1, 2)**k
        denominator = 1+3*t+2*t*t
        wrong = sum(q[key] for key in p if score[key] > 0)
        protected_wrong = sum(qp[key] for key in p if score[key] > 0)
        assert wrong == (3*t+2*t*t)/denominator <= 5*t
        assert expectation(q, score) == (54*t+54*t*t)/denominator
        assert expectation(q, score) <= 27*wrong
        assert protected_wrong == F(1, 2)+t*t/(1+2*t*t)
        assert expectation(qp, score) == 9+27*t*t/(1+2*t*t)
        coherent_lift(q)
        coherent_lift(qp)
        if k in (0, 1, 2, 4, 8, 16, 32, 64):
            rows.append(dict(round=k, wrong_probability=str(wrong),
                             expected_defect=str(expectation(q, score)),
                             wrong_probability_decimal=float(wrong),
                             expected_defect_decimal=float(expectation(q, score)),
                             parity_protected_wrong_probability=str(protected_wrong),
                             parity_protected_defect=str(expectation(qp, score))))
        ordinary = conditional_power(ordinary, edge_record, weights, 1)
        protected = conditional_power(protected, parity_record, weights, 1)
    # Nonuniform full-support candidate priors test the general odds bound.
    for sigma in TRANSPORTS.values():
        prior = {tau: F(i, 21) for i, tau in enumerate(CANDIDATES, 1)}
        w = {tau: 1-census_defect(sigma, tau)/36 for tau in prior}
        h = dict.fromkeys(prior, 0)
        odds = (1-prior[sigma])/prior[sigma]
        for k in (0, 1, 3, 8, 32):
            q = conditional_power(prior, h, w, k)
            assert sum(q[tau] for tau in q if tau != sigma) <= odds*F(1, 2)**k
    return dict(edges=len(TRANSPORTS), candidates_per_edge=6,
                defect_multiplicities={"0": 1, "18": 3, "27": 2},
                protected_edge_floor=str(edge_floor),
                protected_edge_and_relative_parity_floor=str(parity_floor),
                rounds=rows)


def audit_growing_bank():
    """Every old record receives another selection pass at each new arrival.

    This is a growing inference bank, not the native causal birth process.
    The analytic all-N proof is in PROTECTED_SELECTION_CONVERGENCE.md.
    """
    total_error, total_variance, rows = F(0), F(0), []
    for n in range(1, 257):
        age = n-1
        t = F(1, 2)**age
        error = (3*t+2*t*t)/(1+3*t+2*t*t)
        total_error += error
        total_variance += error*(1-error)
        assert total_error <= 10*(1-F(1, 2)**n) < 10
        # Under within-stage independent candidate sampling, this is E[W_N^2].
        second_moment = total_variance+total_error**2
        assert second_moment <= total_error+total_error**2 < 110
        if n in (1, 2, 4, 8, 16, 32, 64, 128, 256):
            rows.append(dict(records=n, expected_wrong_count=float(total_error),
                             expected_wrong_fraction=float(total_error/n),
                             wrong_count_second_moment=float(second_moment)))
    return dict(algorithm="one new uniform-prior record, one pass per old record per stage",
                all_rank_expected_wrong_count_bound=10,
                all_rank_second_moment_bound_under_independent_sampling=110,
                finite_checks=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 256
    births, census, bank = audit_birth_floors(), audit_census(), audit_growing_bank()
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/protected_selection_convergence.py",
             "scripts/microscopic_selection_audit.py", "scripts/harmonic_born_geometry_drift.py",
             "scripts/harmonic_child_nonuniformity.py", "scripts/chiral_growth_generalization.py",
             "UnifiedTheory/Audit/KFCausalCSpecProtectedSelectionConvergence.lean",
             "UnifiedTheory/Audit/KFCausalCSpecBridgeDefectObservable.lean",
             "UnifiedTheory/Audit/KFCausalCSpecCensusRecovery.lean",
             "UnifiedTheory/Audit/KFCausalCSpecGlobalization.lean"]
    result = dict(scope="finite selection feasibility and census reconstruction; no GR emergence",
                  arithmetic="exact Fraction identities; 256-bit Arb scalar coherent/Born lifts",
                  source_sha256={path: hashlib.sha256((root/path).read_bytes()).hexdigest()
                                 for path in paths},
                  birth_floors=births, bridge_census=census, growing_bank=bank)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(births["summary"], indent=2))
    print("Bridge census: exact convergence through 64 rounds; protected parity floor = 9.")
    print("Growing bank: exact first/second moments checked through 256 records.")
    print("All record laws, sharp floors, iterative identities, and amplitude lifts passed.")


if __name__ == "__main__":
    main()
