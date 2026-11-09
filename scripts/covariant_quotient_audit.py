#!/usr/bin/env python3
"""Finite covariant complex-percolation benchmark and quotient-metric audit.

Complex percolation is an existing model, not a new GUT. The inherited norm
on grouped precursor amplitudes is compared with the flat grouped norm.
Geometry checks concern the recorded Born law, not an unmeasured quantum
event pre-measure or its unproved extension to infinite covariant events.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path

from chiral_growth_generalization import (
    canonical_relation_key, downsets, exhaustive_unlabeled_posets,
    maximal_count, permutation_edge_maps, predecessor_masks, transitive_closure,
)
from harmonic_child_nonuniformity import child_relation, gaussian_add

ZERO, ONE = (F(0), F(0)), (F(1), F(0))
A, B = (F(1, 2), F(1, 2)), (F(1, 2), F(-1, 2))


def mul(z, w):
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


@lru_cache(None)
def power(z, n):
    if n == 0:
        return ONE
    return mul(power(z, n-1), z)


def norm2(z):
    return z[0]**2+z[1]**2


def gsum(values):
    result = ZERO
    for value in values:
        result = gaussian_add(result, value)
    return result


def encode(z):
    return [str(z[0]), str(z[1])]


def amplitude(parent, past):
    omega = bin(past).count("1")
    return mul(power(A, maximal_count(parent, past)), power(B, len(parent)-omega))


def restrict(parent, indices):
    return tuple(sum(1 << j for j, target in enumerate(indices)
                     if parent[source] & (1 << target)) for source in indices)


def restrict_mask(mask, indices):
    return sum(1 << j for j, source in enumerate(indices) if mask & (1 << source))


def audit_parents():
    rows, summary = [], {}
    bell_checks, path_checks = 0, 0
    for n, parents in exhaustive_unlabeled_posets(5).items():
        maps = permutation_edge_maps(n+1)
        counts = dict(parents=len(parents), flat_grouped_Born_failure=0)
        for parent in parents:
            pasts = list(downsets(parent))
            raw = {past: amplitude(parent, past) for past in pasts}
            assert gsum(raw.values()) == ONE
            assert sum(norm2(z) for z in raw.values()) == 1
            assert all(z != ZERO for z in raw.values())
            # Uniform raw-amplitude cap used in the analytic variation obstruction.
            assert n == 0 or all(norm2(z) <= F(1, 2) for z in raw.values())
            predecessors = predecessor_masks(parent)
            proposed = defaultdict(lambda: ZERO)
            proposed_mass = F(0)
            for links in range(1 << n):
                past = links
                for j in range(n):
                    if links & (1 << j):
                        past |= predecessors[j]
                count = bin(links).count("1")
                z = mul(power(A, count), power(B, n-count))
                proposed[past] = gaussian_add(proposed[past], z)
                proposed_mass += norm2(z)
            # Independent coherent grouping of proposed bonds into closed precursors.
            assert dict(proposed) == raw and proposed_mass == 1
            groups = defaultdict(list)
            for past in pasts:
                key = canonical_relation_key(child_relation(parent, past), maps)
                groups[key].append(raw[past])
            aggregate = {key: gsum(zs) for key, zs in groups.items()}
            assert all(len(set(zs)) == 1 for zs in groups.values())
            quotient_mass = sum(norm2(aggregate[key])/len(groups[key]) for key in groups)
            flat_mass = sum(norm2(z) for z in aggregate.values())
            excess = sum(len(zs)*(len(zs)-1)*norm2(zs[0]) for zs in groups.values())
            assert gsum(aggregate.values()) == ONE and quotient_mass == 1
            assert flat_mass-quotient_mass == excess
            assert (flat_mass > 1) == any(len(zs) > 1 for zs in groups.values())
            counts["flat_grouped_Born_failure"] += flat_mass > 1
            # Every pair of precursors, with their actual common spectators deleted.
            for first, second in itertools.product(pasts, repeat=2):
                union = first | second
                indices = [i for i in range(n) if union & (1 << i)]
                reduced = restrict(parent, indices)
                a1 = amplitude(reduced, restrict_mask(first, indices))
                a2 = amplitude(reduced, restrict_mask(second, indices))
                assert mul(raw[first], a2) == mul(raw[second], a1)
                bell_checks += 1
            # Every natural birth ordering has the same unaggregated amplitude.
            relations = sum(bin(row).count("1") for row in parent)
            covers = sum(maximal_count(parent, past) for past in predecessors)
            invariant = mul(power(A, covers), power(B, comb(n, 2)-relations))
            for order in itertools.permutations(range(n)):
                position = {v: j for j, v in enumerate(order)}
                if any(position[i] > position[j] for i in range(n) for j in range(n)
                       if parent[i] & (1 << j)):
                    continue
                product = ONE
                for rank, newborn in enumerate(order):
                    indices = list(order[:rank])
                    prefix = restrict(parent, indices)
                    past = restrict_mask(predecessors[newborn], indices)
                    product = mul(product, amplitude(prefix, past))
                assert product == invariant
                path_checks += 1
            rows.append(dict(rank=n, successor_masks=list(parent),
                             precursor_slots=len(pasts), unlabeled_children=len(groups),
                             flat_grouped_Born_mass=str(flat_mass),
                             inherited_quotient_Born_mass=str(quotient_mass),
                             largest_raw_Born_probability=str(max(norm2(z) for z in raw.values())),
                             exact_flat_excess=str(excess)))
        summary[str(n)] = counts
    return dict(summary=summary, parents=rows, Bell_pair_checks=bell_checks,
                natural_labeling_path_checks=path_checks)


def audit_rank_two():
    chain, anti = (2, 0), (0, 0)
    chain_cut = {j: F(0) for j in range(3)}
    anti_cut = chain_cut.copy()
    for parent, cuts in ((chain, chain_cut), (anti, anti_cut)):
        for past in downsets(parent):
            cuts[bin(past).count("1")] += norm2(amplitude(parent, past))
    assert chain_cut == {0: F(1, 4), 1: F(1, 4), 2: F(1, 2)}
    assert anti_cut == {0: F(1, 4), 1: F(1, 2), 2: F(1, 4)}
    grouped = [power(B, 2), gaussian_add(mul(A, B), mul(A, B)), power(A, 2)]
    assert sum(norm2(z) for z in grouped) == F(3, 2)
    assert sum(norm2(z)/m for z, m in zip(grouped, (1, 2, 1))) == 1
    return dict(chain_cut_law=[str(chain_cut[j]) for j in range(3)],
                antichain_cut_law=[str(anti_cut[j]) for j in range(3)],
                antichain_grouped_amplitudes=[encode(z) for z in grouped],
                multiplicities=[1, 2, 1], flat_mass="3/2", inherited_mass="1")


def audit_recorded_geometry():
    rows = []
    configurations = 0
    for n in range(2, 7):
        edges = list(itertools.combinations(range(n), 2))
        probabilities = (F(1, 2),) if n == 6 else (F(1, 5), F(1, 2), F(4, 5))
        for p in probabilities:
            weights = {k: p**k*(1-p)**(len(edges)-k) for k in range(len(edges)+1)}
            expected_missing = F(0)
            pair_missing = dict.fromkeys(edges, F(0))
            mass = F(0)
            for mask in range(1 << len(edges)):
                relation = [0]*n
                for bit, (i, j) in enumerate(edges):
                    if mask & (1 << bit):
                        relation[i] |= 1 << j
                closed = transitive_closure(tuple(relation))
                probability = weights[bin(mask).count("1")]
                mass += probability
                for i, j in edges:
                    if not closed[i] & (1 << j):
                        pair_missing[i, j] += probability
                        expected_missing += probability
                configurations += 1
            assert mass == 1
            for (i, j), probability in pair_missing.items():
                assert probability <= (1-p)*(1-p*p)**(j-i-1)
            exact_envelope = sum((n-d)*(1-p)*(1-p*p)**(d-1) for d in range(1, n))
            assert expected_missing <= exact_envelope < n*(1-p)/(p*p)
            rows.append(dict(events=n, bond_probability=str(p),
                             exact_expected_missing_pairs=str(expected_missing),
                             exact_expected_ordering_fraction=str(1-expected_missing/comb(n, 2)),
                             two_step_envelope=str(exact_envelope)))
    return dict(scope="recorded Born process only", edge_configurations=configurations, rows=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parents, rank_two = audit_parents(), audit_rank_two()
    geometry = audit_recorded_geometry()
    root = Path(__file__).resolve().parent.parent
    paths = ["scripts/covariant_quotient_audit.py", "scripts/chiral_growth_generalization.py",
             "scripts/harmonic_child_nonuniformity.py",
             "UnifiedTheory/Audit/KFCausalBornCovariantQuotient.lean",
             "UnifiedTheory/Audit/KFCausalSetTransitionEdges.lean"]
    result = dict(scope="finite covariant benchmark and inherited quotient norm; GUT uncompleted",
                  arithmetic="exact rational real and imaginary parts; no sampled path claims",
                  model="known complex percolation at a=(1+i)/2, b=(1-i)/2",
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},
                  parents=parents, rank_two=rank_two, recorded_geometry=geometry)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(parents["summary"], indent=2))
    print("Exact Bell pairs:", parents["Bell_pair_checks"],
          "; natural-labeling paths:", parents["natural_labeling_path_checks"])
    print("Recorded Born geometry:", geometry["edge_configurations"], "exact edge configurations.")
    print("Coherent and inherited Born normalization pass; flat quotient excess certified.")


if __name__ == "__main__":
    main()
