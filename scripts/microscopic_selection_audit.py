#!/usr/bin/env python3
"""Selection audit: centered phases versus a covariant insertion reference.

Exact rational combinatorics and Arb complex balls. The insertion law is an
explicit alternative, not a derived physical law: uniformly choose a linear
extension and a cut, then forget the extension. Probabilities are aggregated
onto unlabeled children before a coherent/Born lift is constructed.

The script checks finite identities; the all-rank stochastic arguments and
the phase-only obstruction are in MICROSCOPIC_SELECTION_PRINCIPLE.md.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
import time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import flint
from flint import acb, arb, ctx

from chiral_growth_generalization import (
    canonical_relation_key, downsets, exhaustive_unlabeled_posets,
    permutation_edge_maps,
)
from harmonic_child_nonuniformity import (
    aggregated_child_amplitudes, child_relation, harmonic_pair_coupling,
)
from harmonic_born_geometry_drift import ball, describe, shell_probabilities


def insertion_probabilities(parent):
    """P(D) = e(D)e(C minus D)/((n+1)e(C)); e counts linear extensions."""
    n = len(parent)
    full = (1 << n) - 1
    predecessors = [sum(1 << i for i in range(n) if parent[i] & (1 << j))
                    for j in range(n)]

    @lru_cache(None)
    def extensions(mask):
        if not mask:
            return 1
        return sum(extensions(mask ^ (1 << j)) for j in range(n)
                   if mask & (1 << j) and not predecessors[j] & mask)

    total = extensions(full)
    assert total > 0
    probabilities = {past: Fraction(extensions(past)*extensions(full ^ past),
                                    (n+1)*total) for past in downsets(parent)}
    assert sum(probabilities.values()) == 1
    assert all(p > 0 for p in probabilities.values())
    for j in range(n+1):
        assert sum(p for past, p in probabilities.items()
                   if bin(past).count("1") == j) == Fraction(1, n+1)
    return probabilities


def direct_extension_cut_counts(parent):
    """Independent small-rank enumeration of the reference experiment."""
    n = len(parent)
    counts = {past: 0 for past in downsets(parent)}
    total = 0
    for order in itertools.permutations(range(n)):
        position = {v: j for j, v in enumerate(order)}
        if any(position[i] > position[j] for i in range(n) for j in range(n)
               if parent[i] & (1 << j)):
            continue
        past = 0
        counts[past] += 1
        total += 1
        for v in order:
            past |= 1 << v
            counts[past] += 1
            total += 1
    return {past: Fraction(count, total) for past, count in counts.items()}


def tilt_reference(reference, weights):
    """Variational selector for exp(-S)=weights, exact for rational weights."""
    assert set(reference) == set(weights) and all(w > 0 for w in weights.values())
    partition = sum(reference[key]*weights[key] for key in reference)
    result = {key: reference[key]*weights[key]/partition for key in reference}
    assert sum(result.values()) == 1 and all(p > 0 for p in result.values())
    return result


def coherent_lift(probabilities, chirality=1):
    """Binary splitting gives exactly the requested Born probabilities.

    Canonical integer child keys provide a relabeling-invariant ordering.
    This order is an extra phase convention. It is not asserted to follow
    from a causal action or to leave interference observables unchanged.
    """
    keys = sorted(probabilities)
    residual = Fraction(1)
    continuing = acb(1)
    amplitudes = {}
    for key in keys[:-1]:
        q = probabilities[key]/residual
        assert 0 < q < 1
        a = acb(ball(q), chirality*ball(q*(1-q)).sqrt())
        amplitudes[key] = continuing*a
        continuing *= 1-a
        residual -= probabilities[key]
    amplitudes[keys[-1]] = continuing
    assert (sum(amplitudes.values(), acb(0))-1).contains(0)
    for key, amplitude in amplitudes.items():
        assert (abs(amplitude)**2-ball(probabilities[key])).contains(0)
    return amplitudes


def shell_amplitudes(raw):
    k = len(raw)
    if k == 1:
        return {next(iter(raw)): acb(1)}
    z = sum((acb(ball(x), ball(y)) for x, y in raw.values()), acb(0))
    u = arb(1)/k
    normalized = {key: acb(ball(x), ball(y))/z for key, (x, y) in raw.items()}
    excess = sum((abs(a-u)**2 for a in normalized.values()), arb(0))
    scale = ((1-u)/excess).sqrt()
    result = {key: u+scale*(a-u) for key, a in normalized.items()}
    assert (sum(result.values(), acb(0))-1).contains(0)
    assert (sum((abs(a)**2 for a in result.values()), arb(0))-1).contains(0)
    return result


def relabel(parent, permutation):
    result = [0]*len(parent)
    for i, row in enumerate(parent):
        for j in range(len(parent)):
            if row & (1 << j):
                result[permutation[i]] |= 1 << permutation[j]
    return tuple(result)


def census(max_rank):
    summaries = {}
    rows = []
    for n, parents in exhaustive_unlabeled_posets(max_rank).items():
        maps = permutation_edge_maps(n+1)
        cache = {}
        for parent in parents:
            raw_p = insertion_probabilities(parent)
            assert raw_p == direct_extension_cut_counts(parent)
            # A nonconstant order-dependent perturbation tests the sufficient
            # bound. This score is an audit example, not a selected action.
            weights = {}
            for past in raw_p:
                size = bin(past).count("1")
                maximal = sum(1 for i in range(n)
                              if past & (1 << i) and not parent[i] & past)
                weights[past] = 1+Fraction(maximal, size+1)
                assert 1 <= weights[past] < 2
            tilted_raw = tilt_reference(raw_p, weights)
            for j in range(n+1):
                mass = sum(p for past, p in tilted_raw.items()
                           if bin(past).count("1") == j)
                assert Fraction(1, 2*(n+1)) <= mass <= Fraction(2, n+1)
            tilted_ancestors = sum(p*bin(past).count("1") for past, p in tilted_raw.items())
            assert Fraction(n, 4) <= tilted_ancestors <= Fraction(3*n, 4)
            # Explicit nontrivial relabeling, on top of the combinatorial proof.
            permutation = tuple(reversed(range(n)))
            relabeled_p = insertion_probabilities(relabel(parent, permutation))
            for past, probability in raw_p.items():
                changed = sum(1 << permutation[i] for i in range(n)
                              if past & (1 << i))
                assert relabeled_p[changed] == probability
            p = {}
            sizes = {}
            for past, probability in raw_p.items():
                key = canonical_relation_key(child_relation(parent, past), maps)
                p[key] = p.get(key, Fraction(0))+probability
                size = bin(past).count("1")
                assert key not in sizes or sizes[key] == size
                sizes[key] = size
            assert sum(p.values()) == 1
            assert all(0 < probability <= Fraction(1, n+1) for probability in p.values())
            assert sum(p[key]*sizes[key] for key in p) == Fraction(n, 2)
            positive_lift = coherent_lift(p)
            negative_lift = coherent_lift(p, -1)
            for key in p:
                assert (positive_lift[key].conjugate()-negative_lift[key]).contains(0)
            if n:
                timid = canonical_relation_key(child_relation(parent, (1 << n)-1), maps)
                assert p[timid] == Fraction(1, n+1)
            raw = aggregated_child_amplitudes(parent, harmonic_pair_coupling(n), 1, maps, cache)
            shell = shell_amplitudes(raw)
            old_p, _ = shell_probabilities(raw)
            for key in shell:
                assert (abs(shell[key])**2-old_p[key]).contains(0)
            k = len(shell)
            u = arb(1)/k
            phase_rows = []
            for phase_name, phase in (("positive", acb(1)), ("negative", acb(-1)),
                                      ("quarter_turn", acb(0, 1))):
                corrected = {key: u+phase*(a-u) for key, a in shell.items()}
                probabilities = {key: abs(a)**2 for key, a in corrected.items()}
                assert (sum(corrected.values(), acb(0))-1).contains(0)
                assert (sum(probabilities.values(), arb(0))-1).contains(0)
                for key in p:
                    # A strict bound fails only for trivial exact-boundary
                    # cases; containment of zero also accepts the equality.
                    slack = 4*u-abs(probabilities[key]-old_p[key])
                    assert slack >= 0 or slack.contains(0)
                mean_missing = sum((probabilities[key]*(n-sizes[key])
                                    for key in p), arb(0))
                phase_rows.append({"phase": phase_name,
                                   "expected_missing": describe(mean_missing)})
            rows.append({"rank": n, "successor_masks": list(parent),
                         "children": len(p), "insertion_expected_missing": str(Fraction(n, 2)),
                         "bounded_tilt_expected_missing": str(n-tilted_ancestors),
                         "harmonic_phases": phase_rows})
        summaries[str(n)] = len(parents)
    return {"parents_per_rank": summaries, "rows": rows,
            "checks": ["exact extension formula versus permutation enumeration",
                       "uniform ancestor count on every parent",
                       "relabeling covariance", "full physical child support",
                       "prescribed Born probabilities and coherent normalization",
                       "chirality conjugation", "centered-phase probability bound",
                       "bounded order-dependent tilt: cut floor and extensive pair bounds"]}


def chain_phase_audit(n, cutoff=64):
    """Large-chain phase comparison with certified omitted-tail errors."""
    h = sum((arb(1)/j for j in range(1, n+1)), arb(0))
    lam = arb(2) if n == 1 else 1+h/(2*(n-1))
    empty = lam**(-n*(n-1))
    kept = min(n, cutoff)
    ratio = arb(1)
    factor = lam**(-2*(n-1))
    ratios = []
    first = second = first_missed = second_missed = arb(0)
    for k in range(kept):
        ratios.append(ratio)
        first += ratio
        second += ratio*ratio
        first_missed += k*ratio
        second_missed += k*ratio*ratio
        ratio *= factor
        factor *= lam*lam
    omitted = n-kept
    if omitted:
        first += arb(0, (omitted*ratio).upper())
        second += arb(0, (omitted*ratio*ratio).upper())
        first_missed += arb(0, (n*omitted*ratio).upper())
        second_missed += arb(0, (n*omitted*ratio*ratio).upper())
    z = acb(empty, first)
    d = empty*empty+first*first
    u = arb(1)/(n+1)
    scale = ((1-u)/((empty*empty+second)/d-u)).sqrt()
    # Weighted raw moments produce all n+1 probabilities without allocating
    # them: sum k |v+t A_k|^2, with k = n-ancestorCount.
    moment = acb(n*empty, first_missed)
    square_moment = n*empty*empty+second_missed
    result = {"rank": n, "phases": []}
    for name, phase in (("positive", acb(1)), ("negative", acb(-1)),
                        ("quarter_turn", acb(0, 1))):
        v = (1-phase*scale)*u
        t = phase*scale/z
        timid = abs(v+t*acb(0, 1))**2
        missing = (abs(v)**2*(n*(n+1)//2)+abs(t)**2*square_moment
                   +2*(v.conjugate()*t*moment).real)
        # Some phases give deterministic rank-one boundaries; normalization
        # still holds, but full support is not claimed for arbitrary phases.
        assert all(x > 0 or x.contains(0) for x in (timid, 1-timid, missing))
        result["phases"].append({"phase": name, "escape": describe(1-timid),
                                  "n_times_escape": describe(n*(1-timid)),
                                  "expected_missing": describe(missing),
                                  "expected_missing_fraction": describe(missing/n)})
    return result


def locality_audit():
    anti2 = (0, 0)
    one = (0,)
    p = insertion_probabilities(anti2)
    reduced = insertion_probabilities(one)
    ratio = p[1]/p[0]
    reduced_ratio = reduced[1]/reduced[0]
    assert ratio == Fraction(1, 2) and reduced_ratio == 1
    # Two specified natural-labeling histories to a 2-chain plus isolated point.
    chain2 = (2, 0)
    via_antichain = Fraction(1, 2)*p[1]
    via_chain = Fraction(1, 2)*insertion_probabilities(chain2)[0]
    assert via_antichain == Fraction(1, 12) and via_chain == Fraction(1, 6)
    harmonic_before = harmonic_pair_coupling(3)**2
    harmonic_after = harmonic_pair_coupling(2)**2
    assert harmonic_before == Fraction(1225, 576)
    assert harmonic_after == Fraction(49, 16)
    return {"raw_Bell_causality": "fails",
            "antichain2_singleton_to_empty_ratio": str(ratio),
            "spectator_deleted_ratio": str(reduced_ratio),
            "strict_natural_labeling_probability_covariance": "fails",
            "chain_plus_point_path_via_antichain": str(via_antichain),
            "chain_plus_point_path_via_chain": str(via_chain),
            "harmonic_raw_Bell_causality": {
                "status": "fails for the rank-running schedule",
                "parent": "two-chain plus isolated spectator",
                "alternatives": "whole two-chain precursor versus empty precursor",
                "imaginary_ratio_before_deletion": str(harmonic_before),
                "imaginary_ratio_after_deletion": str(harmonic_after),
                "scope": "raw signature law; fixed-coupling Bell theorem does not cover rank running"},
            "scope": "parent isomorphism covariance holds; stronger path and Bell conditions do not"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-rank", type=int, default=5)
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.max_rank <= 5 or args.precision < 128:
        parser.error("require 0 <= max-rank <= 5 and precision >= 128")
    ctx.prec = args.precision
    start = time.perf_counter()
    finite = census(args.max_rank)
    print("Exact finite census passed:", finite["parents_per_rank"], flush=True)
    chain_rows = [chain_phase_audit(n) for n in (8, 32, 128, 1000, 10000, 100000)]
    # A second independent formula checks the large-chain moment reduction
    # on the first five chains against full exact quotient enumeration.
    for n in range(1, 6):
        parent = tuple(sum(1 << j for j in range(i+1, n)) for i in range(n))
        maps = permutation_edge_maps(n+1)
        raw = aggregated_child_amplitudes(parent, harmonic_pair_coupling(n), 1, maps, {})
        shell = shell_amplitudes(raw)
        sizes = {canonical_relation_key(child_relation(parent, past), maps): bin(past).count("1")
                 for past in downsets(parent)}
        specialized = chain_phase_audit(n)
        for row, phase in zip(specialized["phases"], (acb(1), acb(-1), acb(0, 1))):
            actual = sum((abs(arb(1)/(n+1)+phase*(a-arb(1)/(n+1)))**2*(n-sizes[key])
                          for key, a in shell.items()), arb(0))
            assert (actual-arb(row["expected_missing"]["enclosure"])).contains(0)
    source = Path(__file__).resolve().parent
    names = [Path(__file__).name, "harmonic_born_geometry_drift.py",
             "harmonic_child_nonuniformity.py", "chiral_growth_generalization.py"]
    result = {"scope": "alternative selection audit; no derivation of physical 4D dynamics",
              "precision_bits": args.precision, "python_version": platform.python_version(),
              "python_flint_version": flint.__version__,
              "source_sha256": {name: hashlib.sha256((source/name).read_bytes()).hexdigest()
                                for name in names},
              "finite": finite, "chain_phases": chain_rows, "locality": locality_audit(),
              "insertion_limit": {"ordering_fraction": "1/2 almost surely (analytic)",
                                  "variance_at_rank_N": "(2*N+5)/(18*N*(N-1))",
                                  "any_fixed_N_birth_history_probability_upper": "1/N!",
                                  "continuum_geometry": "not established"},
              "elapsed_seconds": time.perf_counter()-start}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print("Large-chain moment checks and explicit locality counterexamples passed")
    print("Wrote", args.output)


if __name__ == "__main__":
    main()
