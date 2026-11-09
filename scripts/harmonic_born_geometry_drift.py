#!/usr/bin/env python3
"""Audit the actual canonical harmonic Born law, including its infinite chain atom.

Finite parents are aggregated by unlabeled child before the positive radial
correction, matching KFCausalBornShellGeneralLaw. Raw amplitudes use exact
Q(i); python-flint Arb encloses the square roots and probabilities.

The chain reduction uses n+1 distinct children with raw amplitudes
1, i, i*lambda^2, ..., i*lambda^(n*(n-1)). Its truncated sums have explicit
outward error bounds; no Monte Carlo or fitted growth law is used.

The infinite-chain lower bound uses the analytic bound proved in the companion
note: escape(n) <= 128/n^2 for n >= 8. Interval arithmetic certifies the finite
prefix; the all-rank inequality is mathematical input to that tail certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

from chiral_growth_generalization import (
    canonical_relation_key,
    downsets,
    exhaustive_unlabeled_posets,
    permutation_edge_maps,
)
from harmonic_child_nonuniformity import (
    aggregated_child_amplitudes,
    child_relation,
    harmonic_pair_coupling,
)


def ball(x: Fraction | int) -> arb:
    if isinstance(x, Fraction):
        return arb(x.numerator) / x.denominator
    return arb(x)


def describe(x: arb) -> dict[str, str]:
    return {"enclosure": str(x), "midpoint": str(x.mid())}


def shell_probabilities(amplitudes: dict[int, tuple[Fraction, Fraction]]):
    """Exact rational coherent division, followed by Arb radial completion."""
    keys = list(amplitudes)
    k = len(keys)
    if k == 1:
        return {keys[0]: arb(1)}, {"coherent_error": arb(0), "born_error": arb(0)}
    zr = sum((a[0] for a in amplitudes.values()), Fraction(0))
    zi = sum((a[1] for a in amplitudes.values()), Fraction(0))
    d = zr * zr + zi * zi
    assert d > 0
    raw = {
        key: ((a[0] * zr + a[1] * zi) / d, (a[1] * zr - a[0] * zi) / d)
        for key, a in amplitudes.items()
    }
    u = Fraction(1, k)
    excess = sum(((x - u) ** 2 + y * y for x, y in raw.values()), Fraction(0))
    assert excess > 0
    scale = ball((1 - u) / excess).sqrt()
    corrected = {key: (ball(u) + scale * ball(x - u), scale * ball(y))
                 for key, (x, y) in raw.items()}
    probabilities = {key: x*x + y*y for key, (x, y) in corrected.items()}
    assert all(p > 0 for p in probabilities.values())
    re_error = sum((a[0] for a in corrected.values()), arb(0)) - 1
    im_error = sum((a[1] for a in corrected.values()), arb(0))
    born_error = sum(probabilities.values(), arb(0)) - 1
    assert re_error.contains(0) and im_error.contains(0) and born_error.contains(0)
    return probabilities, {"coherent_error": abs(re_error) + abs(im_error),
                           "born_error": abs(born_error)}


def order_fraction(parent) -> Fraction:
    n = len(parent)
    return Fraction(sum(bin(row).count("1") for row in parent), n*(n-1)//2) if n > 1 else Fraction(0)


def census(max_rank: int):
    """Exhaustive finite diagnostics, not a Hauptvermutung certificate."""
    rows = []
    rank_summary = {}
    for n, parents in exhaustive_unlabeled_posets(max_rank).items():
        maps = permutation_edge_maps(n + 1)
        cache = {}
        signs = {"positive": 0, "negative": 0, "unresolved_or_zero": 0}
        for parent in parents:
            lam = harmonic_pair_coupling(n)
            raw = aggregated_child_amplitudes(parent, lam, 1, maps, cache)
            probs, _ = shell_probabilities(raw)
            # Independent exact checks of the all-parent and unique-maximum
            # counting envelopes used in the stronger analytic collapse proof.
            envelope_terms = [Fraction(math.comb(n, k))*lam**(-k*(2*n-k-1))
                              for k in range(n+1)]
            full_magnitude = lam**(n*(n-1))
            assert all(x == 0 or y == 0 for x, y in raw.values())
            relative_l1 = sum((abs(x)+abs(y) for x, y in raw.values()), Fraction(0))/full_magnitude
            assert relative_l1 <= sum(envelope_terms)
            if n > 0 and sum(row == 0 for row in parent) == 1:
                unique_tail = sum((Fraction(k, n)*t for k, t in enumerate(envelope_terms)), Fraction(0))
                assert relative_l1-1 <= unique_tail
            children = {}
            for precursor in downsets(parent):
                child = child_relation(parent, precursor)
                key = canonical_relation_key(child, maps)
                children[key] = (child, bin(precursor).count("1"))
            assert set(children) == set(probs)
            if n < 2:
                continue
            r = order_fraction(parent)
            defects = {key: (order_fraction(child)-Fraction(1, 10))**2
                       for key, (child, _) in children.items()}
            drift = sum((probs[key]*ball(value) for key, value in defects.items()), arb(0))
            drift -= ball((r-Fraction(1, 10))**2)
            sign = "positive" if drift > 0 else "negative" if drift < 0 else "unresolved_or_zero"
            signs[sign] += 1
            expected_fraction = sum((probs[key]*ball(order_fraction(child))
                                     for key, (child, _) in children.items()), arb(0))
            expected_ancestors = sum((probs[key]*count for key, (_, count) in children.items()), arb(0))
            drift_identity = expected_fraction-ball(r)-ball(Fraction(2, n+1))*(expected_ancestors/n-ball(r))
            assert drift_identity.contains(0)
            rows.append({"rank": n, "successor_masks": list(parent), "children": len(probs),
                         "ordering_fraction": str(r), "squared_4d_proxy_drift": describe(drift),
                         "sign": sign, "expected_ancestor_fraction": describe(expected_ancestors/n)})
        rank_summary[str(n)] = {"parents": len(parents), "drift_signs": signs}
    return {"scope": "(ordering_fraction - 1/10)^2 is a finite diagnostic, not the Gate-3 defect",
            "uniform_raw_envelope_checks": "passed on every enumerated parent",
            "ranks": rank_summary, "parents": rows}


def envelope_audit():
    """Exact positive sums bounding all parents and all unique-max parents.

    These evaluations corroborate the analytic estimates; a finite scan does
    not establish the all-rank uniform bounds or almost-sure collapse.
    """
    rows = []
    for n in (8, 16, 64, 256, 1024, 10000, 100000):
        h = sum((arb(1)/j for j in range(1, n+1)), arb(0))
        lam = 1+h/(2*(n-1))
        factor = lam**(-2*(n-1))
        lam_sq = lam*lam
        term = arb(1)
        total = arb(1)
        unique_tail = arb(0)
        for k in range(n):
            term *= arb(n-k)/(k+1)*factor
            factor *= lam_sq
            total += term
            unique_tail += arb(k+1)/n*term
        rows.append({"parent_rank": n, "all_parent_l1_upper": describe(total),
                     "n_times_unique_max_tail_upper": describe(n*unique_tail)})
    return rows


def chain_step(n: int, harmonic: arb, cutoff: int = 64):
    """Arb enclosure of the canonical shell law on an n-chain.

    Scale all raw amplitudes by the largest magnitude. In the imaginary
    coordinate, retain k=0,...,cutoff-1 (j=n-k); the omitted terms are each
    bounded by the next term. Both total first and second moments get an
    outward interval error. The real empty-precursor term is evaluated directly.
    """
    lam = arb(2) if n == 1 else 1 + harmonic/(2*(n-1))
    empty = lam ** (-n*(n-1))
    kept = min(n, cutoff)
    ratio = arb(1)
    step_ratio = lam ** (-2*(n-1))
    lam_sq = lam*lam
    first = arb(0)
    second = arb(0)
    for _ in range(kept):
        first += ratio
        second += ratio*ratio
        ratio *= step_ratio
        step_ratio *= lam_sq
    omitted = n-kept
    if omitted:
        first += arb(0, (omitted*ratio).upper())
        second += arb(0, (omitted*ratio*ratio).upper())
    d = empty*empty + first*first
    u = arb(1)/(n+1)
    excess = (empty*empty + second)/d - u
    assert excess > 0
    scale = ((1-u)/excess).sqrt()
    re = u + scale*(first/d-u)
    im = scale*empty/d
    timid = re*re + im*im
    assert timid > 0 and (1-timid) > 0
    return timid, 1-timid


def chain_audit(max_rank: int, cutoff: int):
    harmonic = arb(0)
    survival = arb(1)
    snapshots = []
    checkpoints = {1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, max_rank}
    for n in range(1, max_rank+1):
        harmonic += arb(1)/n
        timid, escape = chain_step(n, harmonic, cutoff)
        survival *= timid
        if n >= 8:
            assert escape < arb(128)/(n*n)
        if n in checkpoints:
            snapshots.append({"parent_rank": n, "escape_probability": describe(escape),
                              "n_squared_escape": describe(n*n*escape),
                              "finite_chain_probability": describe(survival)})
    # Sum_{n>N} n^-2 <= 1/N and product(1-e_n) >= 1-sum(e_n).
    lower = survival*(1-arb(128)/max_rank) if max_rank > 128 else arb(0)
    return {"cutoff": cutoff, "max_parent_rank": max_rank, "snapshots": snapshots,
            "finite_prefix_survival": describe(survival),
            "infinite_chain_probability_lower": describe(lower),
            "infinite_chain_probability_upper": describe(survival),
            "tail_input": "escape(n) <= 128/n^2 for every n >= 8; see companion analytic proof"}


def self_check():
    """Independent exact quotient enumeration validates the chain reduction."""
    for n in range(1, 6):
        parent = tuple(sum(1 << j for j in range(i+1, n)) for i in range(n))
        maps = permutation_edge_maps(n+1)
        raw = aggregated_child_amplitudes(parent, harmonic_pair_coupling(n), 1, maps, {})
        negative = aggregated_child_amplitudes(parent, harmonic_pair_coupling(n), -1, maps, {})
        assert negative == {key: (a[0], -a[1]) for key, a in raw.items()}
        assert len(raw) == n+1
        probs, _ = shell_probabilities(raw)
        target = canonical_relation_key(child_relation(parent, (1 << n)-1), maps)
        h = sum((arb(1)/j for j in range(1, n+1)), arb(0))
        specialized, _ = chain_step(n, h)
        assert (specialized-probs[target]).contains(0)
        if n == 1:
            assert specialized.contains(arb(1)/2)
    # A truncated enclosure must overlap a direct full sum at larger ranks.
    for n in (128, 257, 1000):
        h = sum((arb(1)/j for j in range(1, n+1)), arb(0))
        short, _ = chain_step(n, h, 32)
        full, _ = chain_step(n, h, n)
        assert (short-full).contains(0)
    return {"quotient_chain_ranks_checked": [1, 2, 3, 4, 5],
            "full_vs_truncated_ranks": [128, 257, 1000],
            "chirality_conjugation": "passed", "normalization": "passed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census-rank", type=int, default=5)
    parser.add_argument("--chain-rank", type=int, default=10000)
    parser.add_argument("--cutoff", type=int, default=64)
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.chain_rank < 1 or args.cutoff < 2 or args.precision < 128:
        parser.error("require positive chain rank, cutoff >= 2, precision >= 128")
    ctx.prec = args.precision
    started = time.perf_counter()
    checks = self_check()
    print("Independent quotient and chain checks passed", flush=True)
    finite = census(args.census_rank)
    print("Finite census:", json.dumps(finite["ranks"]), flush=True)
    chains = chain_audit(args.chain_rank, args.cutoff)
    source_dir = Path(__file__).resolve().parent
    source_hashes = {name: hashlib.sha256((source_dir/name).read_bytes()).hexdigest()
                     for name in (Path(__file__).name, "harmonic_child_nonuniformity.py",
                                  "chiral_growth_generalization.py")}
    result = {"law": "canonical positive-radial harmonic Born law on unlabeled children",
              "arithmetic": "exact rational raw amplitudes; Arb ball enclosures",
              "python_version": platform.python_version(), "python_flint_version": flint.__version__,
              "source_sha256": source_hashes,
              "precision_bits": args.precision, "checks": checks,
              "finite_census": finite, "chain": chains,
              "uniform_envelopes": envelope_audit(),
              "elapsed_seconds": time.perf_counter()-started}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print("Finite chain prefix:", chains["finite_prefix_survival"]["enclosure"])
    print("Infinite chain lower bound:", chains["infinite_chain_probability_lower"]["enclosure"])
    print("Wrote", args.output)


if __name__ == "__main__":
    main()
