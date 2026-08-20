#!/usr/bin/env python3
"""MULTI-CHANNEL SEARCH FOR LOW SECOND-ORDER HORIZON LEAKAGE.

The pair scan shows that low-leakage directions exist, but the winning pair
can drift with sampling.  This script searches the full residualized defect
channel span for directions with:

  * near-zero first-order horizon-area response;
  * small second central horizon leakage;
  * large gap/action response.

The search is numerical.  It complements the two-channel Lean theorem by
testing whether the stable physical object is likely a multi-channel direction
rather than a single pair.
"""

import argparse
import itertools
import math
from types import SimpleNamespace

import numpy as np

import horizon_leakage_nullcone_scan as nullscan


def parse_channels(s):
    return [x.strip() for x in s.split(",") if x.strip()]


def direction_label(channels, coeffs, max_terms=4):
    terms = []
    for name, c in sorted(zip(channels, coeffs), key=lambda x: -abs(x[1]))[:max_terms]:
        terms.append(f"{c:+.3f}*{name}")
    return " ".join(terms)


def normalize_coeffs(v):
    norm = float(np.linalg.norm(v))
    if norm <= 1e-14:
        return None
    return v / norm


def build_directions(channels, rows, args):
    rng = np.random.default_rng(args.search_seed)
    dirs = []

    for i in range(len(channels)):
        v = np.zeros(len(channels))
        v[i] = 1.0
        dirs.append(v)

    for i, j in itertools.combinations(range(len(channels)), 2):
        for t in np.arange(args.tmin, args.tmax + 0.5 * args.step, args.step):
            v = np.zeros(len(channels))
            v[i] = 1.0
            v[j] = float(t)
            nv = normalize_coeffs(v)
            if nv is not None:
                dirs.append(nv)
        aa, ab, bb = nullscan.aggregate_leakage_coeffs(rows, channels[i], channels[j])
        for t in nullscan.root_candidates(aa, ab, bb, args.root_bound):
            v = np.zeros(len(channels))
            v[i] = 1.0
            v[j] = float(t)
            nv = normalize_coeffs(v)
            if nv is not None:
                dirs.append(nv)

    for _ in range(args.directions):
        v = rng.normal(size=len(channels))
        nv = normalize_coeffs(v)
        if nv is not None:
            dirs.append(nv)

    unique = {}
    for v in dirs:
        key = tuple(round(float(x), 8) for x in v)
        unique[key] = v
    return list(unique.values())


def evaluate_direction(rows, channels, coeffs):
    first = []
    quad = []
    hleak = []
    proof_err = []
    gap = []
    used = 0

    for row in rows:
        residuals = row["residuals"]
        if any(name not in residuals for name in channels):
            continue
        p = row["p"]
        raw = np.zeros_like(row["J"], dtype=float)
        for name, c in zip(channels, coeffs):
            raw += c * residuals[name]
        S = nullscan.standardize(p, raw)
        if S is None:
            continue
        qarea = nullscan.quadratic_area_response(p, row["area"], S)
        leak = nullscan.leakage(p, row["J"], S, S)
        first.append(nullscan.weighted_cov(p, row["area"], S))
        quad.append(qarea)
        hleak.append(leak)
        proof_err.append(qarea + leak)
        gap.append(nullscan.weighted_cov(p, row["gap"], S))
        used += 1

    return {
        "first": nullscan.summarize(first),
        "quad": nullscan.summarize(quad),
        "leak": nullscan.summarize(hleak),
        "proof_err": nullscan.summarize(proof_err),
        "gap": nullscan.summarize(gap),
        "used": used,
    }


def score(stats, leakage_scale):
    leak = stats["leak"][0]
    gap = stats["gap"][0]
    if not math.isfinite(leak) or not math.isfinite(gap):
        return -float("inf")
    return abs(gap) / (abs(leak) + leakage_scale)


def collect(args):
    nullscan.rng = np.random.default_rng(args.path_seed)
    scan_args = SimpleNamespace(
        n=args.n,
        paths=args.paths,
        burn=args.burn,
        starts=args.starts,
        channels=args.channels,
        basis=args.basis,
        tmin=args.tmin,
        tmax=args.tmax,
        step=args.step,
        root_bound=args.root_bound,
        leakage_scale=args.leakage_scale,
        top=args.top,
        seed=args.path_seed,
    )
    return nullscan.collect_parent_rows(scan_args)


def run(args):
    rows, ok_paths, channels = collect(args)
    channels = nullscan.channel_list(args)
    dirs = build_directions(channels, rows, args)
    results = []

    for coeffs in dirs:
        stats = evaluate_direction(rows, channels, coeffs)
        if stats["used"] == 0:
            continue
        results.append((coeffs, stats))

    by_score = sorted(results, key=lambda r: score(r[1], args.leakage_scale), reverse=True)
    by_leak = sorted(results, key=lambda r: abs(r[1]["leak"][0]))

    print("\nMULTI-CHANNEL HORIZON NULL-CONE SEARCH")
    print(f"n={args.n}, burn={args.burn}, paths={ok_paths}/{args.paths}, "
          f"parents={len(rows)}, starts={args.starts}, path_seed={args.path_seed}, "
          f"search_seed={args.search_seed}")
    print(f"channels={','.join(channels)}, directions={len(results)}")
    print()
    print("Top by |gap|/(|leak|+scale):")
    print_table(channels, by_score[:args.top])
    print()
    print("Top by smallest |leak|:")
    print_table(channels, by_leak[:args.top])
    print("DONE-HORIZON-MULTICHANNEL-NULLCONE-SEARCH")


def fmt(pair):
    mean, se, _n = pair
    return f"{mean: .4e} +/- {se:.1e}"


def print_table(channels, rows):
    print("direction                                  first_area          leakage"
          "            quad+leak          gap_slope")
    print("-----------------------------------------  ------------------  "
          "-----------------  -----------------  ----------")
    for coeffs, stats in rows:
        print(f"{direction_label(channels, coeffs):<41}  "
              f"{fmt(stats['first']):>18}  {fmt(stats['leak']):>17}  "
              f"{fmt(stats['proof_err']):>17}  {stats['gap'][0]: .6f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--paths", type=int, default=8)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--basis", choices=["shell", "hv", "cert"], default="shell")
    ap.add_argument("--channels", default=None)
    ap.add_argument("--directions", type=int, default=500)
    ap.add_argument("--tmin", type=float, default=-2.0)
    ap.add_argument("--tmax", type=float, default=2.0)
    ap.add_argument("--step", type=float, default=0.10)
    ap.add_argument("--root-bound", type=float, default=8.0)
    ap.add_argument("--leakage-scale", type=float, default=0.02)
    ap.add_argument("--path-seed", type=int, default=53)
    ap.add_argument("--search-seed", type=int, default=20260819)
    ap.add_argument("--top", type=int, default=8)
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
