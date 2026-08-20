#!/usr/bin/env python3
"""STABILITY CHECK FOR SECOND-ORDER HORIZON-LEAKAGE NULL-CONE CANDIDATES.

`horizon_leakage_nullcone_scan.py` finds two-channel combinations whose
sample-mean second-order horizon leakage is small.  This driver repeats the
scan across depths and random seeds, then reports whether the same channel pair
and coefficient keep appearing.

This is an empirical refinement-stability test, not a proof.  The Lean theorem
gives the exact finite null-cone criterion once a stable physical defect basis
is supplied.
"""

import argparse
import itertools
import math
from types import SimpleNamespace

import numpy as np

import horizon_leakage_nullcone_scan as nullscan


DEFAULT_TRACK = "-gap:h2,-gap:h1,-gap:h0,h0:h2,h1:size"
DEFAULT_HV_TRACK = (
    "hv_dim4_err:hv_rel4_abs,hv_dim4_err:hv_dim_spread,"
    "hv_rel4_abs:hv_interval_mass,hv_dim2_err:hv_rel2_abs,"
    "-gap:hv_dim4_err"
)
DEFAULT_CERT_TRACK = (
    "cert_countWindow:-gap,cert_curvatureBias:-gap,"
    "cert_pairConsistency:-gap,cert_distortionBound:-gap,"
    "cert_target4Distortion:-gap,cert_target2Distortion:-gap"
)


def parse_ints(s):
    return [int(x) for x in s.split(",") if x.strip()]


def parse_pairs(s):
    out = []
    for item in [x.strip() for x in s.split(",") if x.strip()]:
        a, b = item.split(":", 1)
        out.append((a.strip(), b.strip()))
    return out


def track_pairs(args):
    if args.track:
        return parse_pairs(args.track)
    if args.basis == "cert":
        return parse_pairs(DEFAULT_CERT_TRACK)
    if args.basis == "hv":
        return parse_pairs(DEFAULT_HV_TRACK)
    return parse_pairs(DEFAULT_TRACK)


def candidate_grid(args, aa, ab, bb):
    grid = list(np.arange(args.tmin, args.tmax + 0.5 * args.step, args.step))
    grid.extend(nullscan.root_candidates(aa, ab, bb, args.root_bound))
    return sorted({round(float(t), 10) for t in grid})


def score(stats, leakage_scale):
    return nullscan.score_result(stats, leakage_scale)


def best_for_pair(rows, args, pair):
    aname, bname = pair
    aa, ab, bb = nullscan.aggregate_leakage_coeffs(rows, aname, bname)
    best_leak = None
    best_score = None
    for t in candidate_grid(args, aa, ab, bb):
        stats = nullscan.evaluate_pair(rows, aname, bname, t)
        if stats["first"][2] == 0:
            continue
        result = {
            "pair": pair,
            "t": t,
            "aa": aa,
            "ab": ab,
            "bb": bb,
            "stats": stats,
        }
        if best_leak is None or abs(stats["leak"][0]) < abs(best_leak["stats"]["leak"][0]):
            best_leak = result
        if best_score is None or score(stats, args.leakage_scale) > score(best_score["stats"], args.leakage_scale):
            best_score = result
    return best_leak, best_score


def best_over_all_pairs(rows, channels, args):
    best_leak = None
    best_score = None
    for pair in itertools.combinations(channels, 2):
        pair_leak, pair_score = best_for_pair(rows, args, pair)
        if pair_leak is not None:
            if best_leak is None or abs(pair_leak["stats"]["leak"][0]) < abs(best_leak["stats"]["leak"][0]):
                best_leak = pair_leak
        if pair_score is not None:
            if best_score is None or score(pair_score["stats"], args.leakage_scale) > score(best_score["stats"], args.leakage_scale):
                best_score = pair_score
    return best_leak, best_score


def run_case(n, seed, args):
    nullscan.rng = np.random.default_rng(seed)
    scan_args = SimpleNamespace(
        n=n,
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
        seed=seed,
    )
    rows, ok_paths, channels = nullscan.collect_parent_rows(scan_args)
    best_leak, best_score = best_over_all_pairs(rows, channels, args)
    tracked = {}
    for pair in track_pairs(args):
        tracked[pair] = best_for_pair(rows, args, pair)[0]
    return {
        "n": n,
        "seed": seed,
        "ok_paths": ok_paths,
        "parents": len(rows),
        "best_leak": best_leak,
        "best_score": best_score,
        "tracked": tracked,
    }


def fmt_result(result):
    if result is None:
        return "none"
    aname, bname = result["pair"]
    stats = result["stats"]
    return (
        f"{aname}+t*{bname} t={result['t']:.4f} "
        f"leak={stats['leak'][0]: .3e} "
        f"quad={stats['quad'][0]: .3e} "
        f"gap={stats['gap'][0]: .3e} "
        f"first={stats['first'][0]: .1e}"
    )


def aggregate_tracked(cases, pairs):
    print("\nTracked pair stability:")
    print("pair              count  mean|leak|   mean|gap|    mean t      std t")
    print("----------------  -----  ----------  ----------  ----------  --------")
    for pair in pairs:
        vals = [case["tracked"].get(pair) for case in cases]
        vals = [v for v in vals if v is not None]
        if not vals:
            continue
        leaks = np.array([abs(v["stats"]["leak"][0]) for v in vals], dtype=float)
        gaps = np.array([abs(v["stats"]["gap"][0]) for v in vals], dtype=float)
        ts = np.array([v["t"] for v in vals], dtype=float)
        print(
            f"{pair[0]}+{pair[1]:<9}  {len(vals):5d}  "
            f"{float(np.mean(leaks)): .3e}  {float(np.mean(gaps)): .3e}  "
            f"{float(np.mean(ts)): .4f}  {float(np.std(ts)): .4f}"
        )


def run(args):
    cases = []
    for n in parse_ints(args.depths):
        for seed in parse_ints(args.seeds):
            case = run_case(n, seed, args)
            cases.append(case)
            print(
                f"\nCASE n={n}, seed={seed}, "
                f"paths={case['ok_paths']}/{args.paths}, parents={case['parents']}"
            )
            print(f"best_score: {fmt_result(case['best_score'])}")
            print(f"best_leak:  {fmt_result(case['best_leak'])}")
            for pair, result in case["tracked"].items():
                print(f"tracked {pair[0]}+{pair[1]}: {fmt_result(result)}")

    aggregate_tracked(cases, track_pairs(args))
    print("DONE-HORIZON-NULLCONE-STABILITY")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--depths", default="18,20")
    ap.add_argument("--seeds", default="53,157")
    ap.add_argument("--paths", type=int, default=8)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--basis", choices=["shell", "hv", "cert"], default="shell")
    ap.add_argument("--channels", default=None)
    ap.add_argument("--track", default=None)
    ap.add_argument("--tmin", type=float, default=-2.0)
    ap.add_argument("--tmax", type=float, default=2.0)
    ap.add_argument("--step", type=float, default=0.05)
    ap.add_argument("--root-bound", type=float, default=8.0)
    ap.add_argument("--leakage-scale", type=float, default=0.02)
    ap.add_argument("--top", type=int, default=8)
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
