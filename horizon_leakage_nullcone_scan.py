#!/usr/bin/env python3
"""SCAN FOR SECOND-ORDER HORIZON-LEAKAGE NULL-CONE MIXTURES.

The Lean theorem `twoChannel_firstAndSecondOrder_area_zero` proves that two
first-order horizon-orthogonal defect channels can be mixed without first- or
second-central-order horizon-area response when their coefficients lie on the
quadratic leakage null cone:

    a^2 Leak(A,A) + 2ab Leak(A,B) + b^2 Leak(B,B) = 0.

This script estimates that quadratic form on sampled parent states and tests
candidate combinations.  It is exploratory evidence only; the theorem is the
finite algebraic guarantee once exact channels and exact leakage coefficients
are supplied.
"""

import argparse
import itertools
import math

import numpy as np

from horizon_entropy_probe import apply_birth, make_law_ell, rng, transition_table
from horizon_source_scan import parent_observables, standardize, weighted_cov, weighted_mean
from horizon_hauptvermutung_channels import (
    DEFAULT_HV_CHANNELS,
    augment_hauptvermutung_observables,
)
from horizon_certificate_channels import (
    DEFAULT_CERT_CHANNELS,
    augment_certificate_observables,
)


DEFAULT_CHANNELS = "-gap,interior_bdg,h0,h1,h2,size"


def channel_list(args):
    if args.channels:
        return [s.strip() for s in args.channels.split(",") if s.strip()]
    if args.basis == "hv":
        return [s.strip() for s in DEFAULT_HV_CHANNELS.split(",") if s.strip()]
    if args.basis == "cert":
        return [s.strip() for s in DEFAULT_CERT_CHANNELS.split(",") if s.strip()]
    return [s.strip() for s in DEFAULT_CHANNELS.split(",") if s.strip()]


def centered(p, x):
    return x - weighted_mean(p, x)


def residualize_against_horizon(p, Jstd, raw):
    S = standardize(p, raw)
    if S is None:
        return None
    R = S - weighted_cov(p, S, Jstd) * Jstd
    return standardize(p, R)


def leakage(p, J, A, B):
    return weighted_cov(p, J, centered(p, A) * centered(p, B))


def quadratic_area_response(p, area, S):
    s = centered(p, S)
    return weighted_cov(p, area, s * s)


def collect_parent_rows(args):
    channels = channel_list(args)
    law = make_law_ell(math.pi / 4, NSTART=args.starts, disk_cache=None)
    rows = []
    failed = 0

    for _path in range(args.paths):
        below = [0]
        above = [0]
        ok = True
        for n in range(1, args.n):
            tab = transition_table(below, above, law)
            if tab is None:
                ok = False
                break
            dlist, garr, p = tab
            if n >= args.burn:
                obs = parent_observables(dlist, garr, above)
                if args.basis == "hv":
                    obs = augment_hauptvermutung_observables(dlist, below, above, obs)
                elif args.basis == "cert":
                    obs = augment_certificate_observables(dlist, below, above, obs)
                Jstd = standardize(p, obs["J"])
                if Jstd is not None:
                    residuals = {}
                    for name in channels:
                        if name not in obs:
                            continue
                        R = residualize_against_horizon(p, Jstd, obs[name])
                        if R is not None:
                            residuals[name] = R
                    if residuals:
                        rows.append({
                            "p": p,
                            "J": obs["J"],
                            "area": obs["DeltaA"],
                            "gap": obs["gap"],
                            "residuals": residuals,
                        })
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed += 1

    return rows, args.paths - failed, channels


def summarize(values):
    x = np.array(values, dtype=float)
    x = x[np.isfinite(x)]
    if len(x) == 0:
        return float("nan"), float("nan"), 0
    mean = float(np.mean(x))
    se = float(np.std(x, ddof=1) / math.sqrt(len(x))) if len(x) > 1 else 0.0
    return mean, se, int(len(x))


def aggregate_leakage_coeffs(rows, Aname, Bname):
    aa = []
    ab = []
    bb = []
    for row in rows:
        residuals = row["residuals"]
        if Aname not in residuals or Bname not in residuals:
            continue
        p = row["p"]
        J = row["J"]
        A = residuals[Aname]
        B = residuals[Bname]
        aa.append(leakage(p, J, A, A))
        ab.append(leakage(p, J, A, B))
        bb.append(leakage(p, J, B, B))
    return summarize(aa)[0], summarize(ab)[0], summarize(bb)[0]


def root_candidates(aa, ab, bb, bound):
    roots = []
    eps = 1e-12
    if not all(math.isfinite(x) for x in (aa, ab, bb)):
        return roots
    if abs(bb) > eps:
        disc = ab * ab - aa * bb
        if disc >= -1e-12:
            disc = max(0.0, disc)
            s = math.sqrt(disc)
            roots.extend([(-ab - s) / bb, (-ab + s) / bb])
    elif abs(ab) > eps:
        roots.append(-aa / (2.0 * ab))
    return [t for t in roots if math.isfinite(t) and abs(t) <= bound]


def evaluate_pair(rows, Aname, Bname, t):
    first = []
    quad = []
    hleak = []
    proof_err = []
    gap = []
    corr = []
    for row in rows:
        residuals = row["residuals"]
        if Aname not in residuals or Bname not in residuals:
            continue
        p = row["p"]
        A = residuals[Aname]
        B = residuals[Bname]
        S = standardize(p, A + t * B)
        if S is None:
            continue
        area = row["area"]
        J = row["J"]
        qarea = quadratic_area_response(p, area, S)
        leak = leakage(p, J, S, S)
        first.append(weighted_cov(p, area, S))
        quad.append(qarea)
        hleak.append(leak)
        proof_err.append(qarea + leak)
        gap.append(weighted_cov(p, row["gap"], S))
        corr.append(weighted_cov(p, A, B))
    return {
        "first": summarize(first),
        "quad": summarize(quad),
        "leak": summarize(hleak),
        "proof_err": summarize(proof_err),
        "gap": summarize(gap),
        "corr": summarize(corr),
    }


def score_result(stats, leakage_scale):
    leak = stats["leak"][0]
    gap = stats["gap"][0]
    if not math.isfinite(leak) or not math.isfinite(gap):
        return -float("inf")
    return abs(gap) / (abs(leak) + leakage_scale)


def run(args):
    global rng
    rng = np.random.default_rng(args.seed)
    rows, ok_paths, channels = collect_parent_rows(args)
    grid = list(np.arange(args.tmin, args.tmax + 0.5 * args.step, args.step))
    results = []

    for Aname, Bname in itertools.combinations(channels, 2):
        aa, ab, bb = aggregate_leakage_coeffs(rows, Aname, Bname)
        candidates = list(grid)
        candidates.extend(root_candidates(aa, ab, bb, args.root_bound))
        candidates = sorted({round(float(t), 10) for t in candidates})

        pair_results = []
        for t in candidates:
            stats = evaluate_pair(rows, Aname, Bname, t)
            if stats["first"][2] == 0:
                continue
            pair_results.append((Aname, Bname, t, aa, ab, bb, stats))
            results.append((Aname, Bname, t, aa, ab, bb, stats))

        if pair_results:
            best_leak = min(pair_results, key=lambda r: abs(r[6]["leak"][0]))
            best_score = max(pair_results, key=lambda r: score_result(r[6], args.leakage_scale))
            print_pair_summary("best_leak", best_leak)
            print_pair_summary("best_score", best_score)

    print("\nSECOND-ORDER HORIZON LEAKAGE NULL-CONE SCAN")
    print(f"n={args.n}, burn={args.burn}, paths={ok_paths}/{args.paths}, "
          f"parents={len(rows)}, starts={args.starts}, seed={args.seed}, basis={args.basis}")
    print(f"channels={','.join(channels)}")
    print()
    print("Top candidates by |gap|/(|leak|+scale):")
    print_table(sorted(results, key=lambda r: score_result(r[6], args.leakage_scale), reverse=True)
                [:args.top])
    print()
    print("Top candidates by smallest |leak|:")
    print_table(sorted(results, key=lambda r: abs(r[6]["leak"][0]))[:args.top])
    print("DONE-HORIZON-LEAKAGE-NULLCONE-SCAN")


def fmt_mean(pair):
    mean, se, _n = pair
    return f"{mean: .4e} +/- {se:.1e}"


def print_pair_summary(label, result):
    Aname, Bname, t, aa, ab, bb, stats = result
    print(f"{label:<10} pair={Aname}+t*{Bname:<13} t={t: .4f} "
          f"coeffs=({aa: .3e},{ab: .3e},{bb: .3e}) "
          f"leak={stats['leak'][0]: .3e} gap={stats['gap'][0]: .3e}")


def print_table(results):
    print("pair                 t        first_area          quad_area          leakage"
          "            quad+leak          gap_slope")
    print("-------------------  -------  ------------------  -----------------  "
          "-----------------  -----------------  ----------")
    for Aname, Bname, t, _aa, _ab, _bb, stats in results:
        pair = f"{Aname}+{Bname}"
        print(f"{pair:<19}  {t: .3f}  {fmt_mean(stats['first']):>18}  "
              f"{fmt_mean(stats['quad']):>17}  {fmt_mean(stats['leak']):>17}  "
              f"{fmt_mean(stats['proof_err']):>17}  {stats['gap'][0]: .6f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=18)
    ap.add_argument("--paths", type=int, default=8)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--seed", type=int, default=53)
    ap.add_argument("--basis", choices=["shell", "hv", "cert"], default="shell")
    ap.add_argument("--channels", default=None)
    ap.add_argument("--tmin", type=float, default=-4.0)
    ap.add_argument("--tmax", type=float, default=4.0)
    ap.add_argument("--step", type=float, default=0.05)
    ap.add_argument("--root-bound", type=float, default=8.0)
    ap.add_argument("--leakage-scale", type=float, default=0.02)
    ap.add_argument("--top", type=int, default=8)
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
