#!/usr/bin/env python3
"""SECOND-ORDER LEAKAGE PROBE FOR HORIZON-ORTHOGONAL DEFECTS.

The Lean theorem in
`UnifiedTheory/Audit/KFCausalCSpecHorizonOrthogonalDefect.lean` proves that
after projecting a defect source off the horizon-hit source `J`, the first
area response vanishes exactly.  It also identifies the next obstruction:

    quadratic_area_response(S) = -Cov(J, centered(S)^2).

This script measures that leakage on the same sampled parent states used by
the horizon source scans.  It does not touch Lean build artifacts; the
ellipsoid law cache is in-memory only.
"""

import argparse
import math

import numpy as np

from horizon_entropy_probe import apply_birth, make_law_ell, rng, transition_table
from horizon_source_scan import parent_observables, standardize, weighted_cov, weighted_mean


def centered(p, x):
    return x - weighted_mean(p, x)


def quadratic_area_response(p, area, source):
    s = centered(p, source)
    return weighted_cov(p, area, s * s)


def horizon_leakage(p, J, source):
    s = centered(p, source)
    return weighted_cov(p, J, s * s)


def collect_rows(args):
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
                SJ = standardize(p, obs["J"])
                SG = standardize(p, obs["-gap"])
                if SJ is not None and SG is not None:
                    R = SG - weighted_cov(p, SG, SJ) * SJ
                    R = standardize(p, R)
                    if R is not None:
                        rows.append((p, obs["J"], obs["DeltaA"], obs["gap"], SJ, R))
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed += 1
    return rows, args.paths - failed


def summarize(values):
    x = np.array(values, dtype=float)
    x = x[np.isfinite(x)]
    if len(x) == 0:
        return float("nan"), float("nan")
    mean = float(np.mean(x))
    se = float(np.std(x, ddof=1) / math.sqrt(len(x))) if len(x) > 1 else 0.0
    return mean, se


def source_stats(rows, source_builder):
    first = []
    quad = []
    leak = []
    proof_err = []
    gap = []
    focus_ret = []
    for p, J, area, gap_obs, SJ, R in rows:
        S = source_builder(p, SJ, R)
        if S is None:
            continue
        base_area = weighted_cov(p, area, SJ)
        area_first = weighted_cov(p, area, S)
        qarea = quadratic_area_response(p, area, S)
        hleak = horizon_leakage(p, J, S)
        first.append(area_first)
        quad.append(qarea)
        leak.append(hleak)
        proof_err.append(qarea + hleak)
        gap.append(weighted_cov(p, gap_obs, S))
        if abs(base_area) > 1e-14:
            focus_ret.append(area_first / base_area)
    return {
        "first": summarize(first),
        "quad": summarize(quad),
        "leak": summarize(leak),
        "proof_err": summarize(proof_err),
        "gap": summarize(gap),
        "focus_ret": summarize(focus_ret),
    }


def run(args):
    rows, ok_paths = collect_rows(args)
    coeffs = [float(x) for x in args.coeffs.split(",") if x.strip()]

    print("\nSECOND-ORDER HORIZON LEAKAGE PROBE")
    print(f"n={args.n}, burn={args.burn}, paths={ok_paths}/{args.paths}, "
          f"parents={len(rows)}, starts={args.starts}")
    print()
    print("source              first_area        quad_area         leakage       "
          "quad+leak       gap_slope    focus_ret")
    print("------------------  ---------------  ---------------  -------------  "
          "-------------  ----------  ---------")

    residual = source_stats(rows, lambda _p, _SJ, R: R)
    print_row("residual", residual)

    for a in coeffs:
        def builder(p, SJ, R, a=a):
            return standardize(p, SJ + a * R)
        print_row(f"J+aR a={a:.2f}", source_stats(rows, builder))

    print("DONE-HORIZON-SECOND-ORDER-LEAKAGE")


def fmt(pair):
    mean, se = pair
    return f"{mean: .6e} +/- {se:.1e}"


def print_row(name, stats):
    print(f"{name:<18}  {fmt(stats['first']):>15}  {fmt(stats['quad']):>15}  "
          f"{fmt(stats['leak']):>13}  {fmt(stats['proof_err']):>13}  "
          f"{stats['gap'][0]: .6f}  {stats['focus_ret'][0]: .4f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--paths", type=int, default=16)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--coeffs", default="0.20,0.30,0.45")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
