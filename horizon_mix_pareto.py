#!/usr/bin/env python3
"""PARETO SCAN FOR THE TWO-CHANNEL HORIZON SOURCE (2026-08-19).

This is the optimization pass after `horizon_source_scan.py`.

Candidate source at each parent:

    S_a = std(J) + a * std(-gap), then standardized again.

`J` is the horizon-hit source that gives the exact finite
relative-entropy/focusing identity.  `-gap` is the action-sector direction
that moves the existing gap observable strongly but focuses weakly by itself.

For each `a`, compute the small-source slopes:

    area_slope(a) = d E[DeltaA] / d lambda = Cov(DeltaA, S_a)
    gap_slope(a)  = d E[gap]    / d lambda = Cov(gap, S_a)

Both are averaged over sampled parent states.  The useful regime keeps most of
the negative area slope of pure `J` while amplifying the negative gap slope.

No Lean build artifacts are touched.  The ellipsoid law cache is in-memory only.
"""

import argparse
import math

import numpy as np

from horizon_entropy_probe import apply_birth, log, make_law_ell, rng, transition_table
from horizon_source_scan import parent_observables, standardize, weighted_cov


def collect_parent_rows(args):
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
                    if args.orthogonal:
                        # Remove the parentwise J component from the action channel.
                        # SJ has unit p-variance and p-mean zero.
                        SG = SG - weighted_cov(p, SG, SJ) * SJ
                        SG = standardize(p, SG)
                    if SG is None:
                        continue
                    rows.append((p, obs["DeltaA"], obs["gap"], SJ, SG))
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed += 1
    return rows, args.paths - failed


def slopes_for_a(rows, a):
    area = []
    gap = []
    corr_j = []
    for p, deltaA, gap_obs, SJ, SG in rows:
        S = standardize(p, SJ + a * SG)
        if S is None:
            continue
        area.append(weighted_cov(p, deltaA, S))
        gap.append(weighted_cov(p, gap_obs, S))
        corr_j.append(weighted_cov(p, SJ, S))  # SJ has unit p-variance.
    return {
        "area": float(np.mean(area)),
        "gap": float(np.mean(gap)),
        "corr_j": float(np.mean(corr_j)),
    }


def run(args):
    rows, ok_paths = collect_parent_rows(args)
    grid = np.arange(args.amin, args.amax + 0.5 * args.step, args.step)
    vals = []
    base = slopes_for_a(rows, 0.0)
    for a in grid:
        s = slopes_for_a(rows, float(a))
        retention = s["area"] / base["area"] if abs(base["area"]) > 1e-14 else float("nan")
        gain = s["gap"] / base["gap"] if abs(base["gap"]) > 1e-14 else float("nan")
        vals.append((float(a), s["area"], s["gap"], s["corr_j"], retention, gain))

    print("\nTWO-CHANNEL HORIZON SOURCE PARETO SCAN")
    print(f"n={args.n}, burn={args.burn}, paths={ok_paths}/{args.paths}, "
          f"parents={len(rows)}, starts={args.starts}")
    if args.orthogonal:
        print("source: S_a = std(std(J) + a residual(std(-gap) | std(J)))")
    else:
        print("source: S_a = std(std(J) + a std(-gap))")
    print(f"pure J slopes: area={base['area']:.6f}, gap={base['gap']:.6f}")
    print()
    print("a       area_slope   gap_slope    corrJ   focus_ret  gap_gain")
    print("------  ----------  ----------  -------  ---------  --------")
    for a, area, gap, corr_j, retention, gain in vals:
        if abs((a / args.report_step) - round(a / args.report_step)) < 1e-8:
            print(f"{a:6.2f}  {area: .6f}  {gap: .6f}  {corr_j: .4f}"
                  f"  {retention: .4f}  {gain: .3f}")

    for threshold in args.thresholds:
        eligible = [v for v in vals if v[4] >= threshold and v[1] < 0 and v[2] < 0]
        if not eligible:
            print(f"\nNo coefficient kept focus_ret >= {threshold:.2f}.")
            continue
        best = max(eligible, key=lambda v: abs(v[2]))
        a, area, gap, corr_j, retention, gain = best
        print(f"\nBest with focus_ret >= {threshold:.2f}:")
        print(f"  a={a:.3f}, area_slope={area:.6f}, gap_slope={gap:.6f}, "
              f"corrJ={corr_j:.4f}, focus_ret={retention:.4f}, gap_gain={gain:.3f}")

    # Also report the coefficient maximizing a simple balanced objective.
    candidates = [v for v in vals if v[1] < 0 and v[2] < 0]
    if candidates:
        best_bal = max(candidates, key=lambda v: v[4] * abs(v[2]))
        a, area, gap, corr_j, retention, gain = best_bal
        print("\nBest balanced objective focus_ret * |gap_slope|:")
        print(f"  a={a:.3f}, area_slope={area:.6f}, gap_slope={gap:.6f}, "
              f"corrJ={corr_j:.4f}, focus_ret={retention:.4f}, gap_gain={gain:.3f}")
    print("DONE-HORIZON-MIX-PARETO")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=22)
    ap.add_argument("--paths", type=int, default=24)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--amin", type=float, default=0.0)
    ap.add_argument("--amax", type=float, default=2.5)
    ap.add_argument("--step", type=float, default=0.05)
    ap.add_argument("--report-step", type=float, default=0.25)
    ap.add_argument("--thresholds", type=lambda s: [float(x) for x in s.split(",")],
                    default=[0.98, 0.95, 0.90])
    ap.add_argument("--orthogonal", action="store_true")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
