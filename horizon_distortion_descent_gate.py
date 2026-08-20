#!/usr/bin/env python3
"""Finite gate check for protected Hauptvermutung distortion descent.

The Lean theorem `protected_distortion_step_decreases_with_remainder` says a
protected distortion source gives a certified decrease when the finite update
remainder is at most half of the first-order descent margin:

    D_next <= D_old + step * linearResponse(S, Dist) + remainder
    remainder <= step * descentRate / 2.

This script estimates that gate on sampled one-birth parent laws.  It is not a
proof; it measures whether candidate certificate-basis source directions are
in the numerical regime required by the formal theorem.
"""

import argparse
import math

import numpy as np

from horizon_entropy_probe import apply_birth, make_law_ell, rng, transition_table
from horizon_source_scan import parent_observables, standardize, weighted_cov, weighted_mean
from horizon_certificate_channels import augment_certificate_observables
from horizon_hauptvermutung_channels import augment_hauptvermutung_observables


def centered(p, x):
    return x - weighted_mean(p, x)


def summarize(values):
    x = np.array(values, dtype=float)
    x = x[np.isfinite(x)]
    if len(x) == 0:
        return float("nan"), float("nan"), 0
    mean = float(np.mean(x))
    se = float(np.std(x, ddof=1) / math.sqrt(len(x))) if len(x) > 1 else 0.0
    return mean, se, int(len(x))


def residualize_against_horizon(p, jstd, raw):
    s = standardize(p, raw)
    if s is None:
        return None
    residual = s - weighted_cov(p, s, jstd) * jstd
    return standardize(p, residual)


def tilted_distribution(p, source, step):
    z = step * source
    z = z - float(np.max(z))
    q = p * np.exp(z)
    total = float(np.sum(q))
    if total <= 0.0 or not math.isfinite(total):
        return None
    return q / total


def augment_observables(args, dlist, below, above, obs):
    if args.basis == "cert":
        return augment_certificate_observables(dlist, below, above, obs)
    if args.basis == "hv":
        return augment_hauptvermutung_observables(dlist, below, above, obs)
    return obs


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
                obs = augment_observables(args, dlist, below, above, obs)
                needed = (args.channel_a, args.channel_b, args.target)
                if all(name in obs for name in needed):
                    jstd = standardize(p, obs["J"])
                    if jstd is not None:
                        ra = residualize_against_horizon(p, jstd, obs[args.channel_a])
                        rb = residualize_against_horizon(p, jstd, obs[args.channel_b])
                        if ra is not None and rb is not None:
                            source = standardize(p, ra + args.t * rb)
                            if source is not None:
                                rows.append({
                                    "p": p,
                                    "source": source,
                                    "J": obs["J"],
                                    "area": obs["DeltaA"],
                                    "gap": obs["gap"],
                                    "target": obs[args.target],
                                })
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed += 1

    return rows, args.paths - failed


def orient_sources(args, rows):
    if args.local_sign:
        flips = 0
        for row in rows:
            response = weighted_cov(row["p"], row["target"], row["source"])
            if response > 0.0:
                row["source"] = -row["source"]
                flips += 1
        return f"local({flips}/{len(rows)} flipped)"

    responses = [
        weighted_cov(row["p"], row["target"], row["source"])
        for row in rows
    ]
    mean_response = summarize(responses)[0]
    sign = 1.0
    if args.auto_sign and math.isfinite(mean_response) and mean_response > 0.0:
        sign = -1.0
    for row in rows:
        row["source"] = sign * row["source"]
    return f"global({sign:+.0f})"


def row_static_stats(row):
    p = row["p"]
    source = row["source"]
    target = row["target"]
    area = row["area"]
    j = row["J"]
    gap = row["gap"]
    s = centered(p, source)
    qarea = weighted_cov(p, area, s * s)
    leak = weighted_cov(p, j, s * s)
    return {
        "first_area": weighted_cov(p, area, source),
        "quadratic_area": qarea,
        "leakage": leak,
        "quad_plus_leak": qarea + leak,
        "gap_response": weighted_cov(p, gap, source),
        "target_response": weighted_cov(p, target, source),
        "old_target": weighted_mean(p, target),
    }


def row_step_stats(row, step):
    p = row["p"]
    source = row["source"]
    target = row["target"]
    q = tilted_distribution(p, source, step)
    if q is None:
        return None
    old = weighted_mean(p, target)
    new = weighted_mean(q, target)
    linear = weighted_cov(p, target, source)
    descent = -linear
    remainder = new - old - step * linear
    half_margin = step * descent / 2.0
    ratio = new / old if abs(old) > 1e-14 else float("nan")
    gate_ratio = remainder / half_margin if abs(half_margin) > 1e-14 else float("nan")
    return {
        "old": old,
        "new": new,
        "linear": linear,
        "descent": descent,
        "remainder": remainder,
        "half_margin": half_margin,
        "gate_ratio": gate_ratio,
        "ratio": ratio,
        "gate_pass": descent > 0.0 and remainder <= half_margin,
        "strict_decrease": new < old,
    }


def print_summary(label, values):
    mean, se, n = summarize(values)
    print(f"{label:<22} {mean: .6e} +/- {se:.1e}  n={n}")


def run(args):
    global rng
    rng = np.random.default_rng(args.seed)
    rows, ok_paths = collect_rows(args)
    sign = orient_sources(args, rows)
    steps = [float(x) for x in args.steps.split(",") if x.strip()]

    print("\nHORIZON-PROTECTED DISTORTION DESCENT GATE")
    print(f"n={args.n}, burn={args.burn}, paths={ok_paths}/{args.paths}, "
          f"parents={len(rows)}, starts={args.starts}, seed={args.seed}, basis={args.basis}")
    print(f"source=residual({args.channel_a}) + {args.t:.6g} residual({args.channel_b}), "
          f"target={args.target}, orientation={sign}")
    print()

    static = [row_static_stats(row) for row in rows]
    print("Static source diagnostics:")
    for key in (
        "first_area",
        "quadratic_area",
        "leakage",
        "quad_plus_leak",
        "gap_response",
        "target_response",
        "old_target",
    ):
        print_summary(key, [s[key] for s in static])
    descent_positive = sum(1 for s in static if s["target_response"] < 0.0)
    print(f"descent_positive_frac  {descent_positive / len(static): .6f}  "
          f"({descent_positive}/{len(static)})")

    print()
    print("Finite tilt gate by step:")
    print("step      pass    strict   mean_remainder     mean_half_margin"
          "   mean_gate_ratio   mean_new/old")
    print("--------  ------  -------  -----------------  -----------------"
          "  ---------------  ------------")
    for step in steps:
        step_rows = [row_step_stats(row, step) for row in rows]
        step_rows = [r for r in step_rows if r is not None]
        if not step_rows:
            continue
        pass_frac = sum(1 for r in step_rows if r["gate_pass"]) / len(step_rows)
        strict_frac = sum(1 for r in step_rows if r["strict_decrease"]) / len(step_rows)
        rem = summarize([r["remainder"] for r in step_rows])[0]
        half = summarize([r["half_margin"] for r in step_rows])[0]
        gate_ratio = summarize([r["gate_ratio"] for r in step_rows])[0]
        ratio = summarize([r["ratio"] for r in step_rows])[0]
        print(f"{step: .4f}  {pass_frac: .3f}   {strict_frac: .3f}"
              f"   {rem: .6e}       {half: .6e}"
              f"      {gate_ratio: .6f}      {ratio: .6f}")

    print("DONE-HORIZON-DISTORTION-DESCENT-GATE")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=18)
    ap.add_argument("--paths", type=int, default=4)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--seed", type=int, default=53)
    ap.add_argument("--basis", choices=["shell", "hv", "cert"], default="cert")
    ap.add_argument("--channel-a", default="cert_pairConsistency")
    ap.add_argument("--channel-b", default="-gap")
    ap.add_argument("--t", type=float, default=3.5035)
    ap.add_argument("--target", default="cert_scaledDistortionBound")
    ap.add_argument("--steps", default="0.005,0.01,0.02,0.05")
    ap.add_argument("--auto-sign", action=argparse.BooleanOptionalAction, default=True)
    ap.add_argument("--local-sign", action="store_true",
                    help="Orient each parent-state source to descend the target observable.")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
