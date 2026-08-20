#!/usr/bin/env python3
"""Coefficient scan for corrected canonical horizon-invisible descent.

The Lean theorem
`correctedCanonicalHorizonInvisibleDescentSource_protected_bridge` says that a
canonical residual-gradient source can be corrected by a second residual
channel when the mixed source lies on the second-order leakage null cone and
retains enough descent margin.

This script estimates that coefficient in the current finite probes.  It uses
the raw scan convention

    residual(target) + t * residual(corrector)

and then applies parent-local sign orientation before checking the finite
descent gate.  Since sign does not change second-order leakage, this is the
empirical counterpart of the Lean corrected-source theorem up to the final
orientation convention.  The comparison mode tests several corrector channels;
in the current BDG decomposition, `-gap` and `interior_bdg` become the same
effective channel after standardizing and projecting away the horizon source.
"""

import argparse
import math
from types import SimpleNamespace

import numpy as np

import horizon_distortion_descent_gate as gate
import horizon_leakage_nullcone_scan as leakscan


def parse_ints(text):
    return [int(x) for x in text.split(",") if x.strip()]


def parse_floats(text):
    return [float(x) for x in text.split(",") if x.strip()]


def parse_strings(text):
    return [x.strip() for x in text.split(",") if x.strip()]


def summarize(values):
    x = np.array(list(values), dtype=float)
    x = x[np.isfinite(x)]
    if len(x) == 0:
        return float("nan")
    return float(np.mean(x))


def spread(values):
    x = np.array(list(values), dtype=float)
    x = x[np.isfinite(x)]
    if len(x) <= 1:
        return 0.0 if len(x) == 1 else float("nan")
    return float(np.std(x, ddof=1))


def leakage_args(args, n, seed):
    return SimpleNamespace(
        basis=args.basis,
        burn=args.burn,
        channels=f"{args.target},{args.corrector}",
        n=n,
        paths=args.paths,
        root_bound=args.root_bound,
        seed=seed,
        starts=args.starts,
    )


def gate_args(args, n, seed, t):
    return SimpleNamespace(
        auto_sign=True,
        basis=args.basis,
        burn=args.burn,
        channel_a=args.target,
        channel_b=args.corrector,
        local_sign=True,
        n=n,
        paths=args.paths,
        seed=seed,
        starts=args.starts,
        steps=args.steps,
        t=t,
        target=args.target,
    )


def choose_root(roots, target_t):
    if not roots:
        return float("nan")
    return min(roots, key=lambda t: abs(abs(t) - abs(target_t)))


def scan_coeff(args, n, seed):
    leakscan.rng = np.random.default_rng(seed)
    rows, ok_paths, _channels = leakscan.collect_parent_rows(
        leakage_args(args, n, seed)
    )
    aa, ab, bb = leakscan.aggregate_leakage_coeffs(
        rows, args.target, args.corrector
    )
    roots = leakscan.root_candidates(aa, ab, bb, args.root_bound)
    t = choose_root(roots, args.target_t)
    stats = leakscan.evaluate_pair(rows, args.target, args.corrector, t)
    return {
        "aa": aa,
        "ab": ab,
        "bb": bb,
        "leak_rows": len(rows),
        "ok_paths": ok_paths,
        "roots": roots,
        "t": t,
        "leakage": stats["leak"][0],
        "quad_area": stats["quad"][0],
        "gap_response": stats["gap"][0],
    }


def scan_gate(args, n, seed, t):
    gate.rng = np.random.default_rng(seed)
    gargs = gate_args(args, n, seed, t)
    rows, ok_paths = gate.collect_rows(gargs)
    orientation = gate.orient_sources(gargs, rows)
    static = [gate.row_static_stats(row) for row in rows]
    steps = parse_floats(args.steps)
    step_stats = {}
    for step in steps:
        vals = [gate.row_step_stats(row, step) for row in rows]
        vals = [v for v in vals if v is not None]
        if vals:
            step_stats[step] = {
                "pass": sum(1 for v in vals if v["gate_pass"]) / len(vals),
                "strict": sum(1 for v in vals if v["strict_decrease"]) / len(vals),
                "ratio": summarize(v["ratio"] for v in vals),
            }
    return {
        "gate_rows": len(rows),
        "ok_paths": ok_paths,
        "orientation": orientation,
        "target_response": summarize(s["target_response"] for s in static),
        "first_area": summarize(s["first_area"] for s in static),
        "leakage": summarize(s["leakage"] for s in static),
        "step_stats": step_stats,
    }


def fmt(x):
    if not math.isfinite(x):
        return "nan"
    return f"{x:.6g}"


def run(args):
    depths = parse_ints(args.depths)
    seeds = parse_ints(args.seeds)
    steps = parse_floats(args.steps)
    print("\nCORRECTED CANONICAL COEFFICIENT SCAN")
    print(f"basis={args.basis}, target={args.target}, corrector={args.corrector}, "
          f"target_t={args.target_t}, paths={args.paths}, starts={args.starts}")
    print()
    head = [
        "n", "seed", "t_root", "|t|", "leak", "quad", "target_resp",
        "gate_rows",
    ]
    head.extend(f"pass@{step:g}" for step in steps)
    print("  ".join(f"{h:>12}" for h in head))
    print("  ".join("-" * 12 for _ in head))
    collected_t = []
    collected_abs_t = []
    collected_leak = []
    collected_target = []
    for n in depths:
        for seed in seeds:
            coeff = scan_coeff(args, n, seed)
            t = coeff["t"]
            if math.isfinite(t):
                collected_t.append(t)
                collected_abs_t.append(abs(t))
            collected_leak.append(coeff["leakage"])
            gate_stats = scan_gate(args, n, seed, t)
            collected_target.append(gate_stats["target_response"])
            row = [
                str(n),
                str(seed),
                fmt(t),
                fmt(abs(t)),
                fmt(coeff["leakage"]),
                fmt(coeff["quad_area"]),
                fmt(gate_stats["target_response"]),
                str(gate_stats["gate_rows"]),
            ]
            for step in steps:
                row.append(fmt(gate_stats["step_stats"].get(step, {}).get("pass", float("nan"))))
            print("  ".join(f"{x:>12}" for x in row))
    print()
    print("Summary:")
    print(f"mean_t              {fmt(summarize(collected_t))}")
    print(f"mean_abs_t          {fmt(summarize(collected_abs_t))}")
    print(f"mean_abs_leakage    {fmt(summarize(abs(x) for x in collected_leak))}")
    print(f"mean_target_resp    {fmt(summarize(collected_target))}")
    print("DONE-CORRECTED-CANONICAL-COEFFICIENT-SCAN")


def with_corrector(args, corrector):
    data = vars(args).copy()
    data["corrector"] = corrector
    return SimpleNamespace(**data)


def compare_correctors(args):
    correctors = parse_strings(args.correctors)
    depths = parse_ints(args.depths)
    seeds = parse_ints(args.seeds)
    steps = parse_floats(args.steps)
    last_step = steps[-1] if steps else float("nan")
    print("\nCORRECTED CANONICAL CORRECTOR COMPARISON")
    print(f"basis={args.basis}, target={args.target}, paths={args.paths}, "
          f"depths={args.depths}, seeds={args.seeds}, target_t={args.target_t}")
    print()
    head = [
        "corrector", "samples", "mean|t|", "sd|t|", "mean|leak|",
        "mean_resp", f"minpass@{last_step:g}",
    ]
    print("  ".join(f"{h:>18}" for h in head))
    print("  ".join("-" * 18 for _ in head))
    for corrector in correctors:
        cargs = with_corrector(args, corrector)
        abs_t = []
        abs_leak = []
        target_resp = []
        pass_fracs = []
        samples = 0
        for n in depths:
            for seed in seeds:
                coeff = scan_coeff(cargs, n, seed)
                t = coeff["t"]
                if not math.isfinite(t):
                    continue
                samples += 1
                abs_t.append(abs(t))
                abs_leak.append(abs(coeff["leakage"]))
                gate_stats = scan_gate(cargs, n, seed, t)
                target_resp.append(gate_stats["target_response"])
                if steps:
                    pass_fracs.append(
                        gate_stats["step_stats"].get(last_step, {}).get(
                            "pass", float("nan")
                        )
                    )
        row = [
            corrector,
            str(samples),
            fmt(summarize(abs_t)),
            fmt(spread(abs_t)),
            fmt(summarize(abs_leak)),
            fmt(summarize(target_resp)),
            fmt(summarize(pass_fracs)),
        ]
        print("  ".join(f"{x:>18}" for x in row))
    print("DONE-CORRECTED-CANONICAL-CORRECTOR-COMPARISON")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--basis", choices=["shell", "hv", "cert"], default="cert")
    ap.add_argument("--target", default="cert_scaledDistortionBound")
    ap.add_argument("--corrector", default="-gap")
    ap.add_argument("--correctors", default=None,
                    help="Comma-separated correctors to compare instead of a single detailed scan.")
    ap.add_argument("--depths", default="18,20")
    ap.add_argument("--seeds", default="53,157")
    ap.add_argument("--paths", type=int, default=2)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--steps", default="0.005,0.01,0.02,0.05")
    ap.add_argument("--root-bound", type=float, default=8.0)
    ap.add_argument("--target-t", type=float, default=3.5)
    args = ap.parse_args()
    if args.correctors:
        compare_correctors(args)
    else:
        run(args)


if __name__ == "__main__":
    main()
