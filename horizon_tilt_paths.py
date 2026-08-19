#!/usr/bin/env python3
"""PATH-LEVEL TEST OF THE REGISTERED HORIZON SOURCE (2026-08-19).

The one-step probes found a stable source

    S_* = std(std(J) + a residual(std(-gap) | std(J))),  a = 0.20,

which preserves about 98% of the exact finite horizon-focusing slope while
coupling about 4x more strongly to the action/gap sector than pure `J`.

This script applies that source at every birth and asks whether the signal
survives path composition.

At each parent causet:

    q_lambda(D) ∝ p(D) exp(lambda S_*(D)).

It then samples full paths and compares final observables:

  * final frontier size (horizon area proxy);
  * global ordering fraction r;
  * final height and rank-width proxy;
  * cumulative selected action gap;
  * UV interval abundances N0,N1,N2 per element;
  * cumulative KL(q||p) paid along the path.

No Lean build artifacts are touched.  The ellipsoid law cache is in-memory only.
"""

import argparse
import math
import time

import numpy as np

from horizon_entropy_probe import (
    apply_birth,
    bitcount,
    frontier_mask_from_above,
    make_law_ell,
    transition_table,
)
from horizon_source_scan import parent_observables, standardize, weighted_cov

T0 = time.time()

MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8, 10], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287, 0.000496])
_ORD = np.argsort(-np.log(MM_F))
_XP = (-np.log(MM_F))[_ORD]
_FP = MM_D[_ORD]


def log(*args):
    print(f"[{time.time() - T0:7.1f}s]", *args, flush=True)


def d_from_f(f):
    if f is None or f <= 0:
        return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))


def source_star(p, obs, a):
    SJ = standardize(p, obs["J"])
    SG = standardize(p, obs["-gap"])
    if SJ is None:
        return None
    if SG is None:
        return SJ
    SG = SG - weighted_cov(p, SG, SJ) * SJ
    SG = standardize(p, SG)
    if SG is None:
        return SJ
    return standardize(p, SJ + a * SG)


def tilted_probs(p, obs, lam, a):
    if lam == 0:
        return p, 0.0
    S = source_star(p, obs, a)
    if S is None:
        return p, 0.0
    z = lam * S
    z -= float(np.max(z))
    q = p * np.exp(z)
    q /= float(np.sum(q))
    kl = float(np.dot(q, np.log((q + 1e-300) / (p + 1e-300))))
    return q, kl


def final_metrics(below, above, action, cumulative_kl):
    N = len(below)
    rel = sum(bitcount(b) for b in below)
    r = rel / (N * (N - 1) / 2)
    frontier = bitcount(frontier_mask_from_above(above))

    heights = [1] * N
    for x in range(N):
        m = below[x]
        best = 0
        while m:
            y = (m & -m).bit_length() - 1
            best = max(best, heights[y])
            m &= m - 1
        heights[x] = best + 1
    height = max(heights)
    rank_width_proxy = max(heights.count(h) for h in set(heights))

    ab = np.zeros(3, dtype=float)
    for x in range(N):
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            k = bitcount(int(above[y]) & int(below[x]))
            if k < 3:
                ab[k] += 1.0
            m &= m - 1
    ab /= N

    prof = {}
    all_f = []
    for x in range(N):
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            inter = int(above[y]) & int(below[x])
            k = bitcount(inter)
            if k >= 4:
                elems = []
                mm = inter
                while mm:
                    e = (mm & -mm).bit_length() - 1
                    elems.append(e)
                    mm &= mm - 1
                nrel = sum(bitcount(int(below[e]) & inter) for e in elems)
                f = nrel / (k * (k - 1) / 2)
                b = 2 ** int(math.log2(k))
                prof.setdefault(b, []).append(f)
                all_f.append(f)
            m &= m - 1

    return {
        "frontier": float(frontier),
        "r": float(r),
        "height": float(height),
        "rank_width": float(rank_width_proxy),
        "action": float(action),
        "kl": float(cumulative_kl),
        "N0": float(ab[0]),
        "N1": float(ab[1]),
        "N2": float(ab[2]),
        "dint_all": d_from_f(float(np.mean(all_f))) if all_f else float("nan"),
        "dint4": d_from_f(float(np.mean(prof[4]))) if 4 in prof else float("nan"),
        "dint8": d_from_f(float(np.mean(prof[8]))) if 8 in prof else float("nan"),
    }


def sample_path(N, law, lam, a, rng, uniforms=None):
    below = [0]
    above = [0]
    action = 0.0
    cumulative_kl = 0.0
    for step, _n in enumerate(range(1, N)):
        tab = transition_table(below, above, law)
        if tab is None:
            return None
        dlist, garr, p = tab
        obs = parent_observables(dlist, garr, above)
        q, kl = tilted_probs(p, obs, lam, a)
        if uniforms is None:
            j = rng.choice(dlist.shape[0], p=q)
        else:
            cdf = np.cumsum(q)
            j = int(np.searchsorted(cdf, uniforms[step], side="right"))
            if j >= len(q):
                j = len(q) - 1
        action += float(garr[j])
        cumulative_kl += kl
        apply_birth(below, above, int(dlist[j]))
    return final_metrics(below, above, action, cumulative_kl)


def summarize(rows):
    keys = [
        "frontier", "r", "height", "rank_width", "action", "kl",
        "N0", "N1", "N2", "dint_all", "dint4", "dint8",
    ]
    out = {}
    for k in keys:
        x = np.array([row[k] for row in rows], dtype=float)
        x = x[np.isfinite(x)]
        out[k] = (
            float(np.mean(x)) if len(x) else float("nan"),
            float(np.std(x, ddof=1) / math.sqrt(len(x))) if len(x) > 1 else 0.0,
        )
    return out


def summarize_shifts(rows, base_rows):
    keys = [
        "frontier", "r", "height", "rank_width", "action", "kl",
        "N0", "N1", "N2", "dint_all", "dint4", "dint8",
    ]
    out = {}
    for k in keys:
        x = np.array([row[k] - base[k] for row, base in zip(rows, base_rows)], dtype=float)
        x = x[np.isfinite(x)]
        out[k] = (
            float(np.mean(x)) if len(x) else float("nan"),
            float(np.std(x, ddof=1) / math.sqrt(len(x))) if len(x) > 1 else 0.0,
        )
    return out


def run(args):
    law = make_law_ell(math.pi / 4, NSTART=args.starts, disk_cache=None)
    lambdas = [float(x) for x in args.lambdas.split(",")]
    rng = np.random.default_rng(args.seed)
    results = {}
    raw = {lam: [] for lam in lambdas}
    if args.paired:
        failures = 0
        while len(raw[lambdas[0]]) < args.paths and failures < args.paths * 3:
            uniforms = rng.random(args.n - 1)
            trial = {}
            ok = True
            for lam in lambdas:
                row = sample_path(args.n, law, lam, args.a, rng, uniforms=uniforms)
                if row is None:
                    ok = False
                    break
                trial[lam] = row
            if not ok:
                failures += 1
                continue
            for lam in lambdas:
                raw[lam].append(trial[lam])
        for lam in lambdas:
            results[lam] = summarize(raw[lam])
            log(f"lambda={lam:+.3f}: sampled {len(raw[lam])} paired paths, shared failures={failures}")
    else:
        for lam in lambdas:
            failures = 0
            while len(raw[lam]) < args.paths and failures < args.paths * 3:
                row = sample_path(args.n, law, lam, args.a, rng)
                if row is None:
                    failures += 1
                    continue
                raw[lam].append(row)
            results[lam] = summarize(raw[lam])
            log(f"lambda={lam:+.3f}: sampled {len(raw[lam])} paths, failures={failures}")

    print("\nPATH-LEVEL HORIZON SOURCE TEST")
    print(f"N={args.n}, paths={args.paths}, starts={args.starts}, a={args.a}, seed={args.seed}, paired={args.paired}")
    print("source S_* = std(std(J) + a residual(std(-gap)|std(J)))")
    print()
    print("lambda   frontier      r        height   rank_w    action      KL       N0       N1       N2")
    print("------  ---------  ---------  -------  -------  --------  --------  -------  -------  -------")
    for lam in lambdas:
        s = results[lam]
        print(f"{lam:+.3f}"
              f"  {s['frontier'][0]:9.3f}"
              f"  {s['r'][0]:9.4f}"
              f"  {s['height'][0]:7.3f}"
              f"  {s['rank_width'][0]:7.3f}"
              f"  {s['action'][0]:8.3f}"
              f"  {s['kl'][0]:8.4f}"
              f"  {s['N0'][0]:7.3f}"
              f"  {s['N1'][0]:7.3f}"
              f"  {s['N2'][0]:7.3f}")

    print("\nLOCAL INTERVAL DIMENSION")
    print("lambda   d_all    d_k~4    d_k~8")
    print("------  -------  -------  -------")
    for lam in lambdas:
        s = results[lam]
        print(f"{lam:+.3f}"
              f"  {s['dint_all'][0]:7.3f}"
              f"  {s['dint4'][0]:7.3f}"
              f"  {s['dint8'][0]:7.3f}")

    if 0.0 in results:
        base = results[0.0]
        base_rows = raw[0.0]
        print("\nSHIFTS VS BASELINE")
        print("lambda   dFrontier±se       dr±se       dHeight±se    dAction±se     dN0±se      dN1±se      dN2±se")
        print("------  -------------  -------------  ------------  ------------  ----------  ----------  ----------")
        for lam in lambdas:
            if lam == 0.0:
                continue
            s = results[lam]
            sh = summarize_shifts(raw[lam], base_rows) if args.paired else None
            if sh is not None:
                print(f"{lam:+.3f}"
                      f"  {sh['frontier'][0]:7.3f}±{sh['frontier'][1]:.3f}"
                      f"  {sh['r'][0]:+8.4f}±{sh['r'][1]:.4f}"
                      f"  {sh['height'][0]:7.3f}±{sh['height'][1]:.3f}"
                      f"  {sh['action'][0]:8.3f}±{sh['action'][1]:.3f}"
                      f"  {sh['N0'][0]:+6.3f}±{sh['N0'][1]:.3f}"
                      f"  {sh['N1'][0]:+6.3f}±{sh['N1'][1]:.3f}"
                      f"  {sh['N2'][0]:+6.3f}±{sh['N2'][1]:.3f}")
                continue
            print(f"{lam:+.3f}"
                  f"  {s['frontier'][0] - base['frontier'][0]:10.3f}"
                  f"  {s['r'][0] - base['r'][0]:9.4f}"
                  f"  {s['height'][0] - base['height'][0]:7.3f}"
                  f"  {s['action'][0] - base['action'][0]:8.3f}"
                  f"  {s['N0'][0] - base['N0'][0]:7.3f}"
                  f"  {s['N1'][0] - base['N1'][0]:7.3f}"
                  f"  {s['N2'][0] - base['N2'][0]:7.3f}")
        if args.paired:
            print("\nLOCAL-DIMENSION SHIFTS VS BASELINE")
            print("lambda   dAll±se       d4±se        d8±se")
            print("------  -----------  -----------  -----------")
            for lam in lambdas:
                if lam == 0.0:
                    continue
                sh = summarize_shifts(raw[lam], base_rows)
                print(f"{lam:+.3f}"
                      f"  {sh['dint_all'][0]:+7.3f}±{sh['dint_all'][1]:.3f}"
                      f"  {sh['dint4'][0]:+7.3f}±{sh['dint4'][1]:.3f}"
                      f"  {sh['dint8'][0]:+7.3f}±{sh['dint8'][1]:.3f}")
    print("DONE-HORIZON-TILT-PATHS")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=24)
    ap.add_argument("--paths", type=int, default=32)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--a", type=float, default=0.20)
    ap.add_argument("--lambdas", default="-0.10,0.00,0.05,0.10")
    ap.add_argument("--seed", type=int, default=20260819)
    ap.add_argument("--paired", action="store_true")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
