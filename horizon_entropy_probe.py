#!/usr/bin/env python3
"""FINITE HORIZON RELATIVE-ENTROPY PROBE (registered 2026-08-19).

Motivation:
  Dorau--Much turn horizon Araki relative entropy into null-energy flux and
  then into Raychaudhuri focusing.  This script tests the finite causal-growth
  analogue before any continuum/AQFT import:

      baseline birth law p(D)
      source/excitation tilt q_lambda(D) ∝ p(D) exp(lambda * J(D))
      finite KL(q_lambda || p)
      horizon-area response under one birth

  Here D is the precursor downset of the next birth and the finite horizon cut
  is the current maximal antichain.  J(D) is the number of current horizon
  elements hit by D.  The next horizon size changes by

      Delta A(D) = 1 - J(D).

Exact finite identity:
  For the exponential tilt by J,

      d/dlambda KL(q_lambda || p) = lambda * Var_q[J]
      d/dlambda E_q[Delta A]     = - Var_q[J]

  so d(KL)/dlambda = -lambda * d<E[Delta A]>/dlambda.  This is the
  causal-growth shadow of "relative entropy controls focusing."

What the run measures:
  1. numerical error in the exact finite identity;
  2. small-lambda area response vs -2 KL/lambda;
  3. whether the same source tilt also moves the existing gap/action
     observable, i.e. whether horizon entropy couples to the BD/action sector.

No Lean build artifacts are touched.  The ellipsoid law cache is in-memory only.
"""

import argparse
import math
import sys
import time

import numpy as np

T0 = time.time()


def log(*args):
    print(f"[{time.time() - T0:7.1f}s]", *args, flush=True)


# Reuse the repo's pi/4 growth primitives without running its main probes.
_argv = sys.argv[:]
try:
    sys.argv = [sys.argv[0]]
    exec(open("selection_and_action.py").read().split('if MODE == "A":')[0])
finally:
    sys.argv = _argv
from law_ellipsoid import make_law_ell


def bitcount(x: int) -> int:
    return bin(int(x)).count("1")


def frontier_mask_from_above(above):
    mask = 0
    for i, a in enumerate(above):
        if a == 0:
            mask |= 1 << i
    return mask


def transition_table(below, above, law):
    n = len(below)
    dlist = downsets_vec(n, np.array(below, dtype=np.int64))
    garr = gaps_vec(dlist, n, np.array(above, dtype=np.int64))
    gc = {}
    for g in garr.tolist():
        gc[g] = gc.get(g, 0) + 1
    lw = law(gc)
    if lw is None:
        return None
    p = np.array([lw[int(g)] for g in garr.tolist()], dtype=float)
    p = np.maximum(p, 0.0)
    s = float(p.sum())
    if s <= 0:
        return None
    p /= s
    return dlist, garr.astype(float), p


def apply_birth(below, above, D):
    n = len(below)
    below.append(int(D))
    above.append(0)
    m = int(D)
    while m:
        d = (m & -m).bit_length() - 1
        above[d] |= 1 << n
        m &= m - 1


def weighted_stats(p, q, J, dA, gap, size, lam):
    J0 = float(np.dot(p, J))
    Jq = float(np.dot(q, J))
    dA0 = float(np.dot(p, dA))
    dAq = float(np.dot(q, dA))
    gap0 = float(np.dot(p, gap))
    gapq = float(np.dot(q, gap))
    size0 = float(np.dot(p, size))
    sizeq = float(np.dot(q, size))

    varq = float(np.dot(q, (J - Jq) ** 2))
    var0 = float(np.dot(p, (J - J0) ** 2))
    kl = float(np.dot(q, np.log((q + 1e-300) / (p + 1e-300))))

    # Exact derivative identity for the exponential family.
    dkl = lam * varq
    darea = -varq
    identity_resid = dkl + lam * darea

    area_shift = dAq - dA0
    small_lam_pred = -2.0 * kl / lam if lam != 0 else float("nan")
    response_ratio = area_shift / small_lam_pred if abs(small_lam_pred) > 1e-14 else float("nan")

    gp = gap - gap0
    jp = J - J0
    denom = math.sqrt(float(np.dot(p, gp * gp)) * max(var0, 0.0))
    corr_j_gap = float(np.dot(p, jp * gp) / denom) if denom > 1e-14 else float("nan")

    return {
        "kl": kl,
        "var0": var0,
        "varq": varq,
        "area_shift": area_shift,
        "response_ratio": response_ratio,
        "identity_resid": identity_resid,
        "gap_shift": gapq - gap0,
        "size_shift": sizeq - size0,
        "corr_j_gap": corr_j_gap,
    }


def parent_probe(dlist, garr, p, above, lam_values):
    frontier = frontier_mask_from_above(above)
    J = np.array([bitcount(int(D) & frontier) for D in dlist], dtype=float)
    dA = 1.0 - J
    size = np.array([bitcount(int(D)) for D in dlist], dtype=float)

    rows = []
    for lam in lam_values:
        zraw = lam * J
        zraw -= float(zraw.max())
        q = p * np.exp(zraw)
        q /= float(q.sum())
        rows.append(weighted_stats(p, q, J, dA, garr, size, lam))
    return rows


def run(args):
    law = make_law_ell(math.pi / 4, NSTART=args.starts, disk_cache=None)
    lam_values = [float(x) for x in args.lambdas.split(",")]
    buckets = {lam: [] for lam in lam_values}
    transition_count = 0
    failed_paths = 0

    for path in range(args.paths):
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
                rows = parent_probe(dlist, garr, p, above, lam_values)
                for lam, row in zip(lam_values, rows):
                    row["n"] = n
                    row["frontier"] = bitcount(frontier_mask_from_above(above))
                    row["children"] = len(dlist)
                    buckets[lam].append(row)
                transition_count += 1
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed_paths += 1

    log(f"sampled {transition_count} parent transitions from {args.paths - failed_paths}/{args.paths} paths")
    print("\nFINITE HORIZON ENTROPY RESPONSE")
    print(f"n={args.n}, burn={args.burn}, paths={args.paths}, law=pi/4 ellipsoid NSTART={args.starts}")
    print("horizon cut = current maximal antichain; source J(D)=#horizon elements in precursor D")
    print("area response = E_q[1-J]-E_p[1-J]; asymptotic prediction = -2 KL/lambda\n")

    for lam in lam_values:
        rows = buckets[lam]
        keys = [
            "kl",
            "var0",
            "varq",
            "area_shift",
            "response_ratio",
            "identity_resid",
            "gap_shift",
            "size_shift",
            "corr_j_gap",
        ]
        arr = {k: np.array([r[k] for r in rows], dtype=float) for k in keys}
        finite_corr = arr["corr_j_gap"][np.isfinite(arr["corr_j_gap"])]
        print(f"lambda={lam:.3f}  parents={len(rows)}")
        print(f"  mean KL                {np.mean(arr['kl']): .6e}")
        print(f"  mean Var_p[J]          {np.mean(arr['var0']): .6e}")
        print(f"  mean area shift        {np.mean(arr['area_shift']): .6e}")
        print(f"  mean response ratio    {np.nanmean(arr['response_ratio']): .6f}"
              f"   (1.0 = small-lambda finite Raychaudhuri)")
        print(f"  max exact-id residual  {np.max(np.abs(arr['identity_resid'])): .3e}")
        print(f"  mean gap/action shift  {np.mean(arr['gap_shift']): .6e}")
        print(f"  mean precursor-size shift {np.mean(arr['size_shift']): .6e}")
        if finite_corr.size:
            print(f"  mean corr_p(J,gap)     {np.mean(finite_corr): .6f}"
                  f"   (median {np.median(finite_corr): .6f})")
        print()

    # Cross-parent signal: does entropy susceptibility line up with action response?
    lam0 = lam_values[0]
    rows = buckets[lam0]
    if len(rows) >= 3:
        x = np.array([r["var0"] for r in rows], dtype=float)
        y = np.array([r["gap_shift"] for r in rows], dtype=float)
        z = np.array([r["area_shift"] for r in rows], dtype=float)
        corr_xy = np.corrcoef(x, y)[0, 1] if np.std(x) > 0 and np.std(y) > 0 else float("nan")
        corr_xz = np.corrcoef(x, z)[0, 1] if np.std(x) > 0 and np.std(z) > 0 else float("nan")
        print("CROSS-PARENT COUPLING AT SMALLEST LAMBDA")
        print(f"  corr(Var_p[J], gap_shift)   = {corr_xy: .6f}")
        print(f"  corr(Var_p[J], area_shift)  = {corr_xz: .6f}")
        print("DONE-HORIZON-ENTROPY")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=28)
    ap.add_argument("--paths", type=int, default=40)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=12)
    ap.add_argument("--lambdas", default="0.05,0.10,0.20")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
