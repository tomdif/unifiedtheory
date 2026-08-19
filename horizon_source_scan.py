#!/usr/bin/env python3
"""HORIZON SOURCE SCAN (registered 2026-08-19).

Follow-up to `horizon_entropy_probe.py`.

Question:
  The frontier-hit source `J(D)` has an exact entropy-to-focusing identity.
  Is that signal already present in the repo's BDG/action gap, or is it a
  boundary component that the full gap partly hides?

For each parent causet and each possible next-birth precursor `D`, compute:

  J(D)        = number of maximal/horizon elements hit by D
  DeltaA(D)   = 1 - J(D)
  gap(D)      = existing pi/4 action-gap increment
  shell_k(D)  = number of y in D whose open interval to the birth has size k

The 2D gap convention is

  gap(D) = 1 - (2 shell_0(D) - 4 shell_1(D) + 2 shell_2(D)).

Every horizon element in D contributes to shell_0, so the boundary part of
the BDG bracket is exactly `2*J(D)`.  This script tests that decomposition by
tilting the baseline law with standardized candidate sources.

Output columns:
  corr(J,S):       baseline correlation between horizon hit count and source
  area_slope:      small-lambda `d E[DeltaA]/d lambda = Cov(DeltaA,S_std)`
                   so negative means focusing
  gap_slope:       small-lambda `d E[gap]/d lambda`
  mean area_shift: measured finite-lambda shift under q ∝ p exp(lambda S_std)
  mean KL:         finite KL(q||p)

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
    log,
    make_law_ell,
    rng,
    transition_table,
)


W0, W1, W2 = 2.0, -4.0, 2.0


def shell_counts(dlist, above):
    h0 = np.zeros(len(dlist), dtype=float)
    h1 = np.zeros(len(dlist), dtype=float)
    h2 = np.zeros(len(dlist), dtype=float)
    for i, D0 in enumerate(dlist):
        D = int(D0)
        m = D
        while m:
            y = (m & -m).bit_length() - 1
            k = bitcount(D & int(above[y]))
            if k == 0:
                h0[i] += 1.0
            elif k == 1:
                h1[i] += 1.0
            elif k == 2:
                h2[i] += 1.0
            m &= m - 1
    return h0, h1, h2


def parent_observables(dlist, garr, above):
    frontier = frontier_mask_from_above(above)
    J = np.array([bitcount(int(D) & frontier) for D in dlist], dtype=float)
    size = np.array([bitcount(int(D)) for D in dlist], dtype=float)
    h0, h1, h2 = shell_counts(dlist, above)
    bracket = W0 * h0 + W1 * h1 + W2 * h2
    boundary_bracket = W0 * J
    interior_bracket = bracket - boundary_bracket
    gap = garr.astype(float)
    # gap = 1 - bracket; this local reconstruction is a sanity check source.
    reconstructed_gap = 1.0 - bracket
    return {
        "J": J,
        "DeltaA": 1.0 - J,
        "size": size,
        "gap": gap,
        "-gap": -gap,
        "bdg_bracket": bracket,
        "boundary_bdg": boundary_bracket,
        "interior_bdg": interior_bracket,
        "h0": h0,
        "h1": h1,
        "h2": h2,
        "gap_reconstructed": reconstructed_gap,
    }


def weighted_mean(p, x):
    return float(np.dot(p, x))


def weighted_var(p, x):
    mu = weighted_mean(p, x)
    return float(np.dot(p, (x - mu) ** 2))


def weighted_cov(p, x, y):
    mx = weighted_mean(p, x)
    my = weighted_mean(p, y)
    return float(np.dot(p, (x - mx) * (y - my)))


def standardize(p, x):
    mu = weighted_mean(p, x)
    var = weighted_var(p, x)
    if var <= 1e-14:
        return None
    return (x - mu) / math.sqrt(var)


def source_vector(p, obs, source_name):
    if source_name.startswith("J_plus_negGap_"):
        a = float(source_name.removeprefix("J_plus_negGap_"))
        SJ = standardize(p, obs["J"])
        SG = standardize(p, obs["-gap"])
        if SJ is None or SG is None:
            return None
        return SJ + a * SG
    return obs[source_name]


def source_row(p, obs, source_name, lam):
    Sraw = source_vector(p, obs, source_name)
    if Sraw is None:
        return None
    S = standardize(p, Sraw)
    if S is None:
        return None

    J = obs["J"]
    area = obs["DeltaA"]
    gap = obs["gap"]
    z = lam * S
    z -= float(z.max())
    q = p * np.exp(z)
    q /= float(q.sum())

    varJ = weighted_var(p, J)
    covJS = weighted_cov(p, J, S)
    covAreaS = weighted_cov(p, area, S)
    covGapS = weighted_cov(p, gap, S)
    corrJS = covJS / math.sqrt(max(varJ, 0.0)) if varJ > 1e-14 else float("nan")

    area_shift = weighted_mean(q, area) - weighted_mean(p, area)
    gap_shift = weighted_mean(q, gap) - weighted_mean(p, gap)
    kl = float(np.dot(q, np.log((q + 1e-300) / (p + 1e-300))))
    return {
        "corrJS": corrJS,
        "area_slope": covAreaS,
        "gap_slope": covGapS,
        "area_shift": area_shift,
        "gap_shift": gap_shift,
        "kl": kl,
        "varJ": varJ,
    }


def run(args):
    law = make_law_ell(math.pi / 4, NSTART=args.starts, disk_cache=None)
    sources = [s.strip() for s in args.sources.split(",") if s.strip()]
    for mix in [s.strip() for s in args.mixes.split(",") if s.strip()]:
        sources.append(f"J_plus_negGap_{mix}")
    buckets = {s: [] for s in sources}
    recon_errors = []
    sampled = 0
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
                recon_errors.append(float(np.max(np.abs(obs["gap"] - obs["gap_reconstructed"]))))
                for source in sources:
                    row = source_row(p, obs, source, args.lam)
                    if row is not None:
                        row["n"] = n
                        row["frontier"] = bitcount(frontier_mask_from_above(above))
                        buckets[source].append(row)
                sampled += 1
            j = rng.choice(dlist.shape[0], p=p)
            apply_birth(below, above, int(dlist[j]))
        if not ok:
            failed += 1

    print("\nHORIZON SOURCE SCAN")
    print(f"n={args.n}, burn={args.burn}, paths={args.paths - failed}/{args.paths}, "
          f"parents={sampled}, lambda={args.lam}, starts={args.starts}")
    print(f"max gap reconstruction error = {max(recon_errors) if recon_errors else float('nan'):.3e}")
    print()
    print("source              corr(J,S)  area_slope  gap_slope   area_shift      KL      gap_shift")
    print("------------------  ---------  ----------  ---------  -----------  --------  ----------")
    for source in sources:
        rows = buckets[source]
        if not rows:
            continue
        vals = {k: np.array([r[k] for r in rows], dtype=float) for k in
                ["corrJS", "area_slope", "gap_slope", "area_shift", "kl", "gap_shift", "varJ"]}
        print(f"{source:18s}"
              f"  {np.nanmean(vals['corrJS']): .6f}"
              f"  {np.mean(vals['area_slope']): .6f}"
              f"  {np.mean(vals['gap_slope']): .6f}"
              f"  {np.mean(vals['area_shift']): .6e}"
              f"  {np.mean(vals['kl']): .6f}"
              f"  {np.mean(vals['gap_shift']): .6e}")

    # Boundary decomposition check for the full gap.
    if "gap" in buckets and "boundary_bdg" in buckets and "interior_bdg" in buckets:
        print()
        print("READING")
        print("  `boundary_bdg = 2J` is the BDG bracket's horizon-boundary piece,")
        print("  hence it focuses in the same source direction as `J`; the full")
        print("  `gap = 1 - bracket` carries this boundary term with the opposite")
        print("  sign.  `interior_bdg` separates the bulk action contribution from")
        print("  the horizon-area response.")
    print("DONE-HORIZON-SOURCE-SCAN")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=22)
    ap.add_argument("--paths", type=int, default=24)
    ap.add_argument("--burn", type=int, default=5)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--lam", type=float, default=0.05)
    ap.add_argument(
        "--sources",
        default="J,boundary_bdg,interior_bdg,gap,-gap,bdg_bracket,size,h0,h1,h2",
    )
    ap.add_argument("--mixes", default="0.25,0.5,1.0,2.0")
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
