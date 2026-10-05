"""Diagnose the non-bijective class transports of ab_slicing_and_images.py (part A).

In the continuum (and hence in the induced order of a sprinkling) no relation
a < b can join the two geometric components of J+(p) ∩ J-(q) across slices:
the gaps are bounded by null rays from p and q.  So every failure must come
from the Dowker classes of K disagreeing with the geometric components on a
slice:
  bridged : one K-class contains both geometric components (a shadow spans a
            gap narrower than the shadow width) -> two K-classes then must be
            a split elsewhere, or the count drops to 1;
  split   : two K-classes inside one geometric component (coverage hole).
Coordinates are used ONLY for this diagnosis (geometric labels, gap widths,
shadow widths).

Geometry (L = 1): with P = J+(p) ∩ slice (half-width t_s - t_p) and
Q = J-(q) ∩ slice (half-width t_q - t_s) covering the circle, the two gaps are
the complements, of widths g_P = 1 - 2(t_s - t_p) and g_Q = 1 - 2(t_q - t_s).

Usage: python3.11 scripts/ab_transport_diagnosis.py
"""
import numpy as np
from collections import Counter
from ab_slicing_and_images import sprinkle, maximal_slice, Slice


def circ(a):
    return a % 1.0


def on_arc(x, c1, c2):
    """True if x lies on the counter-clockwise arc from c1 to c2."""
    return circ(x - c1) < circ(c2 - c1)


def shadow_width(S, x):
    """Median circular angular span of the Dowker simplices' vertex sets (max shadows)."""
    from ab_chain_pair_holonomy import shadows  # noqa: F401  (kept for clarity)
    spans = []
    nbr = {}
    for i, j in S.edges:
        nbr.setdefault(i, set()).add(j)
        nbr.setdefault(j, set()).add(i)
    for i, js in nbr.items():
        d = [min(circ(x[S.A[j]] - x[S.A[i]]), circ(x[S.A[i]] - x[S.A[j]])) for j in js]
        spans.append(max(d))
    return float(np.median(spans)) if spans else 0.0


def classify(S, comps, R, p, q, t, x):
    tsl = t[S.A].mean()
    c1, c2 = circ(x[p] + 0.5), circ(x[q] + 0.5)  # gap centres (complements of P, Q)
    geo = [set(bool(on_arc(x[S.A[a]], c1, c2)) for a in c) for c in comps]
    gP, gQ = 1 - 2 * (tsl - t[p]), 1 - 2 * (t[q] - tsl)
    bridged = any(len(g) == 2 for g in geo)
    labels = [next(iter(g)) for g in geo if len(g) == 1]
    split = len(labels) == 2 and labels[0] == labels[1]
    return bridged, split, min(gP, gQ)


def run(seed, n, rho=3000, T=1.4, tries=15000):
    rng = np.random.default_rng(seed)
    t, x, dx, R = sprinkle(rng, rho, T)
    past = R.sum(axis=0)
    try:
        sl = {k: Slice(R, maximal_slice(R, past, k)[0], n) for k in (190, 270, 370)}
    except np.linalg.LinAlgError:
        print(f"seed={seed} n={n}: SVD failed; skip")
        return
    if not all(s.ok for s in sl.values()):
        print(f"seed={seed} n={n}: some slice not (1,1); skip")
        return
    widths = {k: shadow_width(s, x) for k, s in sl.items()}
    below = lambda P: np.flatnonzero(R[:, P.A].any(axis=1) & ~R[P.A, :].any(axis=0))
    above = lambda P: np.flatnonzero(R[P.A, :].any(axis=0) & ~R[:, P.A].any(axis=1))
    Pb = below(sl[190])
    for s in sl.values():
        Pb = np.intersect1d(Pb, below(s))
    Qa = above(sl[370])
    for s in sl.values():
        Qa = np.intersect1d(Qa, above(s))
    tab = {pr: Counter() for pr in ((190, 270), (270, 370), (190, 370))}
    for _ in range(tries):
        p, q = rng.choice(Pb), rng.choice(Qa)
        if not R[p, q] or not (0.5 <= t[q] - t[p] < 0.75):
            continue
        info = {}
        for k, s in sl.items():
            comps, Sp, Sq, keep = s.classes(R, p, q)
            if not keep:
                break
            info[k] = (comps, *classify(s, comps, R, p, q, t, x))
        else:
            for (lo, hi), c in tab.items():
                cl, bl, spl, gl = info[lo]
                ch, bh, sph, gh = info[hi]
                if len(cl) != 2 and len(ch) != 2:
                    continue
                if len(cl) != len(ch):
                    c["class count differs"] += 1
                    c["  ...of which a slice is bridged"] += (bl or bh)
                    c["  ...min gap < shadow width"] += min(gl, gh) < max(widths[lo], widths[hi])
                    continue
                lab_lo = {a: i for i, cc in enumerate(cl) for a in cc}
                lab_hi = {a: i for i, cc in enumerate(ch) for a in cc}
                prs = {(lab_lo[a], lab_hi[b]) for a in lab_lo for b in lab_hi
                       if R[sl[lo].A[a], sl[hi].A[b]]}
                bij = len(prs) == 2 and len({u for u, _ in prs}) == 2 and len({v for _, v in prs}) == 2
                key = "bijective" if bij else "NOT bijective"
                c[key] += 1
                if not bij:
                    cross = any(u != v for u, v in prs) and any(u == v for u, v in prs)
                    pat = ("one class reaches both" if len({u for u, _ in prs}) < len(prs) or len({v for _, v in prs}) < len(prs)
                           else "only one class linked" if len(prs) == 1 else "no links" if not prs else "other")
                    c[f"  pattern: {pat}"] += 1
                    small = min(min(len(cc) for cc in cl), min(len(cc) for cc in ch))
                    c[f"  smallest class size {min(small, 3)}{'+' if small >= 3 else ''}"] += 1
                    geo_cross = sum(1 for a in lab_lo for b in lab_hi if R[sl[lo].A[a], sl[hi].A[b]]
                                    and lab_lo[a] != lab_hi[b])
                    c["  relations joining different classes"] += geo_cross
                c[f"  {key}: bridged"] += (bl or bh)
                c[f"  {key}: split"] += (spl or sph)
                c[f"  {key}: min gap < shadow width"] += min(gl, gh) < max(widths[lo], widths[hi])
    print(f"\nseed={seed} n={n}: median shadow width {', '.join(f'{k}:{w:.3f}' for k, w in widths.items())};"
          f" slice mean t {', '.join(f'{k}:{t[s.A].mean():.3f}' for k, s in sl.items())}")
    for pr, c in tab.items():
        tot2 = c["bijective"] + c["NOT bijective"]
        rate = c["NOT bijective"] / tot2 if tot2 else float("nan")
        print(f"  slices {pr} (sep {t[sl[pr[1]].A].mean()-t[sl[pr[0]].A].mean():.3f}):"
              f" NOT-bijective rate {rate:.0%} of {tot2}; {dict(c)}")


if __name__ == "__main__":
    for n in (15, 40):
        for seed in (0, 1):
            run(seed, n)
