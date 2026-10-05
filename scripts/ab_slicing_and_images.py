"""Three follow-ups to ab_chain_pair_holonomy.py on the 1+1 cylinder (L = 1).

A. Slicing independence with order-chosen slices.  Slices are
   A_k = minimal elements of {x : |J-(x)| >= k}, extended greedily to a
   MAXIMAL antichain (we first report how many elements the raw set misses).
   For pairs p < q below/above two slices A (lower), B (upper), chains
   p < a < b < q (a in A, b in B) carry labels (class_A, class_B).  We check
   (i) the class map A -> B is a bijection, and (ii) the holonomy between the
   two classes agrees on A and B once ONE global orientation sign is fixed.
B. Short-pair control and step-7 keep rate: pairs binned by t_q - t_p
   (coordinates used for binning only).  Below L/2 there must be one class.
C. Images.  Continuum retarded Green function on the cylinder sums images,
   G = 1/2 sum_k J0(m tau_k).  Johnston's 1+1 causal-set propagator
   K = 1/2 C (I + m^2/(2 rho) C)^{-1} is built from relations, so test which
   it matches once two images are open (t_q - t_p > L/2).

Usage: python3.11 scripts/ab_slicing_and_images.py
"""
import numpy as np
from collections import Counter, defaultdict
from scipy.special import j0
from scipy.linalg import solve_triangular
from ab_chain_pair_holonomy import shadows, dowker, integral_cocycle, components, path, sub_b1


def sprinkle(rng, rho, T):
    n = rng.poisson(rho * T)
    t = np.sort(rng.uniform(0, T, n))
    x = rng.uniform(0, 1, n)
    dx = np.abs(x[None, :] - x[:, None]) % 1.0
    dx = np.minimum(dx, 1.0 - dx)
    return t, x, dx, (t[None, :] - t[:, None]) > dx


def maximal_slice(R, past, k):
    up = np.flatnonzero(past >= k)
    A = list(up[~R[np.ix_(up, up)].any(axis=0)])
    comp = R[:, A].any(axis=1) | R[A, :].any(axis=0)
    comp[A] = True
    missing = np.flatnonzero(~comp)
    added = 0
    for x in sorted(missing, key=lambda y: abs(past[y] - k)):
        if not (R[x, A].any() or R[A, x].any()):
            A.append(x)
            added += 1
    A = np.array(sorted(A))
    assert not R[np.ix_(A, A)].any()
    comp = R[:, A].any(axis=1) | R[A, :].any(axis=0)
    comp[A] = True
    assert comp.all(), "not maximal"
    return A, len(missing), added


class Slice:
    def __init__(self, R, A, n):
        self.A = A
        S = shadows(R, A, n)
        self.edges, self.tris, eid, self.b0, self.b1 = dowker(len(A), S)
        self.ok = (self.b0, self.b1) == (1, 1)
        if self.ok:
            self.omega, self.adj = integral_cocycle(len(A), self.edges, self.tris, eid)

    def hol(self, loop):
        return sum(self.omega[(a, b)] if a < b else -self.omega[(b, a)]
                   for a, b in zip(loop[:-1], loop[1:]))

    def classes(self, R, p, q):
        """Components of J+(p) ∩ J-(q) ∩ A, and whether the step-7 filter passes."""
        Sp = set(np.flatnonzero(R[p, self.A]))
        Sq = set(np.flatnonzero(R[self.A, q]))
        comps = components(self.adj, Sp & Sq)
        keep = sub_b1(Sp, self.edges, self.tris) == 0 and sub_b1(Sq, self.edges, self.tris) == 0
        return comps, Sp, Sq, keep

    def h(self, Sp, Sq, a1, a2):
        l1, l2 = path(self.adj, Sp, a1, a2), path(self.adj, Sq, a2, a1)
        return None if l1 is None or l2 is None else int(round(self.hol(l1 + l2[1:])))


def part_ab(rho=3000, T=1.4, n=40, seed=0, npairs=4000):
    rng = np.random.default_rng(seed)
    t, x, dx, R = sprinkle(rng, rho, T)
    past = R.sum(axis=0)
    print(f"\n=== A/B: rho={rho} n={n} seed={seed} N={len(t)}")
    slices = {}
    for k in (190, 270, 370):          # ~ t = 0.25, 0.30, 0.35 (past area t^2)
        A, miss, added = maximal_slice(R, past, k)
        S = Slice(R, A, n)
        slices[k] = S
        print(f"slice k={k}: |raw minimal set| misses {miss} elements; greedy added {added};"
              f" |A|={len(A)}, mean t={t[A].mean():.3f}±{t[A].std():.3f}; Dowker b0,b1={S.b0},{S.b1}")
    # random greedy maximal antichain: stress test of 'any maximal antichain'
    order = rng.permutation(len(t))
    G = []
    for y in order:
        if not any(R[y, g] or R[g, y] for g in G):
            G.append(y)
    Sg = Slice(R, np.array(sorted(G)), n)
    print(f"random greedy maximal antichain: |A|={len(G)}, t-range {t[G].min():.2f}–{t[G].max():.2f};"
          f" Dowker b0,b1={Sg.b0},{Sg.b1}")
    lo, hi = slices[190], slices[370]
    if not (lo.ok and hi.ok):
        print("slices not (1,1); skip")
        return
    below = lambda P: np.flatnonzero(R[:, P.A].any(axis=1) & ~R[P.A, :].any(axis=0))
    above = lambda P: np.flatnonzero(R[P.A, :].any(axis=0) & ~R[:, P.A].any(axis=1))
    Pb = np.intersect1d(below(lo), below(hi))
    Qa = np.intersect1d(above(lo), above(hi))
    bins = [0, 0.3, 0.4, 0.45, 0.5, 0.55, 0.6, 0.7, 0.85, 2.0]
    binstat = defaultdict(Counter)
    trans = Counter()
    sign = None
    for it in range(npairs + 40000):
        p, q = rng.choice(Pb), rng.choice(Qa)
        if not R[p, q]:
            continue
        dt = t[q] - t[p]
        # first npairs: unbiased (part B); remainder: oversample 0.5-0.75 band for part A
        if it >= npairs and not (0.5 <= dt < 0.75):
            continue
        if it >= npairs:
            b = -1
        else:
            b = np.digitize(dt, bins) - 1
        cl, Sp, Sq, keep = lo.classes(R, p, q)
        if b >= 0:
            binstat[b]["pairs"] += 1
            binstat[b]["kept"] += keep
            if keep:
                binstat[b][f"{len(cl)} class"] += 1
        ch, Sph, Sqh, keeph = hi.classes(R, p, q)
        if not (keep and keeph and len(cl) == 2 and len(ch) == 2):
            continue
        # chains p < a < b < q: class map lower -> upper
        lab_lo = {a: i for i, c in enumerate(cl) for a in c}
        lab_hi = {a: i for i, c in enumerate(ch) for a in c}
        pairs = set()
        for a in lab_lo:
            for bb in lab_hi:
                if R[lo.A[a], hi.A[bb]]:
                    pairs.add((lab_lo[a], lab_hi[bb]))
        if len(pairs) != 2 or len({u for u, _ in pairs}) != 2 or len({v for _, v in pairs}) != 2:
            trans["class map not a bijection"] += 1
            continue
        mp = dict(pairs)
        a1, a2 = next(iter(cl[0])), next(iter(cl[1]))
        b1_, b2_ = next(iter(ch[mp[0]])), next(iter(ch[mp[1]]))
        hl, hh = lo.h(Sp, Sq, a1, a2), hi.h(Sph, Sqh, b1_, b2_)
        if hl is None or hh is None:
            trans["path missing"] += 1
            continue
        if sign is None:
            sign = hh * hl
            trans["orientation reference"] += 1
            continue
        trans["agree" if hh == sign * hl else f"DISAGREE ({hl},{hh})"] += 1
    print("B: t_q - t_p bin -> pairs, step-7 kept, class counts among kept")
    for b in sorted(binstat):
        s = binstat[b]
        cls = {k: v for k, v in s.items() if "class" in k}
        print(f"  [{bins[b]:.2f},{bins[b+1]:.2f}): pairs={s['pairs']:4d} kept={s['kept']:4d}"
              f" ({s['kept']/max(s['pairs'],1):.0%})  {cls}")
    print("A: lower (k=190) vs upper (k=370) slice, two-class pairs:", dict(trans))


def part_c(rho=2000, T=1.0, m=4.0, seed=0):
    rng = np.random.default_rng(seed)
    t, x, dx, R = sprinkle(rng, rho, T)
    N = len(t)
    C = R.astype(float)          # strictly upper triangular (sorted by t)
    Mtx = np.eye(N) + (m * m / (2 * rho)) * C
    K = 0.5 * solve_triangular(Mtx.T, C.T, lower=True, unit_diagonal=True).T  # K = ½ C M^{-1}
    # (C and M commute: both polynomials in C; so ½ C M^{-1} = ½ M^{-1} C.)
    i, j = np.nonzero(R)
    sel = rng.choice(len(i), size=min(len(i), 400000), replace=False)
    i, j = i[sel], j[sel]
    DT = t[j] - t[i]
    raw = (x[j] - x[i]) % 1.0
    G1 = np.zeros(len(i))
    Gimg = np.zeros(len(i))
    nimg = np.zeros(len(i), int)
    for k in range(-3, 4):
        d = np.abs(raw + k)
        inside = d < DT
        tau = np.sqrt(np.maximum(DT**2 - d**2, 0))
        Gimg += np.where(inside, 0.5 * j0(m * tau), 0)
        nimg += inside
    dmin = np.minimum(raw, 1 - raw)
    G1 = 0.5 * j0(m * np.sqrt(DT**2 - dmin**2))
    Kij = K[i, j]
    print(f"\n=== C: Johnston K vs continuum, rho={rho} m={m} N={N}, {len(i)} related pairs")
    print("  images  Δt-bin        pairs   <K>      <½J0 one image>  <½ΣJ0 images>   <½C>")
    for ni in (1, 2):
        for lo_, hi_ in ((0.0, 0.3), (0.3, 0.5), (0.5, 0.7), (0.7, 1.0)):
            s = (nimg == ni) & (DT >= lo_) & (DT < hi_)
            if s.sum() < 50:
                continue
            print(f"  {ni:6d}  [{lo_:.1f},{hi_:.1f})  {s.sum():8d}  {Kij[s].mean():+.4f}"
                  f"   {G1[s].mean():+.4f}          {Gimg[s].mean():+.4f}        0.5000")


if __name__ == "__main__":
    for seed in (0, 1):
        part_ab(seed=seed)
    for seed in (0, 1):
        part_c(seed=seed)


def part_d(rho=1500, T=1.0, m=4.0, seed=0, Phi=(0.0, np.pi / 2, np.pi)):
    """Z-cover test: Johnston K on the unwrapped strip (3 deck copies), then
    K_Phi(x, y) = sum_k e^{i k Phi} K_cover(x, y + k).  At Phi = 0 this should
    reproduce the continuum image sum; Phi weights the deck classes."""
    rng = np.random.default_rng(seed)
    n = rng.poisson(rho * T)
    t0, x0 = rng.uniform(0, T, n), rng.uniform(0, 1, n)
    t = np.tile(t0, 3)
    x = np.concatenate([x0 - 1, x0, x0 + 1])
    copy = np.repeat([-1, 0, 1], n)
    o = np.argsort(t, kind="stable")
    t, x, copy = t[o], x[o], copy[o]
    base = np.tile(np.arange(n), 3)[o]
    R = (t[None, :] - t[:, None]) > np.abs(x[None, :] - x[:, None])
    C = R.astype(float)
    del R
    Mtx = np.eye(len(t)) + (m * m / (2 * rho)) * C
    K = 0.5 * solve_triangular(Mtx.T, C.T, lower=True, unit_diagonal=True).T
    del Mtx, C
    pos = {(b, c): i for i, (b, c) in enumerate(zip(base, copy))}
    src = np.array([pos[(b, 0)] for b in range(n)])
    tgt = {k: np.array([pos[(b, k)] for b in range(n)]) for k in (-1, 0, 1)}
    I, J = np.meshgrid(np.arange(n), np.arange(n), indexing="ij")
    I, J = I.ravel(), J.ravel()
    DT = t0[J] - t0[I]
    keep = DT > 0
    I, J, DT = I[keep], J[keep], DT[keep]
    sel = rng.choice(len(I), size=min(len(I), 300000), replace=False)
    I, J, DT = I[sel], J[sel], DT[sel]
    Kk = {k: K[src[I], tgt[k][J]] for k in (-1, 0, 1)}
    Gk, nimg = {}, np.zeros(len(I), int)
    for k in (-1, 0, 1):
        d = np.abs(x0[J] + k - x0[I])
        inside = d < DT
        Gk[k] = np.where(inside, 0.5 * j0(m * np.sqrt(np.maximum(DT**2 - d**2, 0))), 0)
        nimg += inside
    print(f"\n=== D: Z-cover, rho={rho} m={m} n={n} (cover N={3*n})")
    print("  images Δt-bin      pairs  Phi    <Re K_Phi cover>  <continuum Σ e^{ikΦ} ½J0>")
    for ni in (1, 2):
        for lo_, hi_ in ((0.3, 0.5), (0.5, 0.7), (0.7, 1.0)):
            s = (nimg == ni) & (DT >= lo_) & (DT < hi_)
            if s.sum() < 50:
                continue
            for ph in Phi:
                Kp = sum(np.exp(1j * k * ph) * Kk[k][s] for k in (-1, 0, 1))
                Gp = sum(np.exp(1j * k * ph) * Gk[k][s] for k in (-1, 0, 1))
                print(f"  {ni:5d} [{lo_:.1f},{hi_:.1f}) {s.sum():7d}  {ph:4.2f}   {Kp.real.mean():+.4f}"
                      f"           {Gp.real.mean():+.4f}")


if __name__ == "__main__":
    part_d()
