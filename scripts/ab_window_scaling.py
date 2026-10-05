"""Scaling of the thickened-antichain flux window with sprinkling density and size.

For the 1+1 cylinder S^1(L) x [0,T] we find, per seed, the contiguous window of
thickening n containing the first n with (b0=1, b1=1, |winding|=1, all
triangles flat), and fit n_lo, n_hi against rho and L.
Hypothesis: n_lo ~ const (discreteness), n_hi ~ rho * L^2 (shadows wrap the
circle at a fixed spacetime volume ~ L^2), so the window ratio n_hi/n_lo
grows without bound in the continuum limit.

Usage: python3.11 scripts/ab_window_scaling.py
"""
import numpy as np
import sys
import ab_thickened_antichain as m

NS = sorted(set(int(round(x)) for x in np.geomspace(2, 4000, 48)))


def sprinkle_cyl(rng, rho, L, T):
    n = rng.poisson(rho * L * T)
    t, x = rng.uniform(0, T, n), rng.uniform(0, L, n)
    dx = np.abs(x[None, :] - x[:, None]) % L
    dx = np.minimum(dx, L - dx)
    R = (t[None, :] - t[:, None]) > dx
    return t, 2 * np.pi * x / L, R


def window(t, ang, R, t0):
    A = m.antichain(t, R, t0)
    rows = m.nerve_betti(t, ang, R, A, NS)
    good = [r[4] == 1 and r[5] == 1 and r[7] == 0 and abs(r[8] or 0) == 1 for r in rows]
    if not any(good):
        return None
    i = good.index(True)
    j = i
    while j + 1 < len(good) and good[j + 1]:
        j += 1
    # stop scanning past the window once shadows wrap (the slab is tall enough)
    return NS[i], NS[j], j + 1 < len(good)


def main():
    configs = [(rho, 1.0) for rho in (1000, 2000, 4000, 7000, 10000)]
    configs += [(2000, 2.0), (1000, 2.0)]
    seeds = 5
    rows = []
    print(f"{'rho':>6} {'L':>4} {'seed':>4}  n_lo  n_hi  closed")
    for rho, L in configs:
        for s in range(seeds):
            rng = np.random.default_rng(1000 + s)
            m.rng = rng
            t, ang, R = sprinkle_cyl(rng, rho, L, 1.0 * L)
            w = window(t, ang, R, 0.3 * L)
            del R
            print(f"{rho:6d} {L:4.1f} {s:4d}  {w}")
            sys.stdout.flush()
            if w:
                rows.append((rho, L, w[0], w[1], w[2]))
    rows = np.array(rows, float)
    print("\nper-config medians: rho L n_lo n_hi ratio")
    for rho, L in configs:
        sel = (rows[:, 0] == rho) & (rows[:, 1] == L)
        if sel.any():
            lo, hi = np.median(rows[sel, 2]), np.median(rows[sel, 3])
            print(f"{rho:6.0f} {L:4.1f} {lo:6.1f} {hi:7.1f} {hi/lo:6.1f}")
    closed = rows[rows[:, 4] == 1]
    X = np.c_[np.ones(len(closed)), np.log(closed[:, 0]), np.log(closed[:, 1])]
    for k, name in ((2, "n_lo"), (3, "n_hi")):
        coef, *_ = np.linalg.lstsq(X, np.log(closed[:, k]), rcond=None)
        res = np.log(closed[:, k]) - X @ coef
        se = np.sqrt(np.diag(np.linalg.inv(X.T @ X)) * res.var(ddof=3))
        print(f"fit log {name} = {coef[0]:.2f} + ({coef[1]:.2f}±{se[1]:.2f}) log rho"
              f" + ({coef[2]:.2f}±{se[2]:.2f}) log L   (closed windows, n={len(closed)})")


if __name__ == "__main__":
    main()
