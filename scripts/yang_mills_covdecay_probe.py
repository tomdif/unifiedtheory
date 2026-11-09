"""Numerical comparison with TwistedCovarianceDecay.lean. Numerics, not proof.

Part 1 (flat, Fourier). At the flat field the curl-divergence form is the twisted Laplacian on each
component, and with the block penalty it stays diagonal in momentum, so the kernel is an exact FFT.
Covers the three adjoint colours and the real quaternion component, which cov_decay also includes.
L = 0 means no penalty; the real sector then has a zero mode and is skipped.

These kernels are bounded by the proved bounds at every tested point, but that comparison has no power: each
row records bound_min (the bound's minimum over the torus) against kernel_max, and bound_min > kernel_max means the
check could not have failed. What carries information is the kernel itself: the diagonal G00 is the sharp constant
in the point-energy inequality, and the fitted rates are compared with the proved ones, slowest sector first.

Part 2 (non-flat, conjugate gradient). The same form at a background with small defects, built as a
random gauge transform of the flat field times small link noise. In-hypothesis backgrounds here are gauge
transforms of flat plus tiny noise, so they do not test a background far from flat. Same no-power caveat.

Part 3 (the inequalities inside the Sobolev proof). block_point on the box indicator, where equality should hold,
and sobolev_scalar on massive kernels and box indicators, which report how close the inequality comes to failing.
"""
import json
import os
import time

for v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[v] = "2"

import numpy as np  # noqa: E402

OUT = "/Users/thomasdifiore/unifiedtheory/data/yang_mills_covdecay_2026_10_31.json"


def momenta(N, anti):
    k = 2 * np.pi * np.arange(N) / N
    return k + np.pi / N if anti else k


def kernel(N, L, e1, e2):
    """Exact kernel G(x, 0) of Sum_nu D_nu^* D_nu + (1/4L^2) B^* B for one colour; L = 0 means no penalty."""
    ks = [momenta(N, False), momenta(N, e1), momenta(N, e2), momenta(N, False)]
    grids = np.meshgrid(*ks, indexing="ij", sparse=True)
    lap = sum(4 * np.sin(g / 2) ** 2 for g in grids)
    if L > 0:
        block = 1.0
        for g in grids:
            s = np.sin(L * g / 2)
            d = L * np.sin(g / 2)
            with np.errstate(invalid="ignore", divide="ignore"):
                f = np.where(np.abs(d) < 1e-12, 1.0, s / d)
            block = block * f ** 2
        lap = lap + block / (4 * L ** 2)
    with np.errstate(divide="ignore"):
        inv = 1.0 / lap
    # Twisted directions are antiperiodic: the phase e^{i pi x / N} has modulus one, so the modulus of
    # the plain inverse FFT of 1/lap(k) is the modulus of the kernel on the fundamental domain.
    g = np.fft.ifftn(inv)
    return np.abs(g), float(np.min(lap)), float(np.max(lap))


def torus_dist(N):
    c = np.minimum(np.arange(N), N - np.arange(N))
    grids = np.meshgrid(c, c, c, c, indexing="ij", sparse=True)
    return sum(grids)


def envelope(g, d):
    dmax = int(d.max())
    env = np.zeros(dmax + 1)
    np.maximum.at(env, d.ravel(), g.ravel())
    return env


def rate_fit(env, lo, hi):
    ds = np.arange(lo, hi + 1)
    vals = env[lo: hi + 1]
    keep = vals > 1e-13
    if keep.sum() < 2:
        return None
    return float(-np.polyfit(ds[keep], np.log(vals[keep]), 1)[0])


SECTORS = {"i": (False, True), "j": (True, False), "k": (True, True), "real": (False, False)}


def bounds(N, L, dm):
    """The proved bounds as functions of dist1, by name. All need L <= N for the uniform ones."""
    d = np.arange(dm + 1)
    if L == 0:
        return {"flat_point": 9.0 * np.ones_like(d, dtype=float)}
    return {
        "cov_point": 63.0 * np.ones_like(d, dtype=float),
        "cov_decay_unif": 126.0 * np.exp(-d / (32 * L)),
        "cov_decay": 16.0 * L ** 2 * np.exp(-d / (32 * L)),
    }


def part1():
    rows = []
    # N = 56 is the largest size that stays under the 1.5 GB limit (N = 64 reached 1.9 GB). The last row of the list
    # is the corner N = L, where the real sector's zero mode makes the diagonal largest.
    for N, L in [(8, 0), (16, 0), (32, 0), (48, 0), (16, 1), (32, 1), (48, 1), (56, 1), (32, 2), (48, 2), (56, 2),
                 (32, 4), (48, 4), (56, 4), (48, 6), (56, 6), (56, 8),
                 (1, 1), (2, 1), (2, 2), (3, 3), (4, 4), (8, 8)]:
        d = torus_dist(N)
        per = []
        for name, (e1, e2) in SECTORS.items():
            if L == 0 and name == "real":
                continue
            g, lo, hi = kernel(N, L, e1, e2)
            env = envelope(g, d)
            dm = len(env) - 1
            b = bounds(N, L, dm)
            row = {
                "N": N, "L": L, "sector": name,
                "G00": float(g[0, 0, 0, 0]),
                "kernel_max": float(env.max()),
                "spectrum_lo": lo, "spectrum_hi": hi,
                "lam_formula": float(4 * np.sin(np.pi / (2 * N)) ** 2),
                "fit_rate": rate_fit(env, max(2, dm // 4), dm // 2 + dm // 8),
                "bound_min": {k: float(v.min()) for k, v in b.items()},
                "check_has_power": {k: bool(v.min() < env.max()) for k, v in b.items()},
                "max_env_over_bound": {k: float(np.max(env / v)) for k, v in b.items()},
                "env_at_d": {str(k): float(env[k]) for k in (0, 1, 2, 4, 8, 16, 24, 32) if k <= dm},
                "d2_env_at_d": {str(k): float(k ** 2 * env[k]) for k in (1, 2, 4, 8, 16, 24, 32) if k <= dm},
            }
            per.append(row)
        rows.extend(per)
        with_fit = [r for r in per if r["fit_rate"] is not None]
        slow = min(with_fit, key=lambda r: r["fit_rate"]) if with_fit else None
        print("N", N, "L", L, "G00 by sector", {r["sector"]: round(r["G00"], 4) for r in per},
              "slowest fit", (slow["sector"], round(slow["fit_rate"], 4)) if slow else None,
              "proved rate", None if L == 0 else round(1 / (32 * L), 5), flush=True)
        del d
    return rows


def rate_summary(rows):
    """Slowest-sector fitted rate against the proved rate, and its drift with N, for tori with N at least 4 L."""
    out = []
    for L in sorted({r["L"] for r in rows if r["L"] > 0}):
        fits = {}
        for N in sorted({r["N"] for r in rows if r["L"] == L and r["N"] >= 4 * L}):
            vals = [r["fit_rate"] for r in rows if r["L"] == L and r["N"] == N and r["fit_rate"] is not None]
            if vals:
                fits[N] = min(vals)
        if not fits:
            continue
        top = max(fits)
        out.append({
            "L": L, "slowest_fit_by_N": fits, "proved_rate": 1 / (32 * L),
            "looseness_at_largest_N": fits[top] * 32 * L, "rate_times_L_at_largest_N": fits[top] * L,
            "exact_rate_L1_diagonal": float(2 * np.arcsinh(1 / 8)) if L == 1 else None,
        })
    return out


def thresholds():
    """Distances at which each decay bound first says more than its companion, by arithmetic."""
    return {
        "cov_decay_vs_coercivity_8.547_L2": float(32 * np.log(16 / (1000 / 117))),
        "cov_decay_unif_vs_cov_point": float(32 * np.log(2)),
        "hess_decay_vs_coercivity_16_L2": float(100 * np.log(2)),
        "hess_decay_unif_vs_hess_point": float(100 * np.log(2)),
        "cov_decay_unif_below_measured_G00_0.155": float(32 * np.log(126 / 0.155)),
        "note": "each value is the threshold in units of L; dist1 is at most 2N on the torus",
        "hess_decay_unif_below_measured_G00_over_beta": float(100 * np.log(232 / 0.155)),
    }


# ---- Part 2: covariant form on the imaginary sector, matrix free ----

def rand_su2(shape, rng):
    q = rng.normal(size=shape + (4,))
    return q / np.linalg.norm(q, axis=-1, keepdims=True)


def qmul(a, b):
    return np.stack([
        a[..., 0] * b[..., 0] - a[..., 1] * b[..., 1] - a[..., 2] * b[..., 2] - a[..., 3] * b[..., 3],
        a[..., 0] * b[..., 1] + a[..., 1] * b[..., 0] + a[..., 2] * b[..., 3] - a[..., 3] * b[..., 2],
        a[..., 0] * b[..., 2] - a[..., 1] * b[..., 3] + a[..., 2] * b[..., 0] + a[..., 3] * b[..., 1],
        a[..., 0] * b[..., 3] + a[..., 1] * b[..., 2] - a[..., 2] * b[..., 1] + a[..., 3] * b[..., 0],
    ], axis=-1)


def qinv(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def adjoint(q):
    a, b, c, d = q[..., 0], q[..., 1], q[..., 2], q[..., 3]
    r = np.empty(q.shape[:-1] + (3, 3))
    r[..., 0, 0] = a * a + b * b - c * c - d * d
    r[..., 0, 1] = 2 * (b * c - a * d)
    r[..., 0, 2] = 2 * (b * d + a * c)
    r[..., 1, 0] = 2 * (b * c + a * d)
    r[..., 1, 1] = a * a - b * b + c * c - d * d
    r[..., 1, 2] = 2 * (c * d - a * b)
    r[..., 2, 0] = 2 * (b * d - a * c)
    r[..., 2, 1] = 2 * (c * d + a * b)
    r[..., 2, 2] = a * a - b * b - c * c + d * d
    return r


def flat_links(N):
    u = np.zeros((4, N, N, N, N, 4))
    u[..., 0] = 1.0
    u[1, :, 0, :, :, :] = np.array([0.0, 1.0, 0.0, 0.0])
    u[2, :, :, 0, :, :] = np.array([0.0, 0.0, 1.0, 0.0])
    return u


def build_background(N, gauge, noise, rng):
    u = flat_links(N)
    if noise > 0:
        eps = rng.normal(size=u.shape[:-1] + (3,)) * noise
        e = np.concatenate([np.ones(u.shape[:-1] + (1,)), eps], axis=-1)
        e = e / np.linalg.norm(e, axis=-1, keepdims=True)
        u = qmul(e, u)
    if gauge:
        g = rand_su2((N, N, N, N), rng)
        for mu in range(4):
            u[mu] = qmul(qmul(g, u[mu]), qinv(np.roll(g, -1, axis=mu)))
    return u


def defects(u, N):
    worst = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            p = qmul(qmul(qmul(u[mu], np.roll(u[nu], -1, axis=mu)), qinv(np.roll(u[mu], -1, axis=nu))), qinv(u[nu]))
            c = np.zeros_like(p)
            c[..., 0] = 1.0
            # The plaquette is near +1 or the twist -1. The nearer one is the right one for small noise.
            d = np.minimum(np.linalg.norm(p - c, axis=-1), np.linalg.norm(p + c, axis=-1))
            worst = max(worst, float(d.max()))
    return worst


class Form:
    def __init__(self, u, N, L):
        self.N, self.L = N, L
        self.R = adjoint(u)  # shape (4, N,N,N,N, 3,3)

    def T(self, mu, f):
        return np.einsum("...ij,...j->...i", self.R[mu], np.roll(f, -1, axis=mu))

    def S(self, mu, f):
        return np.roll(np.einsum("...ji,...j->...i", self.R[mu], f), 1, axis=mu)

    def D(self, mu, f):
        return self.T(mu, f) - f

    def Ds(self, mu, f):
        return self.S(mu, f) - f

    def avg(self, mu, f):
        out = f.copy()
        cur = f
        for _ in range(self.L - 1):
            cur = self.T(mu, cur)
            out = out + cur
        return out / self.L

    def avgs(self, mu, f):
        out = f.copy()
        cur = f
        for _ in range(self.L - 1):
            cur = self.S(mu, cur)
            out = out + cur
        return out / self.L

    def block(self, f):
        return self.avg(0, self.avg(1, self.avg(2, self.avg(3, f))))

    def blocks(self, f):
        return self.avgs(3, self.avgs(2, self.avgs(1, self.avgs(0, f))))

    def apply(self, w):
        out = np.zeros_like(w)
        for mu in range(4):
            for nu in range(mu + 1, 4):
                c = self.D(mu, w[nu]) - self.D(nu, w[mu])
                out[nu] += self.Ds(mu, c)
                out[mu] -= self.Ds(nu, c)
        d = sum(self.Ds(mu, w[mu]) for mu in range(4))
        for mu in range(4):
            out[mu] += self.D(mu, d)
            out[mu] += self.blocks(self.block(w[mu])) / (4 * self.L ** 2)
        return out


def cg(form, b, tol=1e-10, maxit=4000):
    x = np.zeros_like(b)
    r = b.copy()
    p = r.copy()
    rs = float(np.sum(r * r))
    bn = rs
    for it in range(maxit):
        ap = form.apply(p)
        alpha = rs / float(np.sum(p * ap))
        x += alpha * p
        r -= alpha * ap
        new = float(np.sum(r * r))
        if new < tol ** 2 * bn:
            return x, it + 1
        p = r + (new / rs) * p
        rs = new
    return x, maxit


def part2():
    rng = np.random.default_rng(20261031)
    rows = []
    for N, L, gauge, noise in [(8, 1, False, 0.0), (8, 2, False, 0.0), (8, 1, True, 0.0001),
                               (8, 2, True, 0.00002), (8, 2, True, 0.02), (8, 2, True, 0.1),
                               (12, 2, True, 0.00002)]:
        t0 = time.time()
        u = build_background(N, gauge, noise, rng)
        dmax = defects(u, N)
        form = Form(u, N, L)
        b = np.zeros((4, N, N, N, N, 3))
        b[0, 0, 0, 0, 0, 0] = 1.0
        x, its = cg(form, b)
        nrm = np.linalg.norm(x, axis=-1)
        link = np.max(nrm, axis=0)
        d = torus_dist(N)
        env = envelope(link, d)
        bound = 16 * L ** 2 * np.exp(-np.arange(len(env)) / (32 * L))
        row = {
            "N": N, "L": L, "gauge": gauge, "noise": noise, "max_defect": dmax,
            "threshold": 1 / (1000 * L ** 2), "in_hypothesis": bool(dmax <= 1 / (1000 * L ** 2)),
            "cg_iters": its, "env": [float(v) for v in env],
            "max_env_over_bound": float(np.max(env / bound)),
            "check_has_power": bool(bound.min() < env.max()),
            "cov_point_ratio": float(env.max() / 63.0),
            "fit_rate": rate_fit(env, 2, len(env) - 3), "proved_rate": 1 / (32 * L),
            "seconds": round(time.time() - t0, 1),
        }
        if not gauge and noise == 0.0:
            # Source in colour i: this must reproduce the exact Fourier kernel, as a check of the code.
            exact, _, _ = kernel(N, L, False, True)
            row["fourier_check_max_diff"] = float(np.max(np.abs(np.abs(x[0, ..., 0]) - exact)))
            row["other_components_max"] = float(max(np.max(np.abs(x[1:])), np.max(np.abs(x[0, ..., 1:]))))
            print("check against Fourier", row["fourier_check_max_diff"], row["other_components_max"], flush=True)
        rows.append(row)
        print({k: row[k] for k in ("N", "L", "noise", "max_defect", "in_hypothesis", "cg_iters", "max_env_over_bound", "fit_rate", "seconds")}, flush=True)
    return rows


# ---- Part 3: the inequalities inside the Sobolev proof ----

def grad_sum(a):
    """The sum over the four directions of the L2 norm of the plain difference."""
    return sum(float(np.linalg.norm(np.roll(a, -1, axis=mu) - a)) for mu in range(4))


def sobolev_rhs(a, K):
    return grad_sum(a) + float(np.linalg.norm(a)) / 4 ** K


def box_indicator(N, ell):
    a = np.zeros((N, N, N, N))
    a[:ell, :ell, :ell, :ell] = 1.0
    return a


def box_average_at_origin(b, ell):
    return float(np.mean(b[:ell, :ell, :ell, :ell]))


def massive_kernel(N, m2):
    k = momenta(N, False)
    grids = np.meshgrid(k, k, k, k, indexing="ij", sparse=True)
    lap = sum(4 * np.sin(g / 2) ** 2 for g in grids) + m2
    return np.real(np.fft.ifftn(1.0 / lap))


def part3():
    block_rows, sob_rows = [], []
    for N, ell in [(8, 2), (8, 8), (16, 4), (16, 16), (32, 8), (32, 32)]:
        b = box_indicator(N, ell)
        val = ell ** 2 * abs(box_average_at_origin(b, ell)) / float(np.linalg.norm(b))
        block_rows.append({"N": N, "l": ell, "l2_avg_over_norm": val})
    for N in (8, 16, 32):
        Kmax = int(np.log2(N))
        for m2 in (1e-1, 1e-2, 1e-3, 1e-4):
            a = massive_kernel(N, m2)
            a = a / np.abs(a).max()
            for K in range(Kmax + 1):
                sob_rows.append({"N": N, "family": "massive_kernel", "m2": m2, "K": K,
                                 "lhs_over_rhs": float(np.abs(a).max() / sobolev_rhs(a, K))})
        for ell in (1, 2, 4, 8, 16):
            if ell > N:
                continue
            a = box_indicator(N, ell)
            for K in range(Kmax + 1):
                sob_rows.append({"N": N, "family": "box_indicator", "l": ell, "K": K,
                                 "lhs_over_rhs": float(np.abs(a).max() / sobolev_rhs(a, K))})
    worst = max(sob_rows, key=lambda r: r["lhs_over_rhs"])
    worst_kernel = max((r for r in sob_rows if r["family"] == "massive_kernel"), key=lambda r: r["lhs_over_rhs"])
    worst_nonconstant = max((r for r in sob_rows if r["family"] == "box_indicator" and r["l"] < r["N"]),
                            key=lambda r: r["lhs_over_rhs"])
    print("block_point equality check", [round(r["l2_avg_over_norm"], 12) for r in block_rows], flush=True)
    print("sobolev_scalar largest lhs/rhs: constant function", worst, flush=True)
    print("  on massive kernels", worst_kernel, flush=True)
    print("  on nonconstant box indicators", worst_nonconstant, flush=True)
    return {"block_point_on_box_indicator": block_rows, "sobolev_scalar": sob_rows, "worst": worst,
            "worst_massive_kernel": worst_kernel, "worst_nonconstant_box": worst_nonconstant}


if __name__ == "__main__":
    flat = part1()
    out = {"note": "numerics, not proof", "flat_fourier": flat, "rate_summary": rate_summary(flat),
           "thresholds_in_units_of_L": thresholds(), "sobolev_internal": part3(), "covariant_cg": part2()}
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", OUT)
