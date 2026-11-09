#!/usr/bin/env python3
"""Size of the non-Gaussian part of the slice exponent, on typical fields and in the worst case.

A relative kernel error delta in `perturbed_gap` must be well below 1/N. This measures, on the twisted slice,
    d(Y) = (beta/2) (V(exp(Y) F) - <Y, A Y>),
with F the flat field and A the second-order form of V at F. Numerics, not a proof.

1. Typical fields. Y is a sample of the free ground state squared on the gauge-orthogonal modes:
   Var(Y_k) = 1/(4 beta sinh(omega_k)), 4 sinh^2(omega_k/2) = kappa_k. Reports the std of d, with a bootstrap error,
   and the slope of log std against log N. The Gaussian sampling is exact for the free model only.
2. Worst case. `ValleyChart` needs a pointwise bound over a level set, so a sample mean is not enough. This searches by
   projected gradient ascent for the largest |V(exp(Y) F) - <Y, A Y>| on the ellipsoid <Y, A Y> = sigma, from several
   random starts. A search finds a lower bound on the sup, not the sup. The ratio to sigma^(3/2) is the cubic constant.

Limits: only the potential term is measured, not the kinetic term or the Jacobian. The coordinates are exponential
coordinates on the gauge-orthogonal modes, and a nonlinear change of chart could trade the cubic term of the potential for
terms in the kinetic part and the Jacobian (Morse lemma), so the worst-case number bounds this chart only.
"""
import os
for v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[v] = "2"
import itertools
import json
import sys
import numpy as np
import scipy.sparse


def qmul(a, b):
    w = a[..., 0] * b[..., 0] - a[..., 1] * b[..., 1] - a[..., 2] * b[..., 2] - a[..., 3] * b[..., 3]
    x = a[..., 0] * b[..., 1] + a[..., 1] * b[..., 0] + a[..., 2] * b[..., 3] - a[..., 3] * b[..., 2]
    y = a[..., 0] * b[..., 2] - a[..., 1] * b[..., 3] + a[..., 2] * b[..., 0] + a[..., 3] * b[..., 1]
    z = a[..., 0] * b[..., 3] + a[..., 1] * b[..., 2] - a[..., 2] * b[..., 1] + a[..., 3] * b[..., 0]
    return np.stack([w, x, y, z], axis=-1)


def qinv(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def qexp(Y):
    th = np.linalg.norm(Y, axis=-1, keepdims=True)
    s = np.where(th > 1e-12, np.sin(th) / np.where(th > 1e-12, th, 1.0), 1.0 - th**2 / 6)
    return np.concatenate([np.cos(th), s * Y], axis=-1)


def flat(N):
    F = np.zeros((N, N, N, 3, 4))
    F[..., 0] = 1.0
    F[0, :, :, 0] = [0.0, 1.0, 0.0, 0.0]  # direction 0 on x0 = 0 carries i
    F[:, 0, :, 1] = [0.0, 0.0, 1.0, 0.0]  # direction 1 on x1 = 0 carries j
    return F


def potential(U):
    N = U.shape[0]
    tot = 0.0
    for m, n in [(0, 1), (0, 2), (1, 2)]:
        a = U[..., m, :]
        b = np.roll(U[..., n, :], -1, axis=m)
        c = np.roll(U[..., m, :], -1, axis=n)
        d = U[..., n, :]
        P = qmul(qmul(qmul(a, b), qinv(c)), qinv(d))
        z = np.ones((N, N, N))
        if (m, n) == (0, 1):
            z[0, 0, :] = -1.0
        tot += np.sum(2.0 - 2.0 * z * P[..., 0])
    return tot


def Ad(p):
    a, b, c, d = p
    return np.array([[a*a+b*b-c*c-d*d, 2*(b*c-a*d), 2*(b*d+a*c)],
                     [2*(b*c+a*d), a*a-b*b+c*c-d*d, 2*(c*d-a*b)],
                     [2*(b*d-a*c), 2*(c*d+a*b), a*a-b*b-c*c+d*d]])


def second_order(N, F):
    """The form A with V(exp(Y) F) = <Y, A Y> + O(Y^3), assembled from the flat field."""
    def idx(x, m):
        return (N * N * (x[0] % N) + N * (x[1] % N) + (x[2] % N)) * 3 + m
    def st(x, m):
        return tuple(x[i] + (i == m) for i in range(3))
    def val(x, m):
        return F[x[0] % N, x[1] % N, x[2] % N, m]
    dim = 9 * N**3
    A = np.zeros((dim, dim))
    for x in itertools.product(range(N), repeat=3):
        for m, n in [(0, 1), (0, 2), (1, 2)]:
            a, b, c, d = val(x, m), val(st(x, m), n), val(st(x, n), m), val(x, n)
            z = -1.0 if ((m, n) == (0, 1) and x[0] == 0 and x[1] == 0) else 1.0
            p2 = qmul(qmul(a, b), qinv(c))
            P = qmul(p2, qinv(d))
            Rs = [np.eye(3), Ad(a), -Ad(p2), -Ad(P)]
            ids = [idx(x, m), idx(st(x, m), n), idx(st(x, n), m), idx(x, n)]
            p0 = P[0]
            for j in range(4):
                for k in range(4):
                    A[3*ids[j]:3*ids[j]+3, 3*ids[k]:3*ids[k]+3] += z * p0 * Rs[j].T @ Rs[k]
    return (A + A.T) / 2


def worst_case(N, F, kap_t, vec_t, rng, sigmas=(1e-6, 1e-4), starts=4, steps=250):
    """Projected ascent of |V(exp(Y) F) - <Y, A Y>| on <Y, A Y> = sigma, in coordinates Y = sum a_k v_k / sqrt(kappa_k)."""
    import torch
    torch.set_num_threads(2)
    Ft = torch.tensor(F, dtype=torch.float64)
    vec_t /= np.sqrt(kap_t)  # in place, the modes are not used again
    Vm = torch.from_numpy(vec_t)

    def qmul_t(a, b):
        return torch.stack([
            a[..., 0]*b[..., 0] - a[..., 1]*b[..., 1] - a[..., 2]*b[..., 2] - a[..., 3]*b[..., 3],
            a[..., 0]*b[..., 1] + a[..., 1]*b[..., 0] + a[..., 2]*b[..., 3] - a[..., 3]*b[..., 2],
            a[..., 0]*b[..., 2] - a[..., 1]*b[..., 3] + a[..., 2]*b[..., 0] + a[..., 3]*b[..., 1],
            a[..., 0]*b[..., 3] + a[..., 1]*b[..., 2] - a[..., 2]*b[..., 1] + a[..., 3]*b[..., 0]], dim=-1)

    conj = torch.tensor([1.0, -1.0, -1.0, -1.0], dtype=torch.float64)

    def pot(U):
        tot = 0.0
        for m, n in [(0, 1), (0, 2), (1, 2)]:
            a = U[..., m, :]
            b = torch.roll(U[..., n, :], -1, dims=m)
            c = torch.roll(U[..., m, :], -1, dims=n)
            d = U[..., n, :]
            P = qmul_t(qmul_t(qmul_t(a, b), c * conj), d * conj)
            z = torch.ones((N, N, N), dtype=torch.float64)
            if (m, n) == (0, 1):
                z[0, 0, :] = -1.0
            tot = tot + torch.sum(2.0 - 2.0 * z * P[..., 0])
        return tot

    def deviation(a):
        Y = (Vm @ a).reshape(N, N, N, 3, 3)
        th = torch.sqrt((Y * Y).sum(-1, keepdim=True) + 1e-300)
        ex = torch.cat([torch.cos(th), torch.sin(th) / th * Y], dim=-1)
        return pot(qmul_t(ex, Ft)) - (a * a).sum(), th.max()

    res = {}
    for sigma in sigmas:
        radius = np.sqrt(sigma)
        best, best_rot = 0.0, 0.0
        for _ in range(starts):
            a = torch.tensor(rng.standard_normal(len(kap_t)), dtype=torch.float64)
            a = radius * a / a.norm()
            for it in range(steps):
                a = a.detach().requires_grad_(True)
                dev, rot = deviation(a)
                val = dev.abs()
                val.backward()
                g = a.grad
                g = g - (g @ a) * a / (a @ a)   # tangent part
                step = radius * 0.3 * (1.0 - it / steps) / (g.norm() + 1e-300)
                a = (a + step * g).detach()
                a = radius * a / a.norm()
            dev, rot = deviation(a)
            if abs(float(dev)) > best:
                best, best_rot = abs(float(dev)), float(rot)
        res[str(sigma)] = {"sup_found": best, "cubic_constant": best / sigma**1.5, "rotation_max": best_rot}
        print(f"  sigma={sigma:.0e} largest |deviation| found {best:.4e}, ratio to sigma^1.5 {best / sigma**1.5:.3f}, "
              f"max rotation {best_rot:.4f}", flush=True)
    return res


def main():
    sizes = [int(s) for s in sys.argv[1].split(",")] if len(sys.argv) > 1 else [4, 6, 8]
    betas = [1e3, 1e4, 1e5, 1e6]
    samples = 1000
    rng = np.random.default_rng(20261031)
    out = {"sizes": {}, "samples": samples, "note": "numerics, not a proof; potential term only, exponential coordinates"}
    for N in sizes:
        F = flat(N)
        A = second_order(N, F)
        kap, vec = np.linalg.eigh(A)
        pos = kap > 1e-9
        kap_t, vec_t = kap[pos], vec[:, pos]
        nulls = int((~pos).sum())
        del vec
        A = scipy.sparse.csr_matrix(A)  # A is local; keeping it dense pushes N = 8 past the memory limit
        omega = 2 * np.arcsinh(np.sqrt(kap_t) / 2)
        # check the normalization of A against the action itself
        tY = 1e-4 * vec_t[:, 0].reshape(N, N, N, 3, 3)
        ratio = potential(qmul(qexp(tY), F)) / (tY.reshape(-1) @ A @ tY.reshape(-1))
        rec = {"zero_modes": nulls, "kappa_min": float(kap_t[0]),
               "kappa_min_theory": float(4 * np.sin(np.pi / (2 * N))**2),
               "norm_check": float(ratio), "beta": {}}
        print(f"N={N} zero modes {rec['zero_modes']} (expected {3*N**3}), kappa_min {kap_t[0]:.5f}, "
              f"theory {rec['kappa_min_theory']:.5f}, norm check {ratio:.6f}", flush=True)
        for beta in betas:
            sig = np.sqrt(1.0 / (4 * beta * np.sinh(omega)))
            d = np.zeros(samples)
            rmax = np.zeros(samples)
            for s in range(samples):
                Yv = vec_t @ (sig * rng.standard_normal(sig.shape))
                Y = Yv.reshape(N, N, N, 3, 3)
                d[s] = (beta / 2) * (potential(qmul(qexp(Y), F)) - Yv @ A @ Yv)
                rmax[s] = np.linalg.norm(Y, axis=-1).max()
            boot = np.array([d[rng.integers(0, samples, samples)].std(ddof=1) for _ in range(400)])
            rec["beta"][str(beta)] = {"mean": float(d.mean()), "mean_se": float(d.std(ddof=1) / np.sqrt(samples)),
                                      "std": float(d.std(ddof=1)), "std_se": float(boot.std(ddof=1)),
                                      "absmax": float(np.abs(d).max()), "rotation_max": float(rmax.max())}
            print(f"  beta={beta:9.0f} mean={d.mean():+.4e} std={d.std(ddof=1):.4e} "
                  f"max|d|={np.abs(d).max():.4e} max rotation={rmax.max():.4f} 1/N={1/N:.3f}", flush=True)
        rec["typical_level_times_beta_over_N3"] = float(np.sum(kap_t / (4 * np.sinh(omega))) / N**3)
        rec["worst_case"] = worst_case(N, F, kap_t, vec_t, rng)
        del A, kap
        out["sizes"][str(N)] = rec
    # scaling of the std with N at fixed beta, with a parametric bootstrap on the slope
    fits = {}
    for beta in betas:
        xs = np.log(np.array(sizes, dtype=float))
        st = np.array([out["sizes"][str(N)]["beta"][str(beta)]["std"] for N in sizes])
        se = np.array([out["sizes"][str(N)]["beta"][str(beta)]["std_se"] for N in sizes])
        if len(sizes) > 1:
            slopes = [np.polyfit(xs, np.log(st + se * rng.standard_normal(len(st))), 1)[0] for _ in range(400)]
            fits[str(beta)] = {"slope": float(np.polyfit(xs, np.log(st), 1)[0]), "slope_se": float(np.std(slopes, ddof=1))}
    out["std_slope_in_log_N"] = fits
    print("slope of log std against log N:", fits, flush=True)
    # the worst-case cubic constant
    wfits = {}
    for key in out["sizes"][str(sizes[0])]["worst_case"]:
        cs = [out["sizes"][str(N)]["worst_case"][key]["cubic_constant"] for N in sizes]
        wfits[key] = float(np.polyfit(np.log(np.array(sizes, dtype=float)), np.log(cs), 1)[0]) if len(sizes) > 1 else None
    out["cubic_constant_slope_in_log_N"] = wfits
    print("slope of log cubic constant against log N:", wfits, flush=True)
    # what the two numbers would ask of the coupling, from the fitted power laws, for the potential term only
    if len(sizes) > 1:
        lx = np.log(np.array(sizes, dtype=float))
        c_fit = np.polyfit(lx, np.log([out["sizes"][str(N)]["worst_case"]["0.0001"]["cubic_constant"] for N in sizes]), 1)
        s_lv = 2 * out["sizes"][str(sizes[0])]["typical_level_times_beta_over_N3"]
        out["reading"] = {
            "level_used": "sigma = s N^3 / beta with s = twice the typical level of the free vacuum",
            "s": s_lv,
            "cubic_constant_fit": {"prefactor": float(np.exp(c_fit[1])), "exponent": float(c_fit[0])},
            "worst_case_requirement": "beta >= (1/4) c_N^2 s^3 N^11 for sup |d| <= 1/N at that level",
            "worst_case_requirement_prefactor": float(0.25 * np.exp(2 * c_fit[1]) * s_lv**3),
            "worst_case_requirement_exponent": float(11 + 2 * c_fit[0]),
            "caveat": "a lower bound on the sup in exponential coordinates, potential term only; a search, not a proof",
        }
        print(out["reading"], flush=True)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data",
                        "yang_mills_semiclassical_2026_10_31.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
