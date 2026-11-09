#!/usr/bin/env python3
"""Numerics, not proof. Wilson flow on the twisted lattice (TwistedFlow.lean) at unit coupling.

Deterministic checks, on single fields, of the normalization and of the statements of TwistedFlow.lean:
  - the finite-difference rate of the action against -||V||^2,
  - the flat field has zero action,
  - the constant-flux fields `critLink` are fixed points, with action N^4 (2 - 2 cos((2m+1) pi / N^2)),
  - near the flat field, grad_dom (3 S <= N^2 F) and the decay rate against 3/N^2,
  - forceSq <= 96 S and the link ceiling ||V_e|| <= 12.

Monte Carlo of the twisted law by checkerboard Metropolis, flowed by Luescher's third-order integrator. Reports the
jackknife error over the flowed samples, a binning estimate of the autocorrelation at flow time zero, the first and
second half of the samples, and the step-size change on one field. Flowed observables may have longer autocorrelation
than the one estimated, so the errors are lower estimates.

The JSON is rewritten after every run, so an interrupted run keeps its completed rows.
"""
import os
for v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[v] = "2"
import json, math, sys, time
import numpy as np

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "yang_mills_flow_2026_10_31.json")


def qmul(a, b):
    w = a[..., 0] * b[..., 0] - np.sum(a[..., 1:] * b[..., 1:], axis=-1)
    v = a[..., 0, None] * b[..., 1:] + b[..., 0, None] * a[..., 1:] + np.cross(a[..., 1:], b[..., 1:])
    return np.concatenate([w[..., None], v], axis=-1)


def conj(a):
    out = a.copy()
    out[..., 1:] *= -1
    return out


def twist(N):
    """z_p on plane (1,2): -1 at x1 = x2 = 0."""
    z = np.ones((N, N, N, N))
    z[:, 0, 0, :] = -1.0
    return z


def plane_z(N, mu, nu):
    return twist(N) if (mu, nu) == (1, 2) else np.ones((N, N, N, N))


def staple_mu(U, N, mu):
    """A with Re(U_mu A) summed over the six plaquettes through each mu link, signs included."""
    A = np.zeros_like(U[mu])
    for nu in range(4):
        if nu == mu:
            continue
        a, b = (mu, nu) if mu < nu else (nu, mu)
        z = plane_z(N, a, b)
        Unu_xpmu = np.roll(U[nu], -1, axis=mu)
        Umu_xpnu = np.roll(U[mu], -1, axis=nu)
        fwd = qmul(qmul(Unu_xpmu, conj(Umu_xpnu)), conj(U[nu]))
        Unu_xmnu = np.roll(U[nu], 1, axis=nu)
        Umu_xmnu = np.roll(U[mu], 1, axis=nu)
        Unu_xpmu_mnu = np.roll(Unu_xmnu, -1, axis=mu)
        bwd = qmul(qmul(conj(Unu_xpmu_mnu), conj(Umu_xmnu)), Unu_xmnu)
        zb = np.roll(z, 1, axis=nu)
        A += z[..., None] * fwd + zb[..., None] * bwd
    return A


def plaquette_terms(U, N):
    """term_p = 2 - 2 z_p Re P_p, shape (6, N,N,N,N)."""
    out = []
    for mu in range(4):
        for nu in range(mu + 1, 4):
            P = qmul(qmul(qmul(U[mu], np.roll(U[nu], -1, axis=mu)), conj(np.roll(U[mu], -1, axis=nu))), conj(U[nu]))
            # |z P - 1|^2 = 2 - 2 z Re P on unit quaternions. This form keeps relative accuracy near a flat field.
            zP = plane_z(N, mu, nu)[..., None] * P
            zP[..., 0] -= 1.0
            out.append(np.sum(zP ** 2, axis=-1))
    return np.array(out)


def rotation(U, N):
    """rot = V * star(U), with V the negative tangential gradient of S1 = sum term_p. Imaginary."""
    rots = []
    for mu in range(4):
        w = -2.0 * conj(staple_mu(U, N, mu))
        r = -qmul(w, conj(U[mu]))
        r[..., 0] = 0.0
        rots.append(r)
    return np.stack(rots)


def qexp_imag(v):
    th = np.linalg.norm(v[..., 1:], axis=-1)
    s = np.where(th > 1e-12, np.sin(th) / np.where(th > 1e-12, th, 1.0), 1.0 - th ** 2 / 6)
    out = np.zeros_like(v)
    out[..., 0] = np.cos(th)
    out[..., 1:] = s[..., None] * v[..., 1:]
    return out


def renorm(U):
    return U / np.linalg.norm(U, axis=-1, keepdims=True)


def sweep(U, N, beta, step, rng):
    grid = np.indices((N, N, N, N)).sum(axis=0) % 2
    acc = 0.0
    for mu in range(4):
        for par in (0, 1):
            A = staple_mu(U, N, mu)
            r = rng.normal(size=(N, N, N, N, 4)) * step
            r[..., 0] = 0.0
            new = qmul(qexp_imag(r), U[mu])
            # S = beta sum(2 - 2 Re(U A)) on this link. Re(U A) is the Euclidean inner product of U and conj(A).
            dS = -2.0 * beta * np.sum((new - U[mu]) * conj(A), axis=-1)
            ok = (grid == par) & (np.log(rng.random((N, N, N, N))) < -dS)
            U[mu][ok] = new[ok]
            acc += ok.sum() / (0.5 * N ** 4)
    return acc / 8


def apply_rot(Z, U):
    return renorm(np.stack([qmul(qexp_imag(Z[mu]), U[mu]) for mu in range(4)]))


def rk3_step(U, N, dt):
    """Luescher's third-order integrator for U' = rot(U) U."""
    Z0 = dt * rotation(U, N)
    W1 = apply_rot(0.25 * Z0, U)
    Z1 = dt * rotation(W1, N)
    W2 = apply_rot(8.0 / 9.0 * Z1 - 17.0 / 36.0 * Z0, W1)
    Z2 = dt * rotation(W2, N)
    return apply_rot(0.75 * Z2 - 8.0 / 9.0 * Z1 + 17.0 / 36.0 * Z0, W2)


def flow_series(U0, N, times, dt):
    U = U0.copy()
    t = 0.0
    rows = []
    S0 = plaquette_terms(U, N).sum()
    for target in times:
        while t < target - 1e-12:
            U = rk3_step(U, N, min(dt, target - t))
            t += min(dt, target - t)
        terms = plaquette_terms(U, N)
        rot = rotation(U, N)
        rows.append((t, terms.sum(), np.sum(rot ** 2), terms.max()))
    return rows, S0, U


def cap(s):
    # SU2GaussianMass.cap, with SU2ScalarTilt.partition 0 = pi/2.
    return 4.0 * (math.pi / 2) * s * math.sqrt(s) / math.gamma(1.5)


def phase(t):
    return np.array([math.cos(t), math.sin(t), 0.0, 0.0])


def crit_field(N, m):
    """TwistedFlow.critLink, x = (x0, x1, x2, x3)."""
    u = (2 * m + 1) * math.pi / N ** 2
    y = lambda s: (s - 1) % N
    U = np.zeros((4, N, N, N, N, 4))
    U[..., 0] = 1.0
    for x1 in range(N):
        for x2 in range(N):
            U[1, :, x1, x2, :] = phase(u * y(x2))
            if x2 == 0:
                U[2, :, x1, x2, :] = phase(-(N * u) * y(x1))
    return U


def flat_field(N):
    """TwistedFlat.flatLink."""
    U = np.zeros((4, N, N, N, N, 4))
    U[..., 0] = 1.0
    qI = np.array([0.0, 1.0, 0.0, 0.0])
    qJ = np.array([0.0, 0.0, 1.0, 0.0])
    U[1, :, 0, :, :] = qI
    U[2, :, :, 0, :] = qJ
    return U


def deterministic(rng):
    out = {}
    N = 4
    U = renorm(rng.normal(size=(4, N, N, N, N, 4)))
    rot = rotation(U, N)
    eps = 1e-5
    fd = (plaquette_terms(apply_rot(eps * rot, U), N).sum() - plaquette_terms(apply_rot(-eps * rot, U), N).sum()) / (2 * eps)
    out["energy_identity_fd"] = {"fd_dS": float(fd), "minus_norm2": float(-np.sum(rot ** 2))}
    F = np.sum(rot ** 2)
    S = plaquette_terms(U, N).sum()
    out["random_field"] = {"N": N, "force_over_96S": float(F / (96 * S)),
                           "max_link_norm": float(np.linalg.norm(rot, axis=-1).max()), "ceiling": 12.0}
    out["flat_action"] = {str(N): float(plaquette_terms(flat_field(N), N).sum()) for N in (2, 4, 6, 8)}
    crit = []
    for N in (2, 4, 6, 8):
        for m in (0, 1):
            if 2 * m + 1 > N ** 2:
                continue
            U = crit_field(N, m)
            terms = plaquette_terms(U, N)
            u = (2 * m + 1) * math.pi / N ** 2
            row = {"N": N, "m": m, "S": float(terms.sum()), "S_formula": N ** 4 * (2 - 2 * math.cos(u)),
                   "max_force_component": float(np.abs(rotation(U, N)).max()), "max_defect": float(np.sqrt(terms.max())),
                   "defect_bound": u, "S_bounds": [4 * (2 * m + 1) ** 2, ((2 * m + 1) * math.pi) ** 2]}
            if N <= 6:
                # A generic small perturbation leaves the fixed point: it is not stable, only critical.
                V = renorm(U + 1e-3 * rng.normal(size=U.shape))
                rows, S0, _ = flow_series(V, N, [1.0, 4.0, 16.0, 48.0], 0.04)
                row["perturbed"] = {"S0": float(S0), "S_at_t": {str(round(r[0], 3)): float(r[1]) for r in rows}}
            crit.append(row)
    out["critical_fields"] = crit
    near = []
    for N, epss in ((4, (1e-9, 1e-6, 1e-3)), (6, (1e-10, 1e-6, 1e-3)), (8, (1e-11, 1e-3))):
        thr = (1 / (1408.0 * N ** 5)) ** 2
        for eps in epss:
            U = flat_field(N)
            Z = eps * rng.normal(size=U.shape)
            Z[..., 0] = 0.0
            U = apply_rot(Z, U)
            S = plaquette_terms(U, N).sum()
            F = np.sum(rotation(U, N) ** 2)
            T = N ** 2 / 3.0
            rows, _, _ = flow_series(U, N, [T / 8, T / 4, T / 2, T, 2 * T], 0.04)
            ts = [r[0] for r in rows]
            S_t = [r[1] for r in rows]
            F_t = [r[2] for r in rows]
            rates = [-math.log(S_t[i + 1] / S_t[i]) / (ts[i + 1] - ts[i]) for i in range(len(ts) - 1)]
            near.append({"N": N, "eps": eps, "S": float(S), "threshold": thr, "below_threshold": bool(S <= thr),
                         "N2F_over_3S": float(N ** 2 * F / (3 * S)),
                         "N2F_over_3S_at_times": [float(N ** 2 * f / (3 * x)) for f, x in zip(F_t, S_t)],
                         "rate_bound_3_over_N2": 3.0 / N ** 2,
                         "lowest_mode_rate_16_sin2": 16 * math.sin(math.pi / (2 * N)) ** 2,
                         "times": ts, "S_t": [float(x) for x in S_t], "measured_rates": rates})
    out["near_flat"] = near
    return out


def jack(values):
    v = np.asarray(values)
    n = len(v)
    if n < 2:
        return float("nan")
    loo = (v.sum() - v) / (n - 1)
    return float(math.sqrt((n - 1) / n * np.sum((loo - loo.mean()) ** 2)))


def binning_tau(series):
    """Integrated autocorrelation time in sweeps, from the growth of the binned error, largest stable bin."""
    x = np.asarray(series, dtype=float)
    var0 = x.var(ddof=1)
    if var0 == 0 or len(x) < 16:
        return float("nan")
    best = 0.5
    b = 1
    while len(x) // b >= 8:
        k = len(x) // b
        means = x[: k * b].reshape(k, b).mean(axis=1)
        best = max(best, 0.5 * b * means.var(ddof=1) / var0)
        b *= 2
    return float(best)


def start_field(N, start, rng):
    """flat: the twisted flat field. identity: all links 1, which is not flat here. hot: Haar random."""
    if start == "flat":
        return flat_field(N)
    if start == "hot":
        return renorm(rng.normal(size=(4, N, N, N, N, 4)))
    U = np.zeros((4, N, N, N, N, 4))
    U[..., 0] = 1.0
    return U


def run(N, beta, nsample, gap, ntherm, times, dt, rng):
    t0 = time.time()
    U = flat_field(N)
    step = 0.4 / math.sqrt(beta)
    trace = []
    for _ in range(ntherm):
        a = sweep(U, N, beta, step, rng)
        trace.append(plaquette_terms(U, N).sum() / N ** 4)
    chain = []
    ts = [t for t in times if t <= N ** 2 / 8 + 1e-9]
    data = np.zeros((nsample, len(ts), 3))
    worst_smooth = 0.0
    worst_static = 0.0
    dtcheck = None
    for i in range(nsample):
        for _ in range(gap):
            a = sweep(U, N, beta, step, rng)
            chain.append(plaquette_terms(U, N).sum() / N ** 4)
        rows, S0, _ = flow_series(U, N, ts, dt)
        for j, (t, S, F, tmax) in enumerate(rows):
            data[i, j] = (S, F, tmax)
            worst_static = max(worst_static, F / (96 * S) if S > 0 else 0.0)
            if t > 0 and S0 > S:
                worst_smooth = max(worst_smooth, F / ((1 / t + 96) * (S0 - S)))
        if i == 0:
            fine, _, _ = flow_series(U, N, ts, dt / 2)
            dtcheck = {str(round(ts[j], 4)): {"site_E_dt": rows[j][1] / N ** 4, "site_E_dt_half": fine[j][1] / N ** 4}
                       for j in range(len(ts))}
    V = N ** 4
    n = N // 2
    lc = math.log(cap(24 * beta))
    bound = 4 * lc / beta
    run = {"N": N, "beta": beta, "acceptance_last_sweep": a, "samples": nsample, "sweeps_between_samples": gap,
           "thermalization_sweeps": ntherm, "dt": dt,
           "trace_first_quarter_mean": float(np.mean(trace[: ntherm // 4])),
           "trace_last_half_mean": float(np.mean(trace[ntherm // 2:])),
           "chain_mean_site_E_t0": float(np.mean(chain)), "chain_tau_int_sweeps": binning_tau(chain),
           "chain_len": len(chain),
           "bound_law_plaquette_mean_wf": bound,
           "bound_explicit_35_over_beta": 35.0 / beta,
           "explicit_bound_applies": bool(lc <= n), "log_cap_24beta": lc, "n": n,
           "bound_force_static": 96 * bound,
           "worst_ratio_wf_smoothing": worst_smooth, "worst_ratio_force_static": worst_static,
           "dt_check_one_field": dtcheck, "series": []}
    half = nsample // 2
    for j, t in enumerate(ts):
        E = data[:, j, 0] / V
        F = data[:, j, 1] / V
        run["series"].append({"t": t, "t_over_N2": t / N ** 2, "site_E": float(E.mean()), "site_E_err_jack": jack(E),
                              "site_E_first_half": float(E[:half].mean()), "site_E_second_half": float(E[half:].mean()),
                              "site_F": float(F.mean()), "site_F_err_jack": jack(F),
                              "t2_site_E": float(t * t * E.mean()), "max_term_mean": float(data[:, j, 2].mean()),
                              "total_S": float(data[:, j, 0].mean()),
                              "bound_F_exp": min(math.exp(min(96 * t, 600.0)) * 576 / beta, 576.0)})
    run["seconds"] = time.time() - t0
    return run


def derived(out):
    """Compare the Monte Carlo means with law_force_exact, law_action_ge and law_plaquette_mean_strict."""
    rows = []
    for r in out["runs"]:
        b = r["beta"]
        s0 = r["series"][0]
        e = s0["site_E"]
        row = {"N": r["N"], "beta": b, "site_E": e, "site_E_err": s0["site_E_err_jack"],
               "site_F": s0["site_F"], "site_F_err": s0["site_F_err_jack"], "law_force_exact_value": 12 / b * (12 - e),
               "law_action_ge_value": 144.0 / (96 * b + 12), "strict": []}
        for x in r["series"][1:]:
            row["strict"].append({"t": x["t"], "site_E": x["site_E"],
                                  "bound": e - (1 - math.exp(-96 * x["t"])) / (8 * b) * (12 - e)})
        rows.append(row)
    out["derived_checks"] = rows


def save(out):
    with open(OUT + ".tmp", "w") as f:
        json.dump(out, f, indent=1)
    os.replace(OUT + ".tmp", OUT)


def identity_check(N, beta, nsample, gap, ntherm, rng):
    """Long chain for law_force_exact: compare the mean of F / N^4 with 12/beta (12 - E) on the same samples."""
    U = flat_field(N)
    step = 0.4 / math.sqrt(beta)
    for _ in range(ntherm):
        sweep(U, N, beta, step, rng)
    es, fs = [], []
    for _ in range(nsample):
        for _ in range(gap):
            sweep(U, N, beta, step, rng)
        es.append(plaquette_terms(U, N).sum() / N ** 4)
        fs.append(np.sum(rotation(U, N) ** 2) / N ** 4)
    es, fs = np.array(es), np.array(fs)
    diff = fs - 12 / beta * (12 - es)
    tau = binning_tau(diff)
    return {"N": N, "beta": beta, "samples": nsample, "gap": gap, "site_E": float(es.mean()), "site_F": float(fs.mean()),
            "law_force_exact_value": float(12 / beta * (12 - es.mean())), "mean_difference": float(diff.mean()),
            "difference_err_naive": jack(diff), "tau_samples": tau,
            "difference_err_binned": jack(diff) * math.sqrt(max(2 * tau, 1.0))}


def plateau(N, beta, start, nsample, gap, ntherm, times, rng):
    """Total action of single flowed fields, by start of the chain. A cold start at all links 1 carries the twist as a
    vortex, whose flow spreads it to the constant-flux fixed point. Local Metropolis at large beta need not leave that
    sector in the sweeps run here, so a stall at the fixed-point action can be memory of the start, not the law."""
    U = start_field(N, start, rng)
    step = 0.4 / math.sqrt(beta)
    for _ in range(ntherm):
        sweep(U, N, beta, step, rng)
    rows = []
    for _ in range(nsample):
        for _ in range(gap):
            sweep(U, N, beta, step, rng)
        r, _, _ = flow_series(U, N, times, 0.04)
        rows.append([float(x[1]) for x in r])
    return {"N": N, "beta": beta, "start": start, "times": times, "fixed_point_action_m0": N ** 4 * (2 - 2 * math.cos(math.pi / N ** 2)),
            "total_S_per_field": rows}


def main():
    rng = np.random.default_rng(20261031)
    if "--extras" in sys.argv:
        with open(OUT) as f:
            out = json.load(f)
        out["identity_check"] = [identity_check(4, 8.0, 1500, 5, 300, rng), identity_check(4, 32.0, 1500, 5, 300, rng),
                                 identity_check(6, 32.0, 400, 5, 300, rng)]
        save(out)
        print(out["identity_check"], flush=True)
        out["plateau"] = []
        for beta in (32.0, 128.0):
            for start in ("flat", "identity", "hot"):
                out["plateau"].append(plateau(8, beta, start, 6, 30, 300, [0.5, 1.0, 2.0, 4.0, 8.0], rng))
                save(out)
        return
    if "--deterministic-only" in sys.argv:
        with open(OUT) as f:
            out = json.load(f)
        out["deterministic"] = deterministic(rng)
        derived(out)
        save(out)
        return
    times = [0.0, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
    out = {"note": "numerics, not proof. Repo normalization S = beta sum_p (2 - 2 z Re P). site means sum over 6 planes.",
           "complete": False, "runs": []}
    out["deterministic"] = deterministic(rng)
    save(out)
    print("deterministic done", flush=True)
    for N, beta, nsample, ntherm in [(4, 8.0, 40, 400), (6, 8.0, 16, 400), (4, 32.0, 40, 400), (6, 32.0, 16, 400),
                                     (8, 8.0, 8, 300), (8, 32.0, 8, 300)]:
        r = run(N, beta, nsample, 20, ntherm, times, 0.04, rng)
        out["runs"].append(r)
        save(out)
        print(N, beta, "acc", round(r["acceptance_last_sweep"], 2), "tau", r["chain_tau_int_sweeps"],
              "E", [(round(x["site_E"], 4), round(x["site_E_err_jack"], 4)) for x in r["series"]],
              "time", round(r["seconds"], 1), flush=True)
    out["complete"] = True
    derived(out)
    save(out)


if __name__ == "__main__":
    main()
