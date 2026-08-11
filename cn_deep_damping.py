#!/usr/bin/env python3
"""THE DECISIVE c_N COMPUTATION (registered in EVERPRESENT_LAMBDA_DERIVED).

The parameter-free everpresent amplitude makes the Poisson-floor
coefficient c_N a kill-or-clear quantity: the CMB demands
c_N(eps*) <= 3.7e-4 at the cosmological smearing eps* ~ 2e-81.  The
July MC (diamond geometry, noise floor ~0.3) could not resolve it.
This computation targets the BULK floor directly:

  - geometry: flat spacetime box [0,T] x torus [0,L]^3 (NO spatial
    boundary; minimum-image causality) at unit density;
  - bulk window: contributions S_x = 1 - D_x summed over x with
    t_x >= t_min = 3 tau_eps(min eps), so every window point's
    smearing past (e^{-eps V} support, eps V <= 81) is fully inside
    the box;
  - same kernel and conventions as action_variance_mc.py:
    f(n,e) = (1-e)^n - 9en(1-e)^{n-1} + 8e^2 n(n-1)(1-e)^{n-2}
             - (4/3)e^3 n(n-1)(n-2)(1-e)^{n-3},   D = sum eps f,
    S/kappa = N - D; interval counts n = C @ C computed ONCE per
    realization and reused for all eps;
  - the boost/cone-depth term ((pi/4) M(eps) g t^2) is separated by
    computing the windowed variance in four TIME BANDS and taking the
    intercept of Var/N against the band's mean t^2;
  - output: c_N(eps) for eps in {0.5, 0.3, 0.2, 0.1, 0.05, 0.02},
    its power-law fit c_N ~ A eps^alpha, the explicit
    VarN/VarD/Cov(N,D) cancellation table, and the extrapolated
    c_N(eps* = 2e-81) verdict against 3.7e-4.

Registered readings:
  (i)  c_N(eps) decreases with eps (power law): the floor VANISHES in
       deep damping; at eps* it is astronomically below the CMB bound
       -> the theory CLEARS its own falsifier (extrapolation across
       ~79 orders flagged as the honest caveat, backed by the
       measured law + the O(eps) per-pair structure).
  (ii) c_N(eps) plateaus at a constant > 4e-4 -> the theory is DEAD
       against the CMB with no remaining freedom.
  (iii) noise floor prevents a verdict below eps ~ 0.02: report the
       smallest resolved c_N and the trend; partial.
"""
import math, sys, time
import numpy as np

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

rng = np.random.default_rng(20260811)
KAPPA = 4 / math.sqrt(6)
EPSS = [0.5, 0.4, 0.3, 0.2, 0.1, 0.05]
L = 9.0
TMIN = 3 * (24 / (math.pi * min(EPSS))) ** 0.25
NBANDS = 4
TBOX = TMIN + NBANDS * 1.0 + 0.2
NREAL = int(sys.argv[1]) if len(sys.argv) > 1 else 220
log(f"box: T = {TBOX:.2f}, L = {L}, <N> = {TBOX * L**3:.0f}, "
    f"window t >= {TMIN:.2f}, bands = {NBANDS}, realizations = {NREAL}")

def f_smear(n, e):
    le = math.log1p(-e)
    out = np.exp(n * le)
    t1 = n * np.exp(np.maximum(n - 1, 0) * le) * (n >= 1)
    t2 = n * np.maximum(n - 1, 0) * np.exp(np.maximum(n - 2, 0) * le) * (n >= 2)
    t3 = n * np.maximum(n - 1, 0) * np.maximum(n - 2, 0) * \
        np.exp(np.maximum(n - 3, 0) * le) * (n >= 3)
    return out - 9 * e * t1 + 8 * e * e * t2 - (4 / 3) * e ** 3 * t3

def one_realization():
    N = rng.poisson(TBOX * L ** 3)
    t = TBOX * rng.random(N)
    x = L * rng.random((N, 3))
    order = np.argsort(t)
    t = t[order]; x = x[order]
    dt = t[None, :] - t[:, None]                    # dt[a,b] = t_b - t_a
    d = np.abs(x[None, :, :] - x[:, None, :])
    d = np.minimum(d, L - d)                        # torus min-image
    d2 = (d ** 2).sum(-1)
    C = ((dt > 0) & (dt * dt > d2)).astype(np.float32)
    n = C @ C
    inwin = t >= TMIN
    band = np.minimum(((t - TMIN)).astype(int), NBANDS - 1)
    res = {}
    for e in EPSS:
        F = f_smear(n, e) * C                        # zero where unrelated
        D_x = e * F.sum(axis=0)                      # sum over y below x
        s_x = 1.0 - D_x
        bs = []
        for b in range(NBANDS):
            sel = inwin & (band == b)
            bs.append((sel.sum(), s_x[sel].sum(), D_x[sel].sum()))
        res[e] = bs
    tm = [(0.5 * (TMIN + b + TMIN + b + 1)) for b in range(NBANDS)]
    return res, tm

acc = {e: [[] for _ in range(NBANDS)] for e in EPSS}
accN = {e: [[] for _ in range(NBANDS)] for e in EPSS}
accD = {e: [[] for _ in range(NBANDS)] for e in EPSS}
tmid = None
t_last = time.time()
for i in range(NREAL):
    res, tmid = one_realization()
    for e in EPSS:
        for b in range(NBANDS):
            Nb, Sb, Db = res[e][b]
            acc[e][b].append(Sb)
            accN[e][b].append(Nb)
            accD[e][b].append(Db)
    if time.time() - t_last > 60:
        log(f"  {i + 1}/{NREAL} realizations")
        t_last = time.time()
log("sampling done")

log("== per-eps, per-band variance table ==")
cn = {}
for e in EPSS:
    xs, ys = [], []
    for b in range(NBANDS):
        S = np.array(acc[e][b]); Nn = np.array(accN[e][b])
        Dd = np.array(accD[e][b])
        vS = np.var(S, ddof=1); mN = Nn.mean()
        vN = np.var(Nn, ddof=1); vD = np.var(Dd, ddof=1)
        cND = np.cov(Nn, Dd, ddof=1)[0, 1]
        v = vS / mN
        xs.append(tmid[b] ** 2); ys.append(v)
        log(f"  eps={e:5}: band t~{tmid[b]:5.2f}  Var(S/k)/N = {v:8.5f}   "
            f"[VarN/N {vN/mN:6.3f}  VarD/N {vD/mN:8.3f}  "
            f"2Cov/N {2*cND/mN:8.3f}]  <S/k>/N = {S.mean()/mN:+.4f}")
    A = np.vstack([xs, np.ones(len(xs))]).T
    (slope, icept), *_ = np.linalg.lstsq(A, np.array(ys), rcond=None)
    cn[e] = icept
    log(f"  eps={e:5}: intercept c_N = {icept:.5f}   t^2-slope = {slope:.6f}")

log("== c_N(eps) scaling law ==")
es = np.array(EPSS)
cs = np.array([cn[e] for e in EPSS])
pos = cs > 0
if pos.sum() >= 3:
    Afit = np.vstack([np.log(es[pos]), np.ones(pos.sum())]).T
    (alpha, lnA), *_ = np.linalg.lstsq(Afit, np.log(cs[pos]), rcond=None)
    A0 = math.exp(lnA)
    log(f"  fit c_N = {A0:.4f} * eps^{alpha:.3f}  "
        f"(over {pos.sum()} positive intercepts)")
    eps_star = 1.987e-81
    cn_star = A0 * eps_star ** alpha
    log(f"  extrapolated c_N(eps* = 2e-81) = {cn_star:.3e}")
    log(f"  CMB bound 3.7e-4: "
        + ("CLEARS by many orders (reading i)" if cn_star < 3.7e-4
           else "FAILS (reading ii)"))
else:
    log("  intercepts not positive-definite enough for a law: reading (iii)")
log("DONE")
