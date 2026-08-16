"""THE ACTION-SELECTION SCAN (registered; the endgame conjecture).

CONJECTURE: everywhere-feasibility of bi-normalized (double-
conservation) growth selects the Benincasa-Dowker action among
gap-weight systems.  The BD 2D weights (2,-4,2) and 4D coefficients
both exhibit deep feasibility (0 infeasible parents to depth 79) -
is that GENERIC in weight space, or a razor-thin locus?

Scan: 2-window integer weight systems W = (w0,w1,w2) (gap =
1 - sum W(min(k,2))), phase grid phi in (0,pi), maxent law; for
each (W,phi): quick 3-step prefilter, then 4 paths to depth 12;
record survival fraction + mean law support (nondegeneracy).

READINGS:
 (i) SELECTION: full-survival + nondegenerate locus is low-
     dimensional, containing/centered on BD (2,-4,2) at phi=pi/4:
     the gravitational action is selected by quantum consistency.
 (ii) BROAD: most systems survive => feasibility does not select
     the action (honest negative; BD remains an input).
 (iii) STRUCTURED: survival common, but parity/quadrature
     structure (even weights => odd gaps => superselection)
     and/or nondegeneracy single out BD-like systems.
"""
import math, os, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
NS = 12; NPATH = 4
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NS + 1)}
rng = np.random.default_rng(31)

def make_law(PHI):
    cache = {}
    def law(gc):
        key = tuple(sorted(gc.items()))
        if key in cache: return cache[key]
        gaps = sorted(gc); mu = np.array([gc[g] for g in gaps], float)
        A = np.vstack([mu * np.cos(np.array(gaps) * PHI),
                       mu * np.sin(np.array(gaps) * PHI)])
        b = np.array([1.0, 0.0]); K = len(gaps)
        r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
        if not r.success: cache[key] = None; return None
        res = minimize(lambda x: float(np.dot(mu, x * x)), r.x, jac=lambda x: 2 * mu * x,
                       constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                       bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 150, "ftol": 1e-11})
        xm = res.x if res.success else r.x
        if float(np.dot(mu, xm * xm)) > 1 + 1e-7: cache[key] = None; return None
        xhi = None
        for t in range(6):
            c = -np.ones(K) if t == 0 else rng.normal(size=K)
            v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
            if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9: xhi = v.x; break
        if xhi is None:
            rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2), bounds=[(0, 1)] * K, method="highs")
            if rc.success and (-rc.fun) > 1e-9:
                d = rc.x / np.linalg.norm(rc.x); t = 1.0
                while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
                xhi = xm + t * d
            else: cache[key] = None; return None
        f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
        lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if f(mid) <= 0: lo = mid
            else: hi = mid
        xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
        def negH(x):
            q = mu * x * x
            return float(np.sum(q * np.log(q + 1e-300)))
        cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
                {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0, "jac": lambda x: 2 * mu * x}]
        best = (negH(xfe), xfe)
        r2 = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K, method="SLSQP",
                      options={"maxiter": 150, "ftol": 1e-10})
        if r2.success:
            x2 = np.maximum(r2.x, 0.0)
            if abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]:
                best = (negH(x2), x2)
        out = {g: best[1][i] ** 2 for i, g in enumerate(gaps)}
        cache[key] = out; return out
    return law

def run_system(W, PHI, npath, ns):
    law = make_law(PHI)
    warr = np.zeros(ns + 2, dtype=np.int64)
    for k in range(3): warr[k] = W[k]
    surv = 0; supp_acc = []
    for trial in range(npath):
        below = [0]; above = [0]; ok = True
        for n in range(1, ns):
            masks = ARANGE[n]; okm = np.ones(masks.shape[0], dtype=bool)
            for x in range(n):
                bx = below[x]
                if bx == 0: continue
                okm &= ~(((masks >> x) & 1 == 1) & ((masks & bx) != bx))
            dlist = masks[okm]
            g = np.ones(dlist.shape[0], dtype=np.int64)
            for d in range(n):
                sel = ((dlist >> d) & 1) == 1
                if not sel.any(): continue
                k = popcount(dlist[sel] & np.int64(above[d])).astype(np.int64)
                g[sel] -= warr[np.minimum(k, 2)]
            gc = {}
            for gg in g.tolist(): gc[gg] = gc.get(gg, 0) + 1
            lw = law(gc)
            if lw is None: ok = False; break
            probs = np.array([lw[gg] for gg in g.tolist()])
            probs = np.maximum(probs, 0); s = probs.sum()
            if s <= 0: ok = False; break
            probs = probs / s
            supp_acc.append(float((probs > 1e-9).sum()) / len(probs))
            j = rng.choice(dlist.shape[0], p=probs)
            D = int(dlist[j]); below.append(D); above.append(0)
            m = D
            while m:
                d = (m & -m).bit_length() - 1
                above[d] |= 1 << n; m &= m - 1
        if ok: surv += 1
    return surv / npath, (np.mean(supp_acc) if supp_acc else 0.0)

PHIS = [math.pi * k / 16 for k in range(1, 16)]
results = []
count = 0
for w0 in range(1, 5):
    for w1 in range(-6, 1):
        for w2 in range(0, 5):
            W = (w0, w1, w2)
            best = (0.0, 0.0, None)
            for PHI in PHIS:
                s3, _ = run_system(W, PHI, 2, 5)      # prefilter: depth 5
                if s3 == 0: continue
                s, supp = run_system(W, PHI, NPATH, NS)
                if (s, supp) > (best[0], best[1]): best = (s, supp, PHI)
            results.append((W, best))
            count += 1
            if count % 20 == 0: log(f"  {count}/140 systems scanned")
log("== survival map (best phi per system) ==")
full = [(W, b) for W, b in results if b[0] == 1.0 and b[1] > 0.3]
part = [(W, b) for W, b in results if 0 < b[0] < 1.0 or (b[0] == 1.0 and b[1] <= 0.3)]
dead = [(W, b) for W, b in results if b[0] == 0.0]
log(f"FULL survival + nondegenerate (surv=1, support>0.3): {len(full)}/140")
for W, (s, supp, phi) in sorted(full, key=lambda t: -t[1][1]):
    log(f"  W={W}  phi={phi/math.pi:.3f}pi  support={supp:.3f}"
        + ("   <== BD 2D" if W == (2, -4, 2) else ""))
log(f"partial/degenerate: {len(part)}, dead: {len(dead)}")
log("DONE-AS")
