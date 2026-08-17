"""Ellipsoid-multistart maxent law (2026-08-16).  Replaces the
LP-vertex multi-start in make_law: parametrize the feasible set
{A y = b, y^T M y = 1, y >= 0} exactly via the null space of A
(an ellipsoid section of dim K-2), sample it densely with a
per-key deterministic generator, polish each start with SLSQP,
return the best-entropy member.  NSTART controls density."""
import numpy as np, math, zlib, pickle, os
from scipy.optimize import minimize, linprog

def make_law_ell(PHI, NSTART=16, disk_cache=None):
    """disk_cache: optional path; solved members are loaded at start
    and appended on the fly (results are per-key deterministic, so
    sharing across processes/scripts is exact)."""
    C = [math.cos(k * PHI) for k in range(256)]
    S = [math.sin(k * PHI) for k in range(256)]
    cache = {}
    if disk_cache and os.path.exists(disk_cache):
        with open(disk_cache, "rb") as fh:
            stored = pickle.load(fh)
            if stored.get("meta") == (round(PHI, 12), NSTART):
                cache.update(stored["cache"])
    def _persist():
        if not disk_cache: return
        tmp = disk_cache + ".tmp"
        with open(tmp, "wb") as fh:
            pickle.dump({"meta": (round(PHI, 12), NSTART), "cache": cache}, fh)
        os.replace(tmp, disk_cache)
    def law(gc):
        key = tuple(sorted(gc.items()))
        if key in cache: return cache[key]
        gaps = sorted(gc); mu = np.array([gc[g] for g in gaps], float)
        K = len(gaps)
        A = np.vstack([mu * np.array([C[g % 256] for g in gaps]),
                       mu * np.array([S[g % 256] for g in gaps])])
        b = np.array([1.0, 0.0])
        M = mu  # diagonal metric
        # feasibility of the linear system on the orthant
        r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
        if not r.success: cache[key] = None; return None
        # min-norm check (Born reachability)
        res = minimize(lambda x: float(np.dot(M, x * x)), r.x, jac=lambda x: 2 * M * x,
                       constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                       bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 500, "ftol": 1e-13})
        xm = res.x if res.success else r.x
        if float(np.dot(M, xm * xm)) > 1 + 1e-7: cache[key] = None; return None
        def negH(x):
            qq = M * x * x
            return float(np.sum(qq * np.log(qq + 1e-300)))
        cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
                {"type": "eq", "fun": lambda x: float(np.dot(M, x * x)) - 1.0, "jac": lambda x: 2 * M * x}]
        def feasible(x):
            return (abs(float(np.dot(M, x * x)) - 1) < 1e-6
                    and np.max(np.abs(A @ x - b)) < 1e-6)
        def polish_and_score(x0, best):
            x0 = np.maximum(x0, 0.0)
            # score the raw start too: at pinned/degenerate solutions SLSQP
            # reports failure even though the point is exactly feasible
            if feasible(x0) and (best is None or negH(x0) < best[0]):
                best = (negH(x0), x0)
            r2 = minimize(negH, x0, constraints=cons, bounds=[(0, None)] * K,
                          method="SLSQP", options={"maxiter": 500, "ftol": 1e-13})
            if r2.success:
                x2 = np.maximum(r2.x, 0.0)
                if feasible(x2) and (best is None or negH(x2) < best[0]):
                    best = (negH(x2), x2)
            return best
        rk = np.random.default_rng(zlib.crc32(repr(key).encode()) ^ 0x5A17)
        best = None
        if K <= 2:
            # 0-dim section: solve directly from xm pushed to the sphere
            # (and LP vertices as backup starts)
            best = polish_and_score(xm, best)
            for t in range(6):
                c = -np.ones(K) if t == 0 else rk.normal(size=K)
                v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
                if v.success: best = polish_and_score(v.x, best)
        else:
            # null-space parametrization: y = y0 + Z t
            y0, *_ = np.linalg.lstsq(A, b, rcond=None)
            _, s_, Vt = np.linalg.svd(A)
            Z = Vt[2:].T                       # K x (K-2)
            Q = Z.T @ (M[:, None] * Z)         # (K-2)^2
            g0 = Z.T @ (M * y0)
            try:
                tc = -np.linalg.solve(Q, g0)
            except np.linalg.LinAlgError:
                tc = np.zeros(K - 2)
            rho = 1.0 - float(y0 @ (M * y0)) + float(tc @ Q @ tc)
            if rho <= 0:
                # sphere barely reachable: fall back to min-norm polish
                best = polish_and_score(xm, best)
            else:
                L = np.linalg.cholesky(Q + 1e-12 * np.eye(K - 2))
                Li = np.linalg.inv(L).T
                d = K - 2
                for si in range(NSTART):
                    u = rk.normal(size=d); u /= np.linalg.norm(u)
                    t = tc + math.sqrt(rho) * (Li @ u)
                    best = polish_and_score(y0 + Z @ t, best)
                best = polish_and_score(xm, best)
            # orthant-safe backup starts: LP vertex + bisection to the
            # sphere along xm->xhi (both >= 0, so the segment is too)
            for t in range(4):
                c = -np.ones(K) if t == 0 else rk.normal(size=K)
                v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
                if not (v.success and float(np.dot(M, v.x * v.x)) >= 1 - 1e-9): continue
                xhi = v.x
                fb = lambda tt: float(np.dot(M, ((1 - tt) * xm + tt * xhi) ** 2)) - 1.0
                lo, hi = 0.0, 1.0
                for _ in range(80):
                    mid = 0.5 * (lo + hi)
                    if fb(mid) <= 0: lo = mid
                    else: hi = mid
                best = polish_and_score(np.maximum((1 - lo) * xm + lo * xhi, 0.0), best)
        if best is None:
            cache[key] = None
            if len(cache) % 500 == 0: _persist()
            return None
        x = best[1]; out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
        cache[key] = out
        if len(cache) % 500 == 0: _persist()
        return out
    law.cache = cache
    law.persist = _persist
    return law
