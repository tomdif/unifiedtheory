#!/usr/bin/env python3
"""Monte Carlo: variance of the smeared 4D Benincasa-Dowker action on a
sprinkled causal diamond (unit density, Planck units).

S = kappa * (N - D_eps),  kappa = 4/sqrt6,
D_eps = sum_{y<x} eps * f(n_xy, eps),
f(n,eps) = (1-e)^n -9 e n (1-e)^{n-1} + 8 e^2 n(n-1)(1-e)^{n-2}
           - (4/3) e^3 n(n-1)(n-2)(1-e)^{n-3}      [ASS 4D smeared weights]
(eps=1 recovers sharp layer weights (1,-9,16,-8)).

Diamond between (-T,0) and (T,0); V = (2pi/3) T^4 = E[N].
Decides: is Var[S] ~ N (Poissonian) or ~ N * T^2 (boost-edge super-Poissonian)?
"""
import numpy as np, json, sys, time

rng = np.random.default_rng(20260729)
KAPPA = 4/np.sqrt(6)

def sample_diamond(V):
    T = (3*V/(2*np.pi))**0.25
    N = rng.poisson(V)
    s = T*rng.random(N)**0.25                 # pdf ~ s^3
    t = np.where(rng.random(N) < 0.5, T-s, s-T)
    r = s*rng.random(N)**(1/3)
    v = rng.normal(size=(N,3)); v /= np.linalg.norm(v, axis=1)[:,None]
    return t, r[:,None]*v, T

def f_smear(n, e):
    if e == 1.0:
        return np.where(n==0,1.0,0.0) - 9*np.where(n==1,1.0,0.0) \
             + 16*np.where(n==2,1.0,0.0) - 8*np.where(n==3,1.0,0.0)
    le = np.log1p(-e)
    def pw(k):  # n^(k) falling * (1-e)^(n-k), 0 where n<k
        nn = np.maximum(n-k, 0)
        ff = np.ones_like(n, dtype=np.float64)
        for j in range(k): ff = ff*np.maximum(n-j, 0)
        return ff*np.exp(nn*le)*(n >= k)
    return pw(0) - 9*e*pw(1) + 8*e*e*pw(2) - (4/3)*e**3*pw(3)

def one_run(V, epss):
    t, x, T = sample_diamond(V)
    N = len(t)
    dt = t[None,:]-t[:,None]                 # dt[a,b] = t_b - t_a
    d2 = ((x[None,:,:]-x[:,None,:])**2).sum(-1)
    C = ((dt > 0) & (dt*dt > d2)).astype(np.float32)   # C[a,b]=1 iff a < b
    n = (C @ C)                              # n[a,b] = #{z: a<z<b}
    mask = C.astype(bool)
    nvals = n[mask]
    out = {"N": N, "T": T}
    for e in epss:
        D = e*f_smear(nvals, e).sum()
        out[f"S_{e}"] = KAPPA*(N - D)
        out[f"D_{e}"] = D
    return out

if __name__ == "__main__":
    epss = [1.0, 0.5, 0.2, 0.1, 0.05]
    plan = [(1000, 48), (2000, 32), (4000, 16), (8000, 8)]
    res = []
    for V, R in plan:
        t0 = time.time()
        for r in range(R):
            res.append({"V": V, **one_run(float(V), epss)})
        print(f"V={V}: {R} runs in {time.time()-t0:.0f}s", flush=True)
    with open("action_variance_mc.json","w") as fh: json.dump(res, fh)
    # summary
    for V,_ in plan:
        sub = [r for r in res if r["V"]==V]
        Nbar = np.mean([r["N"] for r in sub]); T = sub[0]["T"]
        line = f"V={V:5d} T={T:5.2f}: "
        for e in epss:
            S = np.array([r[f"S_{e}"] for r in sub])
            line += f" var{e}={S.var(ddof=1):9.3g}"
        line += f"  varN*k2={KAPPA**2*Nbar:9.3g}"
        print(line, flush=True)
