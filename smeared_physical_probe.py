#!/usr/bin/env python3
"""The physical-regime probe (reviewer-mandated, decides the smeared claim).

1. PHYSICAL BAND: eps = (l/xi)^4 for l/xi in [0.4, 0.5] => eps in
   [0.0256, 0.0625].  Natural choices are resonance-adjacent
   (0.0625 = 1/16 exactly; 0.0256 within 4e-5 of 1/39).  Probe
   carefully chosen eps with computed min|gap| and nearest-1/m
   distance, at phases inside the k-th windows (k*pi, k*pi/(1-eps)),
   k = 1, 2, 3, plus controls outside.
2. ISLAND WIDTH: where life exists, walk eps toward the nearest
   resonance at fixed alive phi; record the death point vs the
   resonance location.
3. IRRATIONAL DISCRIMINATOR: eps = 0.45 died (min|gap| = 0.012, near a
   root).  Probe irrational neighbors at the same phi: alive =>
   proximity-kill (resonance geography); dead => deeper-equation kill.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

C4 = [1.0, -9.0, 16.0, -8.0]
def W_eps(k, eps):
    tot = 0.0
    for i in range(1, 5):
        tot += C4[i-1] * math.comb(k, i-1) * (eps/(1-eps))**(i-1)
    return eps * (1-eps)**k * tot

def action_eps(rel, n, eps):
    relset = set(rel)
    tot = float(n)
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W_eps(k, eps)
    return tot

def canon(n, rel):
    best = None
    for p in itertools.permutations(range(n)):
        r = tuple(sorted((p[a], p[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

def downsets(n, rel):
    below = {x: {a for (a, b) in rel if b == x} for x in range(n)}
    out = []
    for mask in range(1 << n):
        D = frozenset(i for i in range(n) if mask >> i & 1)
        if all(below[x] <= D for x in D): out.append(D)
    return out

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
root = canon(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 7) for key in sorted(levels[n])]

def build(eps):
    children = {}
    for n in range(1, 6):
        for key, (m, rel) in sorted(levels[n].items()):
            S0 = action_eps(rel, m, eps)
            kid = {}
            for D in downsets(m, rel):
                nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                ck = canon(m + 1, nr)
                g = action_eps(nr, m + 1, eps) - S0
                if ck in kid:
                    mu, gg = kid[ck]; kid[ck] = (mu + 1, gg)
                else: kid[ck] = (1, g)
            children[key] = kid
    return children

def descendants(children, seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out

def gate(children, phi):
    U = set(allkeys)
    for _ in range(40):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        A_eq, b_eq = [], []
        r0 = np.zeros(nvu); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= 6: continue
            rr = np.zeros(nvu); ri = np.zeros(nvu)
            rr[ii[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * phi)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        res = linprog(np.zeros(nvu), A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * nvu, method="highs")
        if not res.success: return 0
        A = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if A[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead: return len(U)
        U = U - descendants(children, dead)
        if root not in U: return 0
    return len(U)

def diagnostics(eps):
    ch = build(eps)
    gaps = [g for kid in ch.values() for (mu, g) in kid.values()]
    mn = min(abs(g) for g in gaps)
    m_near = round(1 / eps)
    d_res = min(abs(eps - 1/m) for m in range(max(2, m_near - 2),
                                             m_near + 3))
    return ch, mn, d_res

print("=" * 72)
print("1. PHYSICAL BAND (eps in [0.0256, 0.0625]):", flush=True)
phys = [0.0300, 0.0450, 0.0550, 0.0625]      # 0.0625 = 1/16 resonance
for eps in phys:
    ch, mn, dres = diagnostics(eps)
    print(f"eps = {eps:.4f}: min|gap| = {mn:.5f}, dist to nearest 1/m = "
          f"{dres:.5f}", flush=True)
    results = []
    for k in (1, 2, 3):
        lo, hi = k * np.pi, k * np.pi / (1 - eps)
        for t in (0.25, 0.5, 0.8):
            phi = lo + t * (hi - lo)
            s = gate(ch, phi)
            results.append((k, phi, s))
    ctrl = gate(ch, 2.0)
    inwin = [(k, f"{phi:.4f}", s) for k, phi, s in results]
    print(f"   windows: {inwin}  control(phi=2.0): {ctrl}", flush=True)

print("=" * 72)
print("3. IRRATIONAL DISCRIMINATOR at eps ~ 0.45, phi = 4.427:", flush=True)
for eps in (0.45, 0.45 + (math.sqrt(2) - 1) / 100, 0.45 - (math.sqrt(2) - 1) / 100,
            1 / math.e):
    ch, mn, dres = diagnostics(eps)
    s = gate(ch, 4.427)
    print(f"eps = {eps:.6f}: min|gap| = {mn:.5f}, support = {s}", flush=True)
