#!/usr/bin/env python3
"""The smeared-2D wave gate: does physically-smeared 2D growth retain a
covariant quantum family beyond truncation-2?

Dowker-Glaser (1305.2588 eq 26) smeared 2D action: C^(2) = (1,-2,1),
prefactor beta_2/|alpha_2| = 2, so W_eps(k) = 2*eps*f_2(k,eps),
f_2(n,eps) = (1-eps)^n sum_i C_i binom(n,i-1)(eps/(1-eps))^(i-1).
Physical band eps = (l/xi)^2, l/xi in [0.4,0.5] => eps in [0.16,0.25].

Truncation-2 (necessary condition, dim_general_trunc2.py): 2D band
ALIVE at eps=0.16,0.20 (wide j=1 fracs), DEAD at eps=0.25.  This gate
runs the full wave hierarchy — tree through n=7, equations through
n=6, exact LP with proven-death removal — at those points:

  branch DEAD:   every dimension dies under physical smearing at low
                 winding; the sharp-2D quantum family is a limit
                 artifact (larger result than the boundary surface).
  branch ALIVE:  the first positive claim in the arc to survive
                 contact — a physically-smeared covariant quantum
                 family in 2D.

Control: eps=0.25 (truncation-2 dead) must return EMPTY, or the gate
and the truncation disagree and we halt and reconcile.

Root window (corrected slivers): channels have gaps 1-W(0) and 1;
straddle iff 0 < delta < W0*phi at phi = 2pi*j + delta, so
delta = frac*W0*2pi*j/(1 - frac*W0).
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

C2 = [1.0, -2.0, 1.0]
def W_eps(k, eps):
    tot = 0.0
    for i in range(1, 4):
        tot += C2[i-1] * math.comb(k, i-1) * (eps/(1-eps))**(i-1)
    return 2.0 * eps * (1-eps)**k * tot

def action_eps(rel, n, eps):
    relset = set(rel)
    tot = float(n)
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W_eps(k, eps)
    return tot

def canon_fast(n, rel):
    if not rel:
        return (n, ())
    up = [[] for _ in range(n)]; dn = [[] for _ in range(n)]
    for a, b in rel:
        up[a].append(b); dn[b].append(a)
    col = [(len(up[v]), len(dn[v])) for v in range(n)]
    vals = sorted(set(col)); m = {c: i for i, c in enumerate(vals)}
    col = [m[c] for c in col]
    for _ in range(n):
        nc = [(col[v], tuple(sorted(col[w] for w in up[v])),
               tuple(sorted(col[w] for w in dn[v]))) for v in range(n)]
        vals = sorted(set(nc)); m = {c: i for i, c in enumerate(vals)}
        nc = [m[c] for c in nc]
        if nc == col: break
        col = nc
    classes = {}
    for v in range(n): classes.setdefault(col[v], []).append(v)
    parts = [classes[c] for c in sorted(classes)]
    best = None
    for perm_parts in itertools.product(
            *[itertools.permutations(cls) for cls in parts]):
        pos = {}
        i = 0
        for part in perm_parts:
            for v in part:
                pos[v] = i; i += 1
        r = tuple(sorted((pos[a], pos[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

NMAX = 7
levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
counts = {n: len(v) for n, v in levels.items()}
print("causets per level:", counts, flush=True)
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045], \
    "canonical form validation FAILED"
print("canon_fast validated against A000112", flush=True)

root = canon_fast(1, ())
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
def nelem(key): return key[0]

def build(eps):
    children = {}
    for n in range(1, NMAX):
        for key, (m, rel) in sorted(levels[n].items()):
            S0 = action_eps(rel, m, eps)
            below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
            kid = {}
            for mask in range(1 << m):
                D = [i for i in range(m) if mask >> i & 1]
                if not all(below[x] <= set(D) for x in D): continue
                nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                ck = canon_fast(m + 1, nr)
                g = action_eps(nr, m + 1, eps) - S0
                if ck in kid:
                    mu, gg = kid[ck]
                    assert abs(gg - g) < 1e-9
                    kid[ck] = (mu + 1, gg)
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
    for rnd in range(60):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        A_eq, b_eq = [], []
        r0 = np.zeros(nvu); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= NMAX: continue
            rr = np.zeros(nvu); ri = np.zeros(nvu)
            rr[ii[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * phi)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        cobj = np.zeros(nvu)
        for key in U:
            if nelem(key) >= 5: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success: return set(), 0, rnd
        A = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if A[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead:
            br = sum(1 for key in U if key in children
                     and sum(1 for ck in children[key] if ck in U) >= 2)
            return U, br, rnd
        U = U - descendants(children, dead)
        if root not in U: return set(), 0, rnd
    return U, -1, 60

# (eps, j, frac, truncation-2 verdict from dim_general_trunc2.py)
POINTS = [
    (0.16, 1, 0.25, "t2-ALIVE"),
    (0.16, 1, 0.50, "t2-ALIVE"),
    (0.16, 1, 0.75, "t2-ALIVE"),
    (0.20, 1, 0.50, "t2-ALIVE"),
    (0.25, 1, 0.50, "t2-DEAD (control: must be EMPTY)"),
]

for eps, j, frac, verdict in POINTS:
    ch = build(eps)
    W0 = W_eps(0, eps)
    delta = frac * W0 * 2 * np.pi * j / (1 - frac * W0)
    phi = 2 * np.pi * j + delta
    U, br, rnds = gate(ch, phi)
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    desc = "  ".join(f"n={n}:{per.get(n, 0)}/{counts[n]}"
                     for n in range(1, NMAX + 1)) if U else "EMPTY"
    print(f"eps={eps} j={j} frac={frac} phi={phi:.4f} [{verdict}]:\n"
          f"  support {len(U)} rounds {rnds} branching {br}\n"
          f"  [{desc}]", flush=True)
print("DONE", flush=True)
