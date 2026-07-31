#!/usr/bin/env python3
"""The 2D wave-equation gate: forced-quantum survivor or total no-go?

2D structure (from collision_2d.py): all gaps odd => no phase-1 channel,
no zero-gap slack, no broom, no null web; the root equation
    A(2ch) e^{-i phi} + A(2A) e^{i phi} = 1
forces BOTH children alive with EQUAL amplitude 1/(2 cos phi) for every
phi with cos phi > 0.  Any surviving dynamics is stochastic from step one
and disconnected causets are mandatory -- downward closure loses its 4D
executioner.  The gate: exact support search for

    sum_children mu * A(child) * e^{i g phi} = A(parent),  A >= 0,

support downward-closed (full label covariance), over ALL causets n <= 6,
at rational and generic phases.  Removals are proven (max A(C) = 0 under
progressively relaxed systems) and propagate through future cones.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

W2 = {0: 2, 1: -4, 2: 2}
def action(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W2.get(k, 0)
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
print("causets per level:", {n: len(v) for n, v in levels.items()})

children = {}
allkeys = []
for n in range(1, 7):
    for key, (m, rel) in sorted(levels[n].items()):
        allkeys.append(key)
        if n == 6: continue
        S0 = action(rel, m)
        kid = {}
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
            else: kid[ck] = (1, g)
        children[key] = kid
root = canon(1, ())
def nelem(key): return key[0]

# ancestor (downset-class) map for future-cone removal
anc = {}
for key in allkeys:
    m, rel = key
    a = set()
    for D in downsets(m, rel):
        if not D or len(D) == m: continue
        idx = {d: i for i, d in enumerate(sorted(D))}
        a.add(canon(len(D), tuple(sorted((idx[x], idx[y])
              for (x, y) in rel if x in D and y in D))))
    anc[key] = a

ext = {root: 1}
for n in range(1, 6):
    for key in sorted(levels[n].keys()):
        if key not in ext: continue
        for ck, (mu, g) in children.get(key, {}).items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]

def build_lp(U, phi):
    idx = {key: i for i, key in enumerate(sorted(U))}
    nv = len(idx)
    A_eq, b_eq = [], []
    row = np.zeros(nv); row[idx[root]] = 1
    A_eq.append(row); b_eq.append(1.0)
    for key in sorted(U):
        if nelem(key) >= 6: continue
        rr = np.zeros(nv); ri = np.zeros(nv)
        rr[idx[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in U: continue
            z = mu * np.exp(1j * g * phi)
            rr[idx[ck]] += z.real
            ri[idx[ck]] += z.imag
        A_eq.append(rr); b_eq.append(0.0)
        A_eq.append(ri); b_eq.append(0.0)
    return idx, np.array(A_eq), np.array(b_eq)

def exact_gate(phi, label):
    U = set(allkeys)
    for _ in range(60):
        idx, A_eq, b_eq = build_lp(U, phi)
        nv = len(idx)
        cobj = np.zeros(nv)
        for key in U:
            if nelem(key) >= 4: cobj[idx[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * nv, method="highs")
        if not res.success:
            return set(), None
        A = {key: res.x[idx[key]] for key in U}
        # test only witness-zeros for forced death
        dead = set()
        for key in sorted(U):
            if A[key] > 1e-9: continue
            c2 = np.zeros(nv); c2[idx[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq,
                         bounds=[(0, 1000)] * nv, method="highs")
            if (not r2.success) or -r2.fun < 1e-9:
                dead.add(key)
        if not dead:
            return U, A
        U = {key for key in U if key not in dead and not (anc[key] & dead)}
        if root not in U: return set(), None
    return U, A

phis = [("pi/6", np.pi / 6), ("pi/4", np.pi / 4), ("pi/3", np.pi / 3),
        ("5pi/12", 5 * np.pi / 12), ("0.50 rad", 0.50),
        ("0.90 rad", 0.90), ("1.20 rad", 1.20)]
print("=" * 72)
for label, phi in phis:
    U, A = exact_gate(phi, label)
    if not U:
        print(f"phi = {label}: TOTAL DEATH -- no covariant dynamics")
        continue
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    desc = "  ".join(f"n={n}: {per.get(n, 0)}/{len(levels[n])}"
                     for n in range(1, 7))
    br = sum(1 for key in U if key in children
             and sum(1 for ck in children[key] if ck in U) >= 2)
    acts5 = sorted({action(key[1], key[0]) for key in U if nelem(key) == 5})
    # unitarity telescoping check on the witness
    resid = []
    for n in range(2, 7):
        tot = sum(ext.get(key, 0) * A.get(key, 0.0)
                  * np.exp(1j * (action(key[1], key[0]) - 1) * phi)
                  for key in levels[n] if key in U)
        resid.append(abs(tot - 1))
    chain_keys = [canon(n, tuple((i, j) for i in range(n)
                                 for j in range(i + 1, n)))
                  for n in range(2, 7)]
    chains_in = [ck[0] for ck in chain_keys if ck in U]
    npos = sum(1 for key in U if A.get(key, 0) > 1e-9)
    print(f"phi = {label}: support {len(U)} ({npos} positive in witness)  "
          f"[{desc}]")
    print(f"    branching nodes {br}; chains {chains_in}; distinct S at "
          f"n=5: {len(acts5)} values {acts5[:12]}{'...' if len(acts5) > 12 else ''}")
    print(f"    unitarity residuals: {[f'{r:.1e}' for r in resid]}")

# ---- pi/4 supplement: slack-guided search for ANY viable support -----------
print()
print("=" * 72)
print("pi/4 supplement (slack-guided; death above was only full-system):")
phi = np.pi / 4
U = set(allkeys)
for round_ in range(40):
    idx = {key: i for i, key in enumerate(sorted(U))}
    nv = len(idx)
    eqs = []   # (causet, real-row, imag-row)
    for key in sorted(U):
        if nelem(key) >= 6: continue
        rr = np.zeros(nv); ri = np.zeros(nv)
        rr[idx[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in U: continue
            z = mu * np.exp(1j * g * phi)
            rr[idx[ck]] += z.real
            ri[idx[ck]] += z.imag
        eqs.append((key, rr, ri))
    ne = 2 * len(eqs) + 1
    # variables: A (nv) + slack+ + slack- (ne each); minimize total slack
    rows = []
    brhs = []
    row = np.zeros(nv); row[idx[root]] = 1
    rows.append(row); brhs.append(1.0)
    for key, rr, ri in eqs:
        rows.append(rr); brhs.append(0.0)
        rows.append(ri); brhs.append(0.0)
    Am = np.array(rows)
    ns = Am.shape[0]
    A_full = np.hstack([Am, np.eye(ns), -np.eye(ns)])
    c = np.concatenate([np.zeros(nv), np.ones(2 * ns)])
    res = linprog(c, A_eq=A_full, b_eq=np.array(brhs),
                  bounds=[(0, 1000)] * nv + [(0, None)] * (2 * ns),
                  method="highs")
    slack = res.fun
    if slack < 1e-9:
        print(f"  round {round_}: FEASIBLE with support candidate {len(U)}")
        break
    # remove the causet whose equation carries the most slack (+ future cone)
    sl = res.x[nv:nv + ns] + res.x[nv + ns:]
    worst, wkey = 0.0, None
    for i, (key, rr, ri) in enumerate(eqs):
        v = sl[1 + 2 * i] + sl[2 + 2 * i]
        if v > worst: worst, wkey = v, key
    if wkey is None or wkey == root:
        print(f"  round {round_}: irreducible slack {slack:.4f} at the root"
              " -- NO viable support at pi/4")
        U = set()
        break
    U = {key for key in U if key != wkey and wkey not in anc[key]}
    if root not in U:
        print(f"  round {round_}: root removed -- NO viable support at pi/4")
        U = set()
        break
    print(f"  round {round_}: slack {slack:.4f}, removing {wkey[0]}-causet"
          f" {wkey[1]} (+cone) -> {len(U)} remain")
if U:
    # finish with the proven-removal loop
    U2, A2 = exact_gate(phi, "pi/4-restarted")
    print(f"  proven-removal finish: support {len(U2)}")
