#!/usr/bin/env python3
"""Era-boundary sweep: close the quantum gate's [PHYS] caveat mechanically.

A quantum era boundary seeds a new era on some causet C (always of
unique-maximum form: previous causet + its cap).  The era gate for seed C:
  * entry: the first birth is forced (unique child), amplitude 1, required
    phase h(C)*phi  =>  h(C)*phi = 0 mod 2pi  (admissibility: 9 | h(C) at
    b=9 windows, 3 | h(C) at k=3);
  * gregarious constraint then forces all denominators real positive
    (arg D_r = -h(C)*phi = 0), exactly as in era 2;
  * transition classes: (g(C u D) - h(C)) mod 9 = g mod 9 for admissible
    seeds -- the era-2 constraint system with seed-shifted precursor gaps.
Sweep: ALL unique-maximum seeds |C| <= 5 (a superset of reachable
boundary seeds), windows k in {1,2,3,4}, relative depth r <= 3,
zero-pattern LP as in quantum_gate_b9.py.  A "genuinely quantum" survivor
is a feasible pattern with a live signature of class != 0 (non-real
forced phase).  If none exists anywhere, the caveat dies.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

W = {0: 1, 1: -9, 2: 16, 3: -8}
def action_units(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W.get(k, 0)
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

def maximals(rel, S):
    return [d for d in S if not any((d, e) in rel for e in S)]

# ---- seeds: unique-maximum causets, |C| <= 5 -------------------------------
levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 5):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
seeds = []
for n in range(1, 6):
    for key, (m, rel) in sorted(levels[n].items()):
        if len(maximals(set(rel), set(range(m)))) == 1 or m == 1:
            seeds.append((m, rel))
print(f"unique-maximum seeds |C| <= 5: {len(seeds)}")

# ---- relative posets to size 3 (era depth), and lambda machinery -----------
rel_levels = {0: {canon(0, ()): (0, ())}}
for r in range(0, 3):
    nxt = {}
    for key, (m, rel) in rel_levels[r].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    rel_levels[r + 1] = nxt

SIGS = [(v, m) for v in range(1, 4) for m in range(1, v + 1)]
def lam_coeff(v, m):
    c = np.zeros(4)
    for j in range(m, v + 1):
        c[j] = math.comb(v - m, j - m)
    return c
LAM = {s: lam_coeff(*s) for s in SIGS}
DEN = {r: np.array([math.comb(r, j) if j <= r else 0 for j in range(4)],
                   dtype=float) for r in range(4)}

def era_gap(seedrel, nC, relR, mR, D):
    """gap of birth above C u D inside host C+R (depends only on C u D)."""
    # absolute host: C, then R shifted by nC, all above all of C
    arel = set(seedrel)
    arel |= {(a + nC, b + nC) for (a, b) in relR}
    arel |= {(c, e + nC) for c in range(nC) for e in range(mR)}
    an = nC + mR
    S0 = action_units(tuple(sorted(arel)), an)
    P = {c for c in range(nC)} | {d + nC for d in D}
    crel = tuple(sorted(arel | {(p, an) for p in P}))
    return action_units(crel, an + 1) - S0

def solve_seed(seedrel, nC, k, b):
    phi_cls = 9 if b == 9 else 3
    h = era_gap(seedrel, nC, (), 0, frozenset())
    if h % phi_cls != 0:
        return "inadmissible", None
    # transitions per relative node, classes (g - h) mod 9 (== g mod 9 here,
    # but keep the general form)
    transitions = {}
    for r in range(0, 4):
        for key, (m, rel) in rel_levels[r].items():
            tr = []
            for D in downsets(m, rel):
                sig = (len(D), len(maximals(set(rel), D))) if D else (0, 0)
                g = era_gap(seedrel, nC, rel, m, D)
                tr.append((sig, (g - h) % 9, D, rel, m))
            transitions[(r, key)] = tr
    best = None
    for nz in range(len(SIGS) + 1):
        for zero in itertools.combinations(SIGS, nz):
            zero = set(zero)
            reach = {(0, canon(0, ()))}
            frontier = [(0, canon(0, ()))]
            while frontier:
                r, key = frontier.pop()
                if r >= 3: continue
                for sig, cls, D, rel, m in transitions[(r, key)]:
                    if sig != (0, 0) and sig in zero: continue
                    nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                    ck = canon(m + 1, nr)
                    if (m + 1, ck) not in reach:
                        reach.add((m + 1, ck)); frontier.append((m + 1, ck))
            req = {}; ok = True
            for (r, key) in reach:
                for sig, cls, D, rel, m in transitions[(r, key)]:
                    if sig == (0, 0):
                        if cls % (9 if b == 9 else 3) not in (0,) and cls != 0:
                            pass
                        continue
                    if sig in zero: continue
                    req.setdefault(sig, set()).add(cls)
            for sig, cl in req.items():
                if b == 3:
                    cl = {c % 3 for c in cl}
                if len(cl) > 1: ok = False
            if not ok: continue
            A_eq, b_eq, A_ub, b_ub = [], [], [], []
            EPS = 1e-3
            def rows(cvec, phase):
                rr = np.zeros(6); ri = np.zeros(6)
                for j in range(1, 4):
                    c = cvec[j] * np.exp(-1j * phase)
                    rr[2*(j-1)] += c.real; rr[2*(j-1)+1] += -c.imag
                    ri[2*(j-1)] += c.imag; ri[2*(j-1)+1] += c.real
                return rr, ri
            for sig in SIGS:
                cvec = LAM[sig]
                if sig in zero:
                    rr, ri = rows(cvec, 0.0)
                    A_eq += [rr, ri]; b_eq += [0.0, 0.0]
                elif sig in req:
                    cls = next(iter(req[sig])) % (9 if b == 9 else 3)
                    tau = 2 * np.pi * ((cls * k) % 9) / 9 if b == 9 else \
                          2 * np.pi * ((cls * 1) % 3) / 3
                    rr, ri = rows(cvec, tau)
                    A_eq.append(ri); b_eq.append(0.0)
                    A_ub.append(-rr); b_ub.append(-EPS)
            for r in range(1, 4):
                if not any(rr_ == r for (rr_, kk_) in reach): continue
                rr, ri = rows(DEN[r], 0.0)
                A_eq.append(ri); b_eq.append(0.0)
                A_ub.append(-rr); b_ub.append(DEN[r][0] - EPS)
            res = linprog(np.zeros(6), A_ub=np.array(A_ub) if A_ub else None,
                          b_ub=np.array(b_ub) if b_ub else None,
                          A_eq=np.array(A_eq) if A_eq else None,
                          b_eq=np.array(b_eq) if b_eq else None,
                          bounds=[(-50, 50)] * 6, method="highs")
            if not res.success: continue
            live = [s_ for s_ in SIGS if s_ not in zero and s_ in req]
            quantum = [s_ for s_ in live
                       if (next(iter(req[s_])) * k) % (9 if b == 9 else 3) != 0]
            cand = (len(quantum), len(live), live, quantum)
            if best is None or cand > best: best = cand
    return "ok", best

print("=" * 72)
any_quantum = False
for k, b in [(1, 9), (2, 9), (4, 9), (3, 3)]:
    n_adm = n_dead = n_real = n_quantum = 0
    examples = []
    for (nC, seedrel) in seeds:
        status, best = solve_seed(seedrel, nC, k, b)
        if status == "inadmissible": continue
        n_adm += 1
        if best is None or best[1] == 0: n_dead += 1
        elif best[0] == 0:
            n_real += 1
            if len(examples) < 2: examples.append((nC, seedrel, best))
        else:
            n_quantum += 1; any_quantum = True
            examples.append((nC, seedrel, best))
    print(f"k={k} (b={b}): admissible seeds {n_adm}/{len(seeds)}; "
          f"broom-only {n_dead}, real-remnant {n_real}, "
          f"GENUINELY QUANTUM {n_quantum}")
    for nC, sr, best in examples[:3]:
        print(f"    seed n={nC} rel={sr}: live {best[2]}, quantum {best[3]}")
print("=" * 72)
print("CAVEAT " + ("REMAINS: quantum survivor found above." if any_quantum
      else "CLOSED (to seed size 5, depth 3): no era admits any live"
           " signature with a non-real forced phase at any b=9 window;"
           " every admissible era is broom-or-real-remnant, like era 2."))
