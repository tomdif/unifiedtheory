#!/usr/bin/env python3
"""Composability probe of the phi = 8pi resonant sector — EXACT.

QUESTION: does the resonant family at eps = 1/4, phi = 8pi contain a
BRANCHING member whose amplitudes factorize on disjoint unions,
  Ã(C1 ⊔ C2) = Ã(C1) · Ã(C2)   [ORBIT counting convention: one
  amplitude per isomorphism class, no interleaving multiplicities —
  stated explicitly because the labeled and event conventions give
  different theorems; note the EVENT-form cluster gate's root
  obstruction is cos(phi) = 1 (Paper 3), which is SATISFIED at the
  resonances — the third sector is exactly where that obstruction
  vanishes].

Structure that makes the probe exact: within the surviving web every
channel phase is +-1 and every multiplicity is an integer, so the sum
rules are integer-linear; factorization makes each disconnected
survivor's amplitude the product of its (strictly smaller, hence
already assigned) components' amplitudes; the free variables at each
level are the CONNECTED survivors.  The system is therefore solved
level by level in exact rational arithmetic: float LP proposes a
vertex, Fraction-rounding + exact verification certifies it.

PRE-REGISTERED READINGS:
  - exact branching factorizing member found -> composability is
    COMPATIBLE with branching at the resonance (orbit convention);
    the earlier chat claim 'factorizing => dust' was wrong (it killed
    only the chain cone and V); the sector must then face
    real-amplitude-QM exclusion arguments (Renou et al.) on their
    merits.
  - sequential solve infeasible at some level -> evidence toward the
    composability no-go, NOT a theorem (greedy has no backtracking);
    reported as such.
Known forced values (n <= 3, orbit form): Ã(2A) = 1 forces
Ã(2ch) = 0; 2A's equation then forces Ã(3A) + Ã(V) = 1 with
Ã(3A) = 1, so Ã(V) = 0; the claw remains free at 3A's equation.
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

# ---- machinery (exact weights, canon, tree, gate) --------------------------
src = open("resonant_sector_scan.py").read()
cut = src.index("def run_point")
exec(src[:cut])          # W_exact, canon_fast, levels, counts, root, allkeys...

eps, q = Fraction(1, 4), 4     # phi = 8pi
W = {k: W_exact(k, eps) for k in range(0, NMAX)}
linkang = {k: (-W[k] * 2 * q) % 2 for k in W}

def S_angle(rel, m):
    ang = (Fraction(m) * 2 * q) % 2
    for k in link_ks(rel, m):
        ang = (ang + linkang[k]) % 2
    return ang

def link_ks(rel, m):
    relset = set(rel)
    return [sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
            for (a, b) in rel]

children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        SA = S_angle(rel, m)
        kid = {}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            gang = (S_angle(nr, m + 1) - SA) % 2
            if ck in kid:
                mu, gg = kid[ck]; kid[ck] = (mu + 1, gg)
            else: kid[ck] = (1, gang)
        children[key] = kid

def descendants(seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out

def cph(ang):
    a = float(ang) * np.pi
    return complex(np.cos(a), np.sin(a))

def nelem(key): return key[0]

U = set(allkeys)
for rnd in range(80):
    kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
    A_eq, b_eq = [], []
    r0 = np.zeros(len(kk)); r0[ii[root]] = 1
    A_eq.append(r0); b_eq.append(1.0)
    for key in kk:
        if nelem(key) >= NMAX: continue
        rr = np.zeros(len(kk)); ri = np.zeros(len(kk))
        rr[ii[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in U: continue
            z = mu * cph(g)
            rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
        A_eq.append(rr); b_eq.append(0.0); A_eq.append(ri); b_eq.append(0.0)
    A_eq = np.array(A_eq); b_eq = np.array(b_eq)
    cobj = np.zeros(len(kk))
    for key in U:
        if nelem(key) >= 5: cobj[ii[key]] = -1.0
    res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                  method="highs")
    if not res.success: U = set(); break
    Av = {k: res.x[ii[k]] for k in kk}
    dead = set()
    for key in kk:
        if Av[key] > 1e-9: continue
        c2o = np.zeros(len(kk)); c2o[ii[key]] = -1.0
        r2 = linprog(c2o, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                     method="highs")
        if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
    if not dead: break
    U = U - descendants(dead)
assert len(U) == 1081, f"survivor rebuild mismatch: {len(U)}"
print(f"survivor web rebuilt: {len(U)}", flush=True)

# exact +-1 phases within the web
def sigma(g):
    a = g % 2
    assert a in (Fraction(0), Fraction(1)), f"non-real channel {g}"
    return 1 if a == 0 else -1

# ---- connected components --------------------------------------------------
def components(key):
    m, rel = key
    parent = list(range(m))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for (a, b) in rel:
        ra, rb = find(a), find(b)
        if ra != rb: parent[ra] = rb
    groups = {}
    for v in range(m): groups.setdefault(find(v), []).append(v)
    comps = []
    for g in groups.values():
        gi = {v: i for i, v in enumerate(sorted(g))}
        sub = tuple(sorted((gi[a], gi[b]) for (a, b) in rel
                           if a in gi and b in gi))
        comps.append(canon_fast(len(g), sub))
    return sorted(comps)

conn = {key: len(components(key)) == 1 for key in allkeys}
nconn = {n: sum(1 for key in U if nelem(key) == n and conn[key])
         for n in range(1, NMAX + 1)}
print("connected survivors per level:", nconn, flush=True)

# ---- parent map (for downward-closure enforcement) -------------------------
parents = {}
for key in allkeys:
    m, rel = key
    if m == 1: parents[key] = []; continue
    ups = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    mx = [v for v in range(m) if not [b for (a, b) in rel if a == v]]
    # maximal = elements with nothing ABOVE them: (a,b) means a below b
    mx = [v for v in range(m) if not any(a == v for (a, b) in rel if False)]
    above = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    mx = [v for v in range(m) if not above[v]]
    ps = set()
    for v in mx:
        keep = [u for u in range(m) if u != v]
        gi = {u: i for i, u in enumerate(keep)}
        sub = tuple(sorted((gi[a], gi[b]) for (a, b) in rel
                           if a in gi and b in gi))
        ps.add(canon_fast(m - 1, sub))
    parents[key] = sorted(ps)

# ---- sequential exact solve with CLOSURE loop ------------------------------
# Support downward-closure is definitional (transition amplitudes are
# ratios A(child)/A(parent)): a member with A(C)=0 but a positive
# descendant is NOT a dynamics.  Enforce by fixed-point forcing: solve,
# zero out any positive causet with a zero parent, re-solve.
forced_zero = set()
value = {}
feasible = True
for closure_round in range(40):
  value = {root: Fraction(1)}
  feasible = True
  for n in range(1, NMAX):
    lvl_next = [key for key in sorted(U) if nelem(key) == n + 1]
    unknowns = [key for key in lvl_next if conn[key]
                and key not in forced_zero]
    uix = {k: i for i, k in enumerate(unknowns)}
    for key in lvl_next:
        if key in forced_zero and conn[key]:
            value[key] = Fraction(0)
        elif not conn[key]:
            v = Fraction(1)
            for c in components(key):
                assert c in U, "component of survivor not a survivor"
                v *= value[c]
            value[key] = Fraction(0) if key in forced_zero else v
    rows, rhs = [], []
    for key in sorted(U):
        if nelem(key) != n: continue
        row = [Fraction(0)] * len(unknowns)
        const = Fraction(0)
        for ck, (mu, g) in children[key].items():
            if ck not in U: continue
            s = mu * sigma(g)
            if ck in uix: row[uix[ck]] += s
            else: const += s * value[ck]
        rows.append(row); rhs.append(value[key] - const)
    if unknowns:
        A = np.array([[float(x) for x in r] for r in rows])
        b = np.array([float(x) for x in rhs])
        sol = None
        r = None
        for obj in ("maxsum", "zero"):
            c = -np.ones(len(unknowns)) if obj == "maxsum" \
                else np.zeros(len(unknowns))
            r = linprog(c, A_eq=A, b_eq=b, bounds=[(0, 100)] * len(unknowns),
                        method="highs")
            if not r.success: continue
            for dlim in (2**12, 2**20, 2**30, 2**40):
                cand = [Fraction(x).limit_denominator(dlim) for x in r.x]
                if all(x >= 0 for x in cand) and all(
                        sum(rw[i] * cand[i] for i in range(len(cand))) == rh
                        for rw, rh in zip(rows, rhs)):
                    sol = cand; break
            if sol: break
        if sol is None:
            print(f"  round {closure_round}: LEVEL {n}->{n+1} no "
                  f"exactly-verified nonneg solution (float LP "
                  f"{'feasible' if (r is not None and r.success) else 'INFEASIBLE'})",
                  flush=True)
            feasible = False
            break
        for k, v in zip(unknowns, sol): value[k] = v
    else:
        bad = [i for i, (rw, rh) in enumerate(zip(rows, rhs)) if rh != 0]
        if bad:
            print(f"  round {closure_round}: LEVEL {n} inconsistent with "
                  f"no unknowns", flush=True)
            feasible = False
            break
  if not feasible:
      break
  # closure violations: positive causet with a zero parent
  viol = set()
  for key in sorted(U):
      if value.get(key, Fraction(0)) <= 0: continue
      for p in parents[key]:
          if p in U and value.get(p, Fraction(0)) == 0:
              viol.add(key); break
  if not viol:
      print(f"closure fixed point after {closure_round + 1} round(s); "
            f"forced-zero set {len(forced_zero)}", flush=True)
      break
  forced_zero |= viol
  # cascade: descendants of forced-zero also forced
  forced_zero |= descendants(forced_zero) - {root}
  print(f"  round {closure_round}: {len(viol)} closure violations -> "
        f"forced-zero now {len(forced_zero)}", flush=True)

if feasible:
    # branching census of the factorizing member
    supp = {k for k, v in value.items() if v > 0}
    br = [key for key in supp if key in children and sum(
        1 for ck in children[key] if ck in supp) >= 2]
    print(f"\nEXACT FACTORIZING MEMBER FOUND: support {len(supp)}, "
          f"branching nodes {len(br)}")
    print("sample values (n <= 4):")
    for key in sorted(value):
        if nelem(key) <= 4:
            tag = "conn" if conn[key] else "disc"
            print(f"  n={nelem(key)} {tag} {key[1]}: {value[key]}")
    if br:
        print("branching examples:", [k[1] for k in br[:4]])
        print("\nREADING (pre-registered): composability is COMPATIBLE with "
              "branching at the resonance under orbit counting; "
              "'factorizing => dust' is retracted; Renou-type exclusion "
              "must be engaged on the merits.")
    else:
        print("\nREADING: factorizing member exists but is branch-free "
              "(deterministic) — composability incompatible with branching "
              "along this greedy path; not yet a theorem.")
else:
    print("\nREADING (pre-registered): greedy infeasibility is EVIDENCE for "
          "the composability no-go, not a theorem (no backtracking).")
print("DONE", flush=True)
