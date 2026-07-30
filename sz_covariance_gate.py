#!/usr/bin/env python3
"""THE NON-FACTORED COVARIANCE GATE: the one door, run mechanically.

Family: the maximally general quantum growth dynamics carrying the ansatz
phases -- one amplitude per (parent, downset-orbit), constrained ONLY by
  (i)  ansatz phases:  a = rho * e^{i g phi},  rho >= 0,  g = BD gap;
  (ii) Markov sum rule per reachable node:  sum a = 1;
  (iii) discrete general covariance: the product of amplitudes along any
        labeled path depends only on the endpoint's isomorphism class.
Bell causality and signature-factoring are DROPPED -- this is exactly the
door the two-gate no-go left open.

Reduction (proved in the report): covariance <=> the amplitude is a
coboundary  a(C -> C') = [A(C')/A(C)] e^{i g phi}  with A >= 0 per
unlabeled causet, and the whole system becomes the WAVE EQUATION ON THE
CAUSET TREE:

    sum_{children C'} mu(C -> C') * A(C') * e^{i g(C->C') phi}  =  A(C)

for every supported causet C (A(C) > 0), A(bullet) = 1, mu = number of
distinct downsets realizing the link.  Supported causets with a supported
parent are exactly the formed universes; the minimal-cover theorem
guarantees a gap-0 slack channel at every node.

Gate: for phi = 2 pi k / 9, find the maximal support to n = 6 (local
cone-feasibility fixpoint, then one global LP).  PASS = support beyond
brooms (the ansatz HAS covariant quantum dynamics once factoring is
dropped -- answering the paper's open problem in the negative and
constructively).  FAIL = brooms only (the no-go is unconditional).
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

W = {0: 1, 1: -9, 2: 16, 3: -8}
def action_units(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        kk = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W.get(kk, 0)
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

# ---- tree to n = 6 with multiplicities and gaps ----------------------------
levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
print("causets per level:", {n: len(v) for n, v in levels.items()})

children = {}     # key -> {childkey: (mu, gap)}
allkeys = []
for n in range(1, 7):
    for key, (m, rel) in sorted(levels[n].items()):
        allkeys.append(key)
        if n == 6: continue
        S0 = action_units(rel, m)
        kid = {}
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon(m + 1, nr)
            g = action_units(nr, m + 1) - S0
            if ck in kid:
                assert kid[ck][1] == g
                kid[ck] = (kid[ck][0] + 1, g)
            else:
                kid[ck] = (1, g)
        children[key] = kid
parents = {}
for key, kid in children.items():
    for ck in kid:
        parents.setdefault(ck, []).append(key)
root = canon(1, ())

def nelem(key): return key[0]
def is_broomish(key):
    # broom-forest-with-caps heuristic label not needed; report by structure
    return None

def run_window(k):
    phi = 2 * np.pi * k / 9
    ph = {}
    for key, kid in children.items():
        for ck, (mu, g) in kid.items():
            ph[(key, ck)] = np.exp(1j * g * phi)
    # ---- local feasibility fixpoint -------------------------------------
    S = set(allkeys)
    changed = True
    while changed:
        changed = False
        for key in list(S):
            n = nelem(key)
            # reachability: some supported parent (root exempt)
            if key != root and not any(p in S for p in parents.get(key, [])):
                S.discard(key); changed = True; continue
            if n >= 6 or key not in children: continue
            kids = [(ck, mu, g) for ck, (mu, g) in children[key].items()
                    if ck in S]
            if not kids:
                S.discard(key); changed = True; continue
            # cone check: exists x >= 0 with sum mu x e^{i g phi} = 1
            A_eq = np.zeros((2, len(kids)))
            for i, (ck, mu, g) in enumerate(kids):
                z = mu * np.exp(1j * g * phi)
                A_eq[0, i] = z.real
                A_eq[1, i] = z.imag
            res = linprog(np.zeros(len(kids)), A_eq=A_eq, b_eq=[1.0, 0.0],
                          bounds=[(0, None)] * len(kids), method="highs")
            if not res.success:
                S.discard(key); changed = True
    # ---- global LP on the fixpoint support ------------------------------
    idx = {key: i for i, key in enumerate(sorted(S))}
    nv = len(idx)
    A_eq, b_eq = [], []
    # A(root) = 1
    row = np.zeros(nv); row[idx[root]] = 1
    A_eq.append(row); b_eq.append(1.0)
    for key in sorted(S):
        n = nelem(key)
        if n >= 6: continue
        rr = np.zeros(nv); ri = np.zeros(nv)
        rr[idx[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in S: continue
            z = mu * np.exp(1j * g * phi)
            rr[idx[ck]] += z.real
            ri[idx[ck]] += z.imag
        A_eq.append(rr); b_eq.append(0.0)
        A_eq.append(ri); b_eq.append(0.0)
    # objective: maximize amplitude pushed to depth 6 (spread support)
    c = np.zeros(nv)
    for key in S:
        if nelem(key) >= 5: c[idx[key]] = -1.0
    res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=[(0, 100)] * nv, method="highs")
    if not res.success:
        return S, None, None
    A = {key: res.x[idx[key]] for key in S}
    supp = {key for key in S if A[key] > 1e-9}
    return S, A, supp

def connected(supp):
    """causets in supp reachable from the root via parent links in supp."""
    cc = {root} if root in supp else set()
    changed = True
    while changed:
        changed = False
        for key in supp:
            if key in cc: continue
            if any(p in cc for p in parents.get(key, [])):
                cc.add(key); changed = True
    return cc

def run_window_connected(k):
    """iterate: LP witness -> connected component -> re-solve on it."""
    S, A, supp = run_window(k)
    if A is None: return S, None, None
    for _ in range(12):
        cc = connected(supp)
        if cc == supp: return S, A, supp
        # re-solve with candidate support = connected component
        phi = 2 * np.pi * k / 9
        idx = {key: i for i, key in enumerate(sorted(cc))}
        nv = len(idx)
        A_eq, b_eq = [], []
        row = np.zeros(nv); row[idx[root]] = 1
        A_eq.append(row); b_eq.append(1.0)
        for key in sorted(cc):
            if nelem(key) >= 6: continue
            rr = np.zeros(nv); ri = np.zeros(nv)
            rr[idx[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in cc: continue
                z = mu * np.exp(1j * g * phi)
                rr[idx[ck]] += z.real
                ri[idx[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        c = np.zeros(nv)
        for key in cc:
            if nelem(key) >= 5: c[idx[key]] = -1.0
        res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                      bounds=[(0, 100)] * nv, method="highs")
        if not res.success: return S, None, None
        A = {key: res.x[idx[key]] for key in cc}
        supp = {key for key in cc if A[key] > 1e-9}
    return S, A, supp

def describe(supp):
    per = {}
    for key in supp:
        per.setdefault(nelem(key), []).append(key)
    out = []
    for n in sorted(per):
        tot = len(levels[n])
        out.append(f"n={n}: {len(per[n])}/{tot}")
    return "  ".join(out)

print("=" * 72)
for k in (1, 2, 4, 3):
    S, A, supp = run_window_connected(k)
    if A is None:
        print(f"k={k}: fixpoint support {len(S)} but GLOBAL LP infeasible")
        continue
    print(f"k={k}: fixpoint {len(S)} causets; global LP FEASIBLE; "
          f"positive support {len(supp)}:")
    print(f"   {describe(supp)}")
    # is anything beyond the broom family supported? check chains explicitly
    chain_keys = [canon(n, tuple((i, j) for i in range(n)
                                 for j in range(i + 1, n)))
                  for n in range(2, 7)]
    chains_in = [ck[0] for ck in chain_keys if ck in supp]
    print(f"   chains supported at sizes: {chains_in}")
    # sample amplitudes on small causets
    if A:
        small = [(key, A[key]) for key in sorted(supp) if nelem(key) <= 3]
        print("   A on n<=3:", [(key[0], key[1], round(a, 4))
                                for key, a in small])
print("=" * 72)
print("PASS at a window = support beyond brooms (chains etc.) => the")
print("non-factored covariant dynamics EXISTS at that hbar; the open")
print("problem is answered NO (covariance does not force factoring) and")
print("Bell causality is exposed as the classical no-go's true culprit.")

# ---- deep-dive on the selected window k = 4 --------------------------------
print()
print("=" * 72)
print("k=4 witness deep-dive:")
S, A, supp = run_window_connected(4)
phi = 2 * np.pi * 4 / 9
for n in (4, 5):
    names = sorted((key for key in supp if nelem(key) == n))
    print(f"  supported n={n} causets ({len(names)}):")
    for key in names:
        print(f"    {key[1]}   A={A[key]:.4f}")
# branching check: supported parents with >= 2 supported children
br = 0
for key in supp:
    if key in children:
        ns = sum(1 for ck in children[key] if ck in supp)
        if ns >= 2: br += 1
print(f"  supported causets with >= 2 supported children: {br}")
# linear-extension counts (number of labeled formation paths) by DP
ext = {root: 1}
for n in range(1, 6):
    for key in sorted(levels[n].keys()):
        if key not in ext: continue
        for ck, (mu, g) in children.get(key, {}).items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]
# decoherence functional on supported 4-stems
stems = sorted(key for key in supp if nelem(key) == 4)
def act(key):
    return action_units(key[1], key[0])
Psi = {key: ext[key] * A[key] * np.exp(1j * act(key) * phi) for key in stems}
Dm = np.array([[Psi[a] * np.conj(Psi[b]) for b in stems] for a in stems])
tot = sum(Psi.values())
print(f"  4-stem event amplitudes Psi (ext * A * e^{{iS phi}}):")
for key in stems:
    print(f"    {key[1]}: |Psi| = {abs(Psi[key]):.4f}, "
          f"arg = {np.angle(Psi[key]):.3f}")
print(f"  |sum Psi|^2 = {abs(tot)**2:.4f} (unitarity-of-partition probe)")
print(f"  diag(D) = {np.array2string(np.real(np.diag(Dm)), precision=4)}")
print(f"  max |off-diag| = "
      f"{np.max(np.abs(Dm - np.diag(np.diag(Dm)))):.4f}  "
      "(nonzero = genuine interference between 4-geometries)")

# ---- THE CORRECTED GATE: full covariance = downward-closed support ---------
print()
print("=" * 72)
print("CORRECTED GATE (downward closure: every parent of a supported causet")
print("must be supported -- full label-covariance):")

def run_window_closed(k):
    phi = 2 * np.pi * k / 9
    S = set(allkeys)
    for _ in range(40):
        # downward-closure + reachability prune
        changed = True
        while changed:
            changed = False
            for key in list(S):
                if key == root: continue
                ps = parents.get(key, [])
                if not all(p in S for p in ps):
                    S.discard(key); changed = True
        # global LP on S
        idx = {key: i for i, key in enumerate(sorted(S))}
        nv = len(idx)
        A_eq, b_eq = [], []
        row = np.zeros(nv); row[idx[root]] = 1
        A_eq.append(row); b_eq.append(1.0)
        for key in sorted(S):
            if nelem(key) >= 6: continue
            rr = np.zeros(nv); ri = np.zeros(nv)
            rr[idx[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in S: continue
                z = mu * np.exp(1j * g * phi)
                rr[idx[ck]] += z.real
                ri[idx[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        c = np.zeros(nv)
        for key in S:
            if nelem(key) >= 4: c[idx[key]] = -1.0
        res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                      bounds=[(0, 100)] * nv, method="highs")
        if not res.success: return None, None
        A = {key: res.x[idx[key]] for key in S}
        supp = {key for key in S if A[key] > 1e-9}
        if supp == S: return A, supp
        S = supp
    return A, supp

for k in (4, 2, 1, 3):
    A, supp = run_window_closed(k)
    if A is None:
        print(f"k={k}: infeasible"); continue
    per = {}
    for key in supp: per.setdefault(nelem(key), 0)
    for key in supp: per[nelem(key)] += 1
    desc = "  ".join(f"n={n}: {per.get(n,0)}/{len(levels[n])}"
                     for n in range(1, 7))
    chain_keys = [canon(n, tuple((i, j) for i in range(n)
                                 for j in range(i + 1, n)))
                  for n in range(2, 7)]
    chains_in = [ck[0] for ck in chain_keys if ck in supp]
    # unitarity: sum over n-stems of ext*A*e^{i(S-1)phi} must be 1
    phi = 2 * np.pi * k / 9
    ext = {root: 1}
    for n in range(1, 6):
        for key in sorted(levels[n].keys()):
            if key not in ext: continue
            for ck, (mu, g) in children.get(key, {}).items():
                ext[ck] = ext.get(ck, 0) + mu * ext[key]
    resid = []
    for n in range(2, 7):
        tot = sum(ext.get(key, 0) * A.get(key, 0)
                  * np.exp(1j * (action_units(key[1], key[0]) - 1) * phi)
                  for key in levels[n] if key in supp)
        resid.append(abs(tot - 1))
    br = sum(1 for key in supp if key in children
             and sum(1 for ck in children[key] if ck in supp) >= 2)
    print(f"k={k}: support {len(supp)}  [{desc}]")
    print(f"    chains: {chains_in}; branching nodes: {br}; "
          f"unitarity residuals by level: {[f'{r:.1e}' for r in resid]}")
    # distinct action classes in support (interference between geometries)
    acts = sorted({action_units(key[1], key[0]) % 9 for key in supp})
    print(f"    action classes mod 9 in support: {acts}")

# ---- exact search on the originary family ----------------------------------
print()
print("=" * 72)
print("EXACT originary search (equations only at live causets; removals")
print("propagate upward through the future cone):")
orig = [key for key in allkeys
        if len([x for x in range(key[0])
                if not any(b == x for (a, b) in key[1])]) == 1
        or key[0] == 1]
# ancestor map: ancestors(C) = downset classes of C
anc = {}
for key in orig:
    m, rel = key
    a = set()
    for D in downsets(m, rel):
        if not D: continue
        idxm = {d: i for i, d in enumerate(sorted(D))}
        a.add(canon(len(D), tuple(sorted((idxm[x], idxm[y])
              for (x, y) in rel if x in D and y in D))))
    anc[key] = a

def exact_window(k):
    phi = 2 * np.pi * k / 9
    U = set(orig)
    for _ in range(60):
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
        # find forced-dead members: max A(C) == 0
        dead = set()
        for key in sorted(U):
            c = np.zeros(nv); c[idx[key]] = -1.0
            res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                          bounds=[(0, 100)] * nv, method="highs")
            if (not res.success) or -res.fun < 1e-9:
                dead.add(key)
        if not dead:
            # final witness: maximize total deep support
            c = np.zeros(nv)
            for key in U:
                if nelem(key) >= 4: c[idx[key]] = -1.0
            res = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                          bounds=[(0, 100)] * nv, method="highs")
            A = {key: res.x[idx[key]] for key in U}
            return U, A
        # remove dead + upward closure (anything with a dead ancestor)
        U = {key for key in U if key not in dead
             and not (anc[key] & dead)}
        if root not in U: return set(), None
    return U, None

for k in (4, 1, 2, 3):
    U, A = exact_window(k)
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    desc = "  ".join(f"n={n}: {per.get(n, 0)}" for n in range(1, 7))
    acts = sorted({action_units(key[1], key[0]) % 9 for key in U})
    br = sum(1 for key in U if key in children
             and sum(1 for ck in children[key] if ck in U) >= 2)
    print(f"k={k}: FINAL support {len(U)}  [{desc}]")
    print(f"    action classes mod 9: {acts}; branching nodes: {br}")
    if A:
        n5 = [(key[1], round(A[key], 3)) for key in sorted(U)
              if nelem(key) == 5 and A[key] > 1e-9]
        print(f"    supported n=5 (positive in witness): {len(n5)}")
