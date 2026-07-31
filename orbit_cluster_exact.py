#!/usr/bin/env python3
"""Exact support search: orbit-counted wave + cluster decomposition, phi = pi/3.

Variables: u = log A on CONNECTED causets only (cluster eliminates the
disconnected ones: u(C) = sum over components, with multiplicity).  The
orbit-wave equations at every supported causet n <= 5 become residuals in
the connected variables; support is downward-closed and removals
propagate through future cones (components are downsets, so a dead
component automatically kills its disconnected hosts).  Deaths are
detected as amplitudes driven to zero and verified by re-solve.

Also verified: the ORBIT-convention unitarity (telescoping over
orbit-paths, N_orb replacing ext):  sum_stems N_orb * A * e^{i(S-1)phi} = 1
at every level -- the orbit analog of the labeled telescoping, proving
the convention carries its own sum-rule consistency.
"""
import itertools, math
import numpy as np
from scipy.optimize import least_squares

W2 = {0: 2, 1: -4, 2: 2}
def action(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W2.get(k, 0)
    return tot

def canon_fast(n, rel):
    if not rel: return (n, ())
    up = [[] for _ in range(n)]; dn = [[] for _ in range(n)]
    for a, b in rel: up[a].append(b); dn[b].append(a)
    col = [(len(up[v]), len(dn[v])) for v in range(n)]
    vals = sorted(set(col)); mm = {c: i for i, c in enumerate(vals)}
    col = [mm[c] for c in col]
    for _ in range(n):
        nc = [(col[v], tuple(sorted(col[w] for w in up[v])),
               tuple(sorted(col[w] for w in dn[v]))) for v in range(n)]
        vals = sorted(set(nc)); mm = {c: i for i, c in enumerate(vals)}
        nc = [mm[c] for c in nc]
        if nc == col: break
        col = nc
    classes = {}
    for v in range(n): classes.setdefault(col[v], []).append(v)
    parts = [classes[c] for c in sorted(classes)]
    best = None
    for pp in itertools.product(*[itertools.permutations(c) for c in parts]):
        pos = {}
        i = 0
        for part in pp:
            for v in part: pos[v] = i; i += 1
        r = tuple(sorted((pos[a], pos[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

def downsets_of(m, rel):
    below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
    out = []
    for mask in range(1 << m):
        D = frozenset(i for i in range(m) if mask >> i & 1)
        if all(below[x] <= D for x in D): out.append(D)
    return out

levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 7) for key in sorted(levels[n])]

def components(key):
    m, rel = key
    par = list(range(m))
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for a, b in rel:
        ra, rb = find(a), find(b)
        if ra != rb: par[ra] = rb
    comp = {}
    for v in range(m): comp.setdefault(find(v), []).append(v)
    out = []
    for vs in comp.values():
        vidx = {v: i for i, v in enumerate(sorted(vs))}
        out.append(canon_fast(len(vs), tuple(sorted((vidx[a], vidx[b])
                   for (a, b) in rel if a in vidx and b in vidx))))
    return out

children_orb = {}
for n in range(1, 6):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action(rel, m)
        auts = [p for p in itertools.permutations(range(m))
                if tuple(sorted((p[a], p[b]) for (a, b) in rel))
                == tuple(sorted(rel))]
        seen = set(); kid = {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            orb = frozenset(frozenset(p[d] for d in D) for p in auts)
            if (ck, orb) not in seen:
                seen.add((ck, orb))
                if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
                else: kid[ck] = (1, g)
        children_orb[key] = kid

anc = {}
for key in allkeys:
    m, rel = key
    a = set()
    for D in downsets_of(m, rel):
        if not D or len(D) == m: continue
        di = {d: i for i, d in enumerate(sorted(D))}
        a.add(canon_fast(len(D), tuple(sorted((di[x], di[y])
              for (x, y) in rel if x in D and y in D))))
    anc[key] = a

comp_of = {key: components(key) for key in allkeys}
connected = [key for key in allkeys if len(comp_of[key]) == 1]
phi = np.pi / 3
print(f"connected causets: {len(connected)}; total {len(allkeys)}")

U = set(allkeys)
rng = np.random.default_rng(7)
Afin = None
prev_u = {}
for round_ in range(60):
    conn = [k for k in connected if k in U and k != root]
    ci = {k: i for i, k in enumerate(conn)}
    nvu = len(conn)
    if nvu == 0:
        print("  no variables left -- stopping"); break
    def uval(key, u):
        tot = 0.0
        for c in comp_of[key]:
            if c == root: continue
            tot += u[ci[c]]
        return tot
    eqkeys = [k for k in sorted(U) if nelem(k) <= 5]
    def resid(u):
        out = []
        for key in eqkeys:
            z = -np.exp(uval(key, u))
            for ck, (mu, g) in children_orb[key].items():
                if ck not in U: continue
                z = z + mu * np.exp(uval(ck, u)) * np.exp(1j * g * phi)
            out.append(z.real); out.append(z.imag)
        return np.array(out)
    starts = []
    if prev_u:
        starts.append(np.array([prev_u.get(k, 0.0) for k in conn]))
    starts.append(np.zeros(nvu))
    starts += [rng.normal(0, 0.3, nvu) for _ in range(2)]
    best = None
    for u0 in starts:
        sol = least_squares(resid, u0, method="trf", max_nfev=8000)
        if best is None or sol.cost < best.cost: best = sol
        if np.linalg.norm(resid(sol.x)) < 1e-7: best = sol; break
    r = resid(best.x)
    rn = np.linalg.norm(r)
    if rn >= 1e-6:
        per_eq = np.hypot(r[0::2], r[1::2])
        worst = eqkeys[int(np.argmax(per_eq))]
        if worst[0] <= 3:
            print(f"round {round_}: support {len(U)}, |resid| = {rn:.2e}, "
                  f"worst eq at n={worst[0]} -- refusing amputation, STUCK")
            order = np.argsort(-per_eq)[:6]
            for oi in order:
                k = eqkeys[int(oi)]
                kids = [(ck[0], mu, g) for ck, (mu, g)
                        in children_orb[k].items() if ck in U]
                print(f"    eq resid {per_eq[oi]:.3f} at n={k[0]} "
                      f"rel={k[1]} live-children {kids}")
            per = {}
            for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
            print("    support per level:", per)
            watch = {"V": canon_fast(3, ((0, 1), (0, 2))),
                     "L": canon_fast(3, ((0, 1),)),
                     "3A": canon_fast(3, ()),
                     "broom3": canon_fast(4, ((0, 1), (0, 2), (0, 3))),
                     "diamond": canon_fast(4, ((0, 1), (0, 2), (0, 3),
                                               (1, 3), (2, 3)))}
            print("    watchlist alive:",
                  {nm: (k in U) for nm, k in watch.items()})
            break
        print(f"round {round_}: support {len(U)}, |resid| = {rn:.2e}, "
              f"removing worst-equation causet n={worst[0]} (+cone)")
        U = {key for key in U if key != worst and worst not in anc[key]}
        if root not in U:
            print("  root died"); break
        continue
    prev_u = {k: best.x[ci[k]] for k in conn}
    Avals = {key: np.exp(uval(key, best.x)) for key in U}
    cands = {key for key in U if key != root and Avals[key] < 1e-7}
    if not cands:
        Afin = (best.x, Avals, ci, conn)
        print(f"round {round_}: support {len(U)}, |resid| = {rn:.2e}, "
              "all alive -- DONE")
        break
    # individual pull-up verification: a candidate is dead only if it
    # provably cannot be lifted while keeping the wave equations exact
    forced = set()
    for key in sorted(cands):
        if key not in ci:                      # disconnected: product of
            continue                           # components; handled via them
        j = ci[key]
        def resid_one(u, jj=j):
            base = resid(u)
            pull = max(0.0, -2.0 - u[jj])
            return np.concatenate([base, [0.5 * pull]])
        s1 = least_squares(resid_one, best.x, method="trf", max_nfev=2500)
        if np.linalg.norm(resid(s1.x)) < 1e-6 and s1.x[j] > -12.0:
            continue                           # liftable: not forced
        forced.add(key)
    print(f"round {round_}: support {len(U)}, |resid| = {rn:.2e}, "
          f"candidates {len(cands)}, forced dead {len(forced)}: "
          f"{sorted((k[0], k[1]) for k in forced)}")
    if not forced:
        Avals = {key: np.exp(uval(key, sol2.x)) for key in U}
        Afin = (sol2.x, Avals, ci, conn)
        break
    U = {key for key in U if key not in forced and not (anc[key] & forced)}
    if root not in U:
        print("  root died"); break

if Afin:
    u, Avals, ci, conn = Afin
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    print("=" * 72)
    print("EXACT orbit+cluster support at phi = pi/3:")
    print("  " + "  ".join(f"n={n}: {per.get(n, 0)}/{len(levels[n])}"
                           for n in range(1, 7)))
    # orbit-path counting + unitarity
    Norb = {root: 1}
    for n in range(1, 6):
        for key in sorted(levels[n]):
            if key not in Norb: continue
            for ck, (mu, g) in children_orb[key].items():
                Norb[ck] = Norb.get(ck, 0) + mu * Norb[key]
    print("  orbit-convention unitarity (levels 2-6):")
    for n in range(2, 7):
        tot = sum(Norb.get(key, 0) * Avals.get(key, 0.0)
                  * np.exp(1j * (action(key[1], key[0]) - 1) * phi)
                  for key in levels[n] if key in U)
        print(f"    level {n}: |sum - 1| = {abs(tot - 1):.2e}")
    # small-causet amplitude table (exact-form hunting)
    print("  amplitudes on connected causets n <= 4:")
    for key in sorted(k for k in U if k in set(connected) and nelem(k) <= 4):
        print(f"    n={key[0]} rel={key[1]}: A = {Avals[key]:.6f}")
    # geometry classes at n = 5: which connected causets live
    alive5 = [k for k in U if nelem(k) == 5 and len(comp_of[k]) == 1]
    dead5 = [k for k in levels[5] if k not in U and
             len(comp_of[k]) == 1]
    print(f"  connected n=5: alive {len(alive5)}, dead {len(dead5)}")
    diamond = canon_fast(4, ((0, 1), (0, 2), (0, 3), (1, 3), (2, 3)))
    ch3 = canon_fast(3, ((0, 1), (0, 2), (1, 2)))
    print(f"  diamond alive: {diamond in U};  3-chain alive: {ch3 in U}")
    # dimension of the residual freedom at the solution
    eps = 1e-6
    def resid_final(uv):
        out = []
        for key in sorted(U):
            if nelem(key) > 5: continue
            z = -np.exp(uval(key, uv))
            for ck, (mu, g) in children_orb[key].items():
                if ck not in U: continue
                z = z + mu * np.exp(uval(ck, uv)) * np.exp(1j * g * phi)
            out.append(z.real); out.append(z.imag)
        return np.array(out)
    r0 = resid_final(u)
    J = np.zeros((len(r0), len(u)))
    for j in range(len(u)):
        du = u.copy(); du[j] += eps
        J[:, j] = (resid_final(du) - r0) / eps
    rk = np.linalg.matrix_rank(J, tol=1e-6)
    bulk_cols = [ci[k] for k in conn if nelem(k) <= 5]
    rk_bulk = np.linalg.matrix_rank(J[:, bulk_cols], tol=1e-6)
    print(f"  freedom: {len(u)} connected vars, rank {rk} -> dim {len(u) - rk}")
    print(f"  bulk (n<=5) vars {len(bulk_cols)}, rank {rk_bulk} -> "
          f"bulk dim {len(bulk_cols) - rk_bulk}")

# ===== EXACT LINEAR TREATMENT (pins make the system linear) =================
print()
print("=" * 72)
print("EXACT LINEAR: pins A(2ch)=A(V)=A(L)=1, A(3ch)=A(Lambda)=0 =>")
print("all cluster products are linear; LP + exact removal loop:")
from scipy.optimize import linprog
k2ch = canon_fast(2, ((0, 1),))
kV = canon_fast(3, ((0, 1), (0, 2)))
k3ch = canon_fast(3, ((0, 1), (0, 2), (1, 2)))
kLam = canon_fast(3, ((0, 2), (1, 2)))
pinned1 = {root, k2ch, kV}          # connected value 1
pinned0 = {k3ch, kLam}              # dead
U = {key for key in allkeys
     if not (anc[key] & pinned0) and key not in pinned0}
def valexpr(key, ci):
    """A(key) as (const, {var: coeff}) -- linear via cluster + pins."""
    const = 1.0
    terms = {}
    for c in comp_of[key]:
        if c == root or c in pinned1: continue
        if c in pinned0: return (0.0, {})
        if c in ci: terms[c] = terms.get(c, 0) + 1
        else: return (0.0, {})       # dead/removed component
    if len(terms) == 0: return (const, {})
    if len(terms) == 1 and list(terms.values())[0] == 1:
        return (0.0, {list(terms.keys())[0]: 1.0})
    return None                       # genuinely nonlinear (shouldn't occur)
for round_ in range(60):
    conn_vars = [k for k in connected if k in U
                 and k not in pinned1 and k != root and nelem(k) >= 4]
    ci = set(conn_vars)
    vidx = {k: i for i, k in enumerate(conn_vars)}
    nvu = len(conn_vars)
    A_eq, b_eq = [], []
    bad = False
    for key in sorted(U):
        if nelem(key) > 5: continue
        rr = np.zeros(nvu); ri = np.zeros(nvu)
        cr, cim = 0.0, 0.0
        ex = valexpr(key, ci)
        if ex is None: bad = True; break
        c0, t0 = ex
        cr -= c0
        for vk, cf in t0.items(): rr[vidx[vk]] -= cf
        for ck, (mu, g) in children_orb[key].items():
            if ck not in U: continue
            exc = valexpr(ck, ci)
            if exc is None: bad = True; break
            c1, t1 = exc
            z = mu * np.exp(1j * g * phi)
            cr += c1 * z.real; cim += c1 * z.imag
            for vk, cf in t1.items():
                rr[vidx[vk]] += cf * z.real
                ri[vidx[vk]] += cf * z.imag
        if bad: break
        A_eq.append(rr); b_eq.append(-cr)
        A_eq.append(ri); b_eq.append(-cim)
    if bad:
        print("  nonlinear term encountered -- abort"); break
    A_eq = np.array(A_eq); b_eq = np.array(b_eq)
    res = linprog(np.zeros(nvu), A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, 1000)] * nvu, method="highs")
    if not res.success:
        print(f"  round {round_}: support {len(U)} INFEASIBLE -- "
              "orbit+cluster has NO valid support at pi/3")
        U = set(); break
    x = res.x
    dead = set()
    for k in conn_vars:
        if x[vidx[k]] > 1e-9: continue
        c2 = np.zeros(nvu); c2[vidx[k]] = -1.0
        r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                     method="highs")
        if (not r2.success) or -r2.fun < 1e-9: dead.add(k)
    print(f"  round {round_}: support {len(U)}, vars {nvu}, "
          f"feasible; forced dead {len(dead)}")
    if not dead:
        rank = np.linalg.matrix_rank(A_eq)
        per = {}
        for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
        print("  FINAL support:", "  ".join(
            f"n={n}: {per.get(n, 0)}/{len(levels[n])}" for n in range(1, 7)))
        print(f"  freedom: {nvu} vars, rank {rank} -> dim {nvu - rank}")
        diamond = canon_fast(4, ((0, 1), (0, 2), (0, 3), (1, 3), (2, 3)))
        broom3 = canon_fast(4, ((0, 1), (0, 2), (0, 3)))
        print(f"  diamond alive: {diamond in U}; broom-3 alive: "
              f"{broom3 in U}")
        # a witness with maximal spread + unitarity check
        cobj = -np.ones(nvu)
        rw = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 10)] * nvu,
                     method="highs")
        Aval = {}
        for key in U:
            ex = valexpr(key, ci)
            c0, t0 = ex
            Aval[key] = c0 + sum(cf * rw.x[vidx[vk]]
                                 for vk, cf in t0.items())
        Norb = {root: 1}
        for n in range(1, 6):
            for key in sorted(levels[n]):
                if key not in Norb: continue
                for ck, (mu, g) in children_orb[key].items():
                    Norb[ck] = Norb.get(ck, 0) + mu * Norb[key]
        for n in range(2, 7):
            tot = sum(Norb.get(key, 0) * Aval.get(key, 0.0)
                      * np.exp(1j * (action(key[1], key[0]) - 1) * phi)
                      for key in levels[n] if key in U)
            print(f"    orbit-unitarity level {n}: |sum - 1| = "
                  f"{abs(tot - 1):.2e}")
        print("  connected amplitudes n=4 (witness):")
        for k in sorted(conn_vars):
            if nelem(k) == 4:
                print(f"    rel={k[1]}: A = {rw.x[vidx[k]]:.4f}")
        break
    U = {key for key in U if key not in dead and not (anc[key] & dead)}
