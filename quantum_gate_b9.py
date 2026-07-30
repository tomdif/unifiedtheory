#!/usr/bin/env python3
"""THE QUANTUM COVARIANCE GATE at the b = 9 windows (era 2, depth r <= 4).

Pre-registered form (constraint version): does there exist a complex-RS
(Surya-Zalel covariant, Bell-causal) amplitude dynamics whose transition
amplitudes carry the ansatz phases,

    a(C -> C') = rho * e^{i g phi},   rho >= 0,  g = BD gap,  phi = 2pi k/9 ?

Structure used:
  * Per-node sum rule  sum_c a_c = 1  is the RS binomial identity --
    automatic for ANY complex couplings.  The path phase telescopes to the
    endpoint action => amplitude path-independence (quantum covariance of
    the amplitude) holds by construction.
  * Era 1 must end at stage 1 (the root argument survives verbatim: with
    finite couplings arg(1/(1+t1)) = phi is unsolvable) => era 2, seed = a
    single minimum, relative causets = ALL finite posets.
  * The BD gap of a birth depends ONLY on the precursor poset P = {x0} u D
    (between-counts live inside the past) -- verified mechanically below.
  * Era-2 gregarious gap = 0 (minimal-cover theorem) => all reachable
    denominators D_r = sum C(r,j) s_j must be real positive => every
    constraint is:  arg lambda(sig) == (g mod 9) * phi,  per SIGNATURE.
  * Same signature, different gap mod 9, both reachable => that lambda
    must VANISH (interference closure -- unavailable classically).
    Reachability depends on which lambdas vanish => fixed-point search
    over zero-patterns of the 10 signatures (varpi <= 4).

For each window k in {1,2,3,4} (5..8 conjugate; 3,6 are the b=3 windows)
and each zero-pattern: compute reachable relative causets (r <= 4), gather
live constraints (transitions from reachable nodes with nonvanishing
lambda), reject on collision, then solve the LINEAR feasibility problem
for s in C^4 (phase equalities + positivity + real-positive denominators).
Report all feasible dynamics, their interference content (reachable nodes
with >= 2 live children at distinct relative phases), and their reachable
geometry.  For the maximal surviving dynamics, build the depth-3
decoherence functional on unlabeled 3-stems: decoherence + diagonal = the
pre-registered diag(D)-vs-cos^2 probe.
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

def adjoin_min(rel, n):
    """absolute causet: new minimum below all of 0..n-1 (shift labels +1)."""
    r = {(a + 1, b + 1) for (a, b) in rel} | {(0, i + 1) for i in range(n)}
    return tuple(sorted(r)), n + 1

def birth(rel, n, D):
    return tuple(sorted(set(rel) | {(d, n) for d in D})), n + 1

# ---- relative posets to size 4, and their transitions ----------------------
rel_levels = {0: {canon(0, ()): (0, ())}}
for r in range(0, 4):
    nxt = {}
    for key, (m, rel) in rel_levels[r].items():
        for D in downsets(m, rel):
            nr, nn = birth(rel, m, D)
            nxt[canon(nn, nr)] = (nn, nr)
    rel_levels[r + 1] = nxt
print("relative posets per size:", {r: len(v) for r, v in rel_levels.items()})

# ---- precursor-poset gap table + host-independence check -------------------
gap_of_P = {}          # canon(P_rel) -> gap
sig_of_P = {}
host_ok = True
for r in range(0, 5):
    for key, (m, rel) in rel_levels[r].items():
        arel, an = adjoin_min(rel, m)
        S_host = action_units(arel, an)
        for D in downsets(m, rel):
            # child: absolute birth above D u {x0}
            crel, cn = birth(arel, an, {0} | {d + 1 for d in D})
            g = action_units(crel, cn) - S_host
            idx = {d: i for i, d in enumerate(sorted(D))}
            Dp = canon(len(D), tuple(sorted((idx[a], idx[b]) for (a, b) in rel
                                            if a in D and b in D)))
            sig = (len(D), len(maximals(rel, D)))
            if Dp in gap_of_P and gap_of_P[Dp] != g: host_ok = False
            gap_of_P[Dp] = g
            sig_of_P[Dp] = sig
print("gap depends only on precursor poset:", host_ok)
print("precursor table (|D|, m) : P -> gap (gap mod 9):")
by_sig = {}
for Dp, g in sorted(gap_of_P.items()):
    s = sig_of_P[Dp]
    by_sig.setdefault(s, []).append((Dp, g))
for s in sorted(by_sig):
    if s[0] == 0 or s[0] > 4: continue
    entries = ", ".join(f"g={g} ({g % 9})" for _, g in by_sig[s])
    gaps9 = sorted({g % 9 for _, g in by_sig[s]})
    tag = "COLLISION" if len(gaps9) > 1 else "coherent"
    print(f"  sig {s}: {entries}   -> classes mod 9: {gaps9}  [{tag}]")

# ---- signatures and lambda coefficient vectors -----------------------------
SIGS = [(v, m) for v in range(1, 5) for m in range(1, v + 1)]
def lam_coeff(v, m):
    c = np.zeros(5)
    for j in range(m, v + 1):
        c[j] = math.comb(v - m, j - m)
    return c            # coefficients of (s0=1, s1..s4); s0 coeff always 0 here
LAM = {s: lam_coeff(*s) for s in SIGS}
DEN = {r: np.array([math.comb(r, j) if j <= r else 0 for j in range(5)],
                   dtype=float) for r in range(5)}

# transitions[(r_size, key)] = list of (signature, gap mod 9, Dp)
transitions = {}
for r in range(0, 5):
    for key, (m, rel) in rel_levels[r].items():
        tr = []
        for D in downsets(m, rel):
            idx = {d: i for i, d in enumerate(sorted(D))}
            Dp = canon(len(D), tuple(sorted((idx[a], idx[b]) for (a, b) in rel
                                            if a in D and b in D)))
            sig = (len(D), len(maximals(rel, D))) if D else (0, 0)
            tr.append((sig, gap_of_P[Dp] % 9, Dp, D))
        transitions[(r, key)] = (m, rel, tr)

# ---- the gate per window and zero-pattern ----------------------------------
def solve_pattern(k, zero):
    """zero: set of signatures forced to lambda = 0.  Returns dict or None."""
    phi = 2 * np.pi * k / 9
    # reachability over relative causets r <= 4
    reach = {(0, canon(0, ()))}
    frontier = [(0, canon(0, ()))]
    while frontier:
        r, key = frontier.pop()
        if r >= 4: continue
        m, rel, tr = transitions[(r, key)]
        for sig, g9, Dp, D in tr:
            if sig != (0, 0) and sig in zero: continue
            nr, nn = birth(rel, m, D)
            ck = canon(nn, nr)
            if (nn, ck) not in reach:
                reach.add((nn, ck)); frontier.append((nn, ck))
    # live constraints: per signature, set of required classes mod 9
    req = {}
    live_nodes = []
    for (r, key) in reach:
        m, rel, tr = transitions[(r, key)]
        live = [(sig, g9) for sig, g9, Dp, D in tr
                if sig == (0, 0) or sig not in zero]
        live_nodes.append(((r, key), live))
        for sig, g9 in live:
            if sig == (0, 0):
                if g9 != 0: return None
                continue
            req.setdefault(sig, set()).add(g9)
    for sig, classes in req.items():
        if len(classes) > 1: return None          # collision
    # linear feasibility: s1..s4 complex -> x in R^8
    A_eq, b_eq, A_ub, b_ub = [], [], [], []
    EPS = 1e-3
    def row_from(cvec, phase):                    # Re/Im of e^{-i phase} lam
        rr = np.zeros(8); ri = np.zeros(8)
        for j in range(1, 5):
            c = cvec[j] * np.exp(-1j * phase)
            rr[2*(j-1)] += c.real; rr[2*(j-1)+1] += -c.imag
            ri[2*(j-1)] += c.imag; ri[2*(j-1)+1] += c.real
        const = 0.0 + 0.0j                        # s0 coeff is 0 in LAM
        return rr, ri, const
    for sig in SIGS:
        cvec = LAM[sig]
        if sig in zero:
            rr, ri, _ = row_from(cvec, 0.0)
            A_eq += [rr, ri]; b_eq += [0.0, 0.0]
        elif sig in req:
            tau = (2 * np.pi * ((req[sig].pop() if False else
                                 next(iter(req[sig]))) * k % 9) / 9)
            rr, ri, _ = row_from(cvec, tau)
            A_eq.append(ri); b_eq.append(0.0)
            A_ub.append(-rr); b_ub.append(-EPS)   # Re >= EPS
    for r in range(1, 5):
        if not any(rr == r for (rr, kk) in reach): continue
        cvec = DEN[r]
        rr_, ri_, _ = row_from(cvec, 0.0)
        A_eq.append(ri_); b_eq.append(0.0)
        A_ub.append(-rr_); b_ub.append(cvec[0] - EPS)  # Re(1 + sum) >= eps
    res = linprog(np.zeros(8), A_ub=np.array(A_ub) if A_ub else None,
                  b_ub=np.array(b_ub) if b_ub else None,
                  A_eq=np.array(A_eq) if A_eq else None,
                  b_eq=np.array(b_eq) if b_eq else None,
                  bounds=[(-50, 50)] * 8, method="highs")
    if not res.success: return None
    s = np.array([1] + [res.x[2*i] + 1j * res.x[2*i+1] for i in range(4)])
    # interference census: reachable nodes with >= 2 live child classes at
    # distinct phases
    inode = 0; distinct_geom = set()
    for (rk, live) in live_nodes:
        classes = {g9 for sig, g9 in live}
        if len(classes) >= 2: inode += 1
        distinct_geom.add(rk)
    return {"s": s, "reach": len(reach), "inodes": inode,
            "zero": zero, "livesigs": [s_ for s_ in SIGS if s_ not in zero
                                       and s_ in req]}

print("=" * 72)
results = {}
for k in (1, 2, 3, 4):
    feas = []
    for nz in range(len(SIGS) + 1):
        for zero in itertools.combinations(SIGS, nz):
            r = solve_pattern(k, set(zero))
            if r: feas.append(r)
    # rank by interference content then by live signature count
    feas.sort(key=lambda d: (-len(d["livesigs"]), -d["inodes"]))
    results[k] = feas
    if feas:
        best = feas[0]
        print(f"k={k}: feasible patterns {len(feas)}; MAXIMAL dynamics: "
              f"live sigs {best['livesigs']}, zeroed {sorted(best['zero']) if best['zero'] else 'none'},")
        print(f"       reachable rel-causets {best['reach']}/23, "
              f"superposition nodes {best['inodes']}, "
              f"s = {np.array2string(best['s'][1:], precision=3)}")
    else:
        print(f"k={k}: NO feasible dynamics at any zero-pattern -- window dead")

# ---- decoherence probe on 3-stems for the best surviving dynamics ----------
print("=" * 72)
for k in (1, 2, 3, 4):
    if not results[k]: continue
    best = results[k][0]
    if not best["livesigs"]:
        print(f"k={k}: only the all-zero (quantum broom) dynamics -- "
              "single path, trivial D."); continue
    phi = 2 * np.pi * k / 9
    s = best["s"]
    def amp(r, m, rel, D):
        sig = (len(D), len(maximals(rel, D))) if D else (0, 0)
        if sig != (0, 0) and sig in best["zero"]: return 0j
        lam = 1.0 if sig == (0, 0) else complex(LAM[sig] @ s)
        den = complex(DEN[r] @ s)
        idx = {d: i for i, d in enumerate(sorted(D))}
        Dp = canon(len(D), tuple(sorted((idx[a], idx[b]) for (a, b) in rel
                                        if a in D and b in D)))
        return (lam / den) * 0 + (lam / den)  # phase check done via gap:
    # build all labeled 3-step paths, amplitude = product of a(transition)
    paths = {}
    def walk(r, m, rel, A):
        if r == 3:
            paths.setdefault(canon(m, rel), []).append(A); return
        for D in downsets(m, rel):
            a = amp(r, m, rel, D)
            if a == 0: continue
            nr, nn = birth(rel, m, D)
            walk(r + 1, nn, nr, A * a)
    walk(0, 0, (), 1.0 + 0j)
    stems = sorted(paths)
    Amp = {c: sum(paths[c]) for c in stems}
    Dmat = np.array([[Amp[c] * np.conj(Amp[d]) for d in stems] for c in stems])
    diag = np.real(np.diag(Dmat))
    off = np.max(np.abs(Dmat - np.diag(np.diag(Dmat)))) if len(stems) > 1 else 0
    print(f"k={k}: 3-stems reachable: {len(stems)}; diag(D) = "
          f"{np.array2string(diag, precision=4)}; sum = {diag.sum():.4f}; "
          f"max |off-diag| = {off:.4f}")
    print(f"       (sum diag = 1 <=> decoherent; off-diag = interference "
          "between distinct 3-geometries)")
