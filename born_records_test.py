#!/usr/bin/env python3
"""Completion attempt #3, first records test: Born-shell bi-normalized law.

Registered program (SUM_RULE_MOD.md verdict + BORN_NORMALIZATION_TRANSFER_
AUDIT.md open item 3): the records test (records-churn-2026-08-03) was run
only on the coherent sum(a)=1 law, whose churn was measured to be ~86%
normalization flow.  The bi-normalized intersection (sum a = 1 AND
sum |a|^2 = 1 per parent, realized canonically by the support-relative
radial Born-shell completion) kills normalization flow at the cylinder
level BY THEOREM.  Never tested: do STEM-RECORD measures stabilize?

Design:
  Stage 0  engine: unlabeled causet growth tree n<=7 (counts 1,2,5,16,63,
           318,2045), children with multiplicity mu and action gap g
           (2D BD weights W2={0:2,1:-4,2:2}), phase phi=0.9.
  Stage 1  BASELINE REPLICATION: solve wave-family LP members (maxmin +
           deep), covariant final-class measure mu_T(E)=sum_{C in E}
           |A(C)|^2 N(C)^2, stems s0..s10 = 5 n=3 causets + first 6 n=4
           causets in canonical sort order, horizons T=4..7.
           Certification gate: reproduce stem_measures.log table
           (s3: .9452 .9634 .9411 .5482 etc.) and X(maxmin)=3.0367,
           X(deep)=1.2203 (completion_p4_test.log).
  Stage 2  Born-shell completion of the SAME member: per parent p with
           K labeled children and relative labeled child amplitudes
           a_c = e^{i g phi} A_c / A_p (sum_labeled a = 1 exact),
           u = 1/K, v = a - u, r = sqrt((1-1/K)/sum_labeled |v|^2),
           b = u + r v  (unique nonneg radial least-disturbance point;
           obstructed iff v=0 with K>=2 -- counted and reported).
  Stage 3  New-law measures by tree DP (b depends only on parent/child
           classes): Psi(C) = sum_p Psi(p) mu b   (coherent),
           W(C) = sum_p W(p) mu |b|^2             (Born diagonal),
           Q_T(E) = sum_{C in E}|Psi|^2 / Omega,  P_T(E) = sum W / Omega,
           M_lambda = ((1-l)Q + l P) normalized,  l in {0,.25,.5,.75,1}.
  Stage 4  Verdict metrics per measure: stems table T=4..7, and churn
           split X = X_minus + X_plus over T=5..7 where
             X_minus = sum_stems sum_T max(0, s_T - s_{T+1})   [facts
                       UN-HAPPENING = Kolmogorov inconsistency; must be
                       ~0 for P by the martingale theorem]
             X_plus  = sum_stems sum_T max(0, s_{T+1} - s_T)   [monotone
                       accretion = learning, NOT inconsistency]
           Also: P_T(Omega) drift (theorem check, must be 1), coherent
           interference retention |Q-P| on stems, past-sector purity.

Pre-registered readings (BORN_RECORDS_TEST.md, filed before Stage 2 ran):
  (i)   X_minus(P) ~ 0 and X_minus(Q) < 0.2 (the measured coherence share
        of the old churn): facts stabilize in the bi-normalized theory.
  (ii)  X_minus(Q) >= 0.2: coherent sector still un-makes facts; facts
        live only on the fully dephased (lambda=1) record algebra.
  (iii) Born-shell obstruction on >5% of support-parents: intersection
        thin on the physical tree; completion ill-defined as stated.
"""
import itertools, math, sys, time
import numpy as np
from scipy.optimize import linprog

T0 = time.time()
def log(*a):
    print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

PHI = 0.90
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7

# ---------------- Stage 0: engine (as in continuum_select_2d.py) ----------
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
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
counts = {n: len(v) for n, v in levels.items()}
log("levels:", counts)
assert [counts[i] for i in range(1, NMAX + 1)] == \
    [1, 2, 5, 16, 63, 318, 2045, 16999][:NMAX]
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]

children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action(rel, m)
        kid = {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kid:
                assert kid[ck][1] == g
                kid[ck] = (kid[ck][0] + 1, g)
            else: kid[ck] = (1, g)
        children[key] = kid

# labeled path counts N(C)
Npaths = {root: 1.0}
for key in allkeys:
    if key == root: continue
    Npaths[key] = 0.0
for key in allkeys:
    for ck, (mu, g) in children.get(key, {}).items():
        Npaths[ck] += Npaths[key] * mu

# ---------------- stems ----------------------------------------------------
stems3 = sorted(levels[3])
stems4 = sorted(levels[4])
STEMS = stems3 + stems4[:6]          # the 11 of the records test
ALLSTEMS = stems3 + stems4           # full width, reported too

def contains_stem(key, stem):
    m, rel = key
    sm, srel = stem
    for D in downsets_of(m, rel):
        if len(D) != sm: continue
        di = {d: i for i, d in enumerate(sorted(D))}
        sub = canon_fast(sm, tuple(sorted((di[x], di[y])
              for (x, y) in rel if x in D and y in D)))
        if sub == stem: return True
    return False

log("computing stem containment tables...")
CONT = {}   # (stem, key) -> bool for keys at levels 4..NMAX
for s in ALLSTEMS:
    for T in range(4, NMAX + 1):
        for key in levels[T]:
            CONT[(s, key)] = contains_stem(key, s)
log("containment done")

# stage-4 action sectors (the purity corollary's classes)
S4 = {k: action(levels[4][k][1], 4) for k in levels[4]}
SECVALS = sorted(set(S4.values()))
NSEC = len(SECVALS)
SECIDX = {k: SECVALS.index(S4[k]) for k in levels[4]}
log(f"stage-4 action sectors: {NSEC} values {SECVALS}")

def sector_dp(base, edgew, dtype=float):
    """base[k] scalar at level 4; edgew(p,ck,mu,g) per-class step weight.
       returns vsec[key] = np.array(NSEC) for keys at levels 4..NMAX."""
    vsec = {}
    for k in levels[4]:
        v = np.zeros(NSEC, dtype=dtype)
        v[SECIDX[k]] = base.get(k, 0.0)
        vsec[k] = v
    for T in range(4, NMAX):
        for p in levels[T]:
            vp = vsec.get(p)
            if vp is None: continue
            for ck, (mu, g) in children.get(p, {}).items():
                w = edgew(p, ck, mu, g)
                if w == 0: continue
                if ck not in vsec:
                    vsec[ck] = np.zeros(NSEC, dtype=dtype)
                vsec[ck] = vsec[ck] + vp * w
    return vsec

def purity_report(vsec, meas, label, square=False):
    """<max_i p_i>, p_i prop to vsec_i (or |vsec_i|^2 if square),
       weighted by per-level-normalized meas."""
    out = []
    for T in range(4, NMAX + 1):
        omega = sum(meas[k] for k in levels[T])
        acc = 0.0
        for k in levels[T]:
            if meas[k] <= 0: continue
            v = vsec.get(k)
            if v is None:
                acc += meas[k]; continue
            p = np.abs(v) ** 2 if square else np.abs(v)
            tot = p.sum()
            acc += meas[k] * ((p.max() / tot) if tot > 0 else 1.0)
        out.append(acc / omega)
    log(f"  purity[{label}] T=4..{NMAX}: "
        + "  ".join(f"{x:.4f}" for x in out))

def sector_invariance(vsec, label):
    for T in range(4, NMAX + 1):
        m = np.zeros(NSEC)
        for k in levels[T]:
            if k in vsec: m += np.abs(vsec[k])
        log(f"  sector mass[{label}] T={T}: "
            + " ".join(f"{x:.6f}" for x in m))

# ---------------- Stage 1: members ----------------------------------------
kk = allkeys; ii = {k: i for i, k in enumerate(kk)}
nv = len(kk)
A_eq, b_eq = [], []
r0 = np.zeros(nv); r0[ii[root]] = 1
A_eq.append(r0); b_eq.append(1.0)
for key in kk:
    if nelem(key) >= NMAX: continue
    rr = np.zeros(nv); ri = np.zeros(nv)
    rr[ii[key]] -= 1
    for ck, (mu, g) in children[key].items():
        z = mu * np.exp(1j * g * PHI)
        rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
    A_eq.append(rr); b_eq.append(0.0)
    A_eq.append(ri); b_eq.append(0.0)
A_eq = np.array(A_eq); b_eq = np.array(b_eq)

def solve_member(kind):
    if kind == "deep":
        c = np.zeros(nv)
        for key in kk:
            if nelem(key) >= 5: c[ii[key]] = -1.0
        res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nv,
                      method="highs")
        assert res.success, res.message
        return res.x
    if kind == "maxmin":
        # maximize t s.t. A_k >= t for all k (one extra variable)
        c = np.zeros(nv + 1); c[nv] = -1.0
        Ae = np.hstack([A_eq, np.zeros((A_eq.shape[0], 1))])
        Aub = np.hstack([-np.eye(nv), np.ones((nv, 1))])
        bub = np.zeros(nv)
        res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Ae, b_eq=b_eq,
                      bounds=[(0, 1000)] * nv + [(0, None)],
                      method="highs")
        assert res.success, res.message
        log(f"  maxmin t* = {res.x[nv]:.6g}")
        return res.x[:nv]
    raise ValueError(kind)

log("solving members...")
MEMBERS = {}
for kind in ("maxmin", "deep"):
    MEMBERS[kind] = solve_member(kind)
    log(f"  {kind}: support "
        f"{sum(1 for k in kk if MEMBERS[kind][ii[k]] > 1e-9)}/{nv}")

def stems_table(meas, label, stems=STEMS):
    """meas: dict key->nonneg weight per causet, unnormalized, per level.
       returns {stem: [s_T for T=4..NMAX]} using per-level Omega norm."""
    out = {}
    for T in range(4, NMAX + 1):
        omega = sum(meas[k] for k in levels[T])
        for s in stems:
            num = sum(meas[k] for k in levels[T] if CONT[(s, k)])
            out.setdefault(s, []).append(num / omega if omega > 0 else float("nan"))
    return out

def churn(table, stems=STEMS):
    """X, X_minus, X_plus over horizon steps 5->6->7 (indices 1,2,3)."""
    X = Xm = Xp = 0.0
    for s in stems:
        v = table[s]
        for j in range(1, len(v) - 1):
            d = v[j + 1] - v[j]
            X += abs(d)
            if d < 0: Xm += -d
            else: Xp += d
    return X, Xm, Xp

def print_table(table, label, stems=STEMS):
    log(f"--- stems under {label} (T=4..{NMAX}) ---")
    names = {}
    for i, s in enumerate(stems3): names[s] = f"s{i}(n=3)"
    for i, s in enumerate(stems4): names[s] = f"s{i+5}(n=4)"
    for s in stems:
        vals = "  ".join(f"{x:.4f}" for x in table[s])
        log(f"  {names.get(s,'?'):10s} {vals}")
    X, Xm, Xp = churn(table, stems)
    log(f"  X = {X:.4f}   X_minus = {Xm:.4f}   X_plus = {Xp:.4f}")
    return X, Xm, Xp

# old covariant final-class measure: |A(C)|^2 N(C)^2
log("=== STAGE 1: baseline replication (old law) ===")
BASE = {}
for kind in ("maxmin", "deep"):
    A = MEMBERS[kind]
    meas = {k: (A[ii[k]] ** 2) * (Npaths[k] ** 2) for k in kk}
    tab = stems_table(meas, kind)
    log(f"[baseline {kind}]")
    BASE[kind] = print_table(tab, f"old law, {kind} member")
    # purity corollary (old law): p_i(C) prop N_i(C)^2, weight |A|^2 N^2
    Nsec = sector_dp({k: Npaths[k] for k in levels[4]},
                     lambda p, ck, mu, g: mu)
    purity_report(Nsec, meas, f"old,{kind}", square=True)

log("certification targets: maxmin X=3.0367 (stem_measures.log), "
    "deep X=1.2203 (completion_p4_test.log)")

# ---------------- Stage 2: Born-shell completion ---------------------------
def born_shell(member, tol=1e-12, minAp=1e-7):
    """per-parent labeled relative amplitudes -> radial Born completion.
       returns b[(p,c)] complex per labeled child (equal within class),
       plus diagnostics."""
    A = member
    b = {}
    obstructed = []
    skipped = 0
    bad_markov = 0
    rlist = []
    for p in kk:
        if nelem(p) >= NMAX or p not in children: continue
        Ap = A[ii[p]]
        if Ap <= minAp:
            skipped += 1
            continue
        # labeled children: class ck repeated mu times, amplitude
        # a = e^{i g phi} A_c / A_p each
        classes = list(children[p].items())
        K = sum(mu for _, (mu, g) in classes)
        a = {ck: np.exp(1j * g * PHI) * A[ii[ck]] / Ap
             for ck, (mu, g) in classes}
        ssum = sum(mu * a[ck] for ck, (mu, g) in classes)
        if abs(ssum - 1) > 1e-5:
            bad_markov += 1
        u = 1.0 / K
        v = {ck: a[ck] - u for ck in a}
        s2 = sum(mu * abs(v[ck]) ** 2 for ck, (mu, g) in classes)
        if s2 < tol:
            if K >= 2:
                obstructed.append(p)
                # keep coherent amplitudes (no completion exists)
                for ck in a: b[(p, ck)] = a[ck]
            else:
                for ck in a: b[(p, ck)] = a[ck]  # K=1: already bi-normalized
            continue
        r = math.sqrt((1.0 - 1.0 / K) / s2)
        rlist.append(r)
        for ck in a:
            b[(p, ck)] = u + r * v[ck]
        # exactness checks
        cs = sum(mu * b[(p, ck)] for ck, (mu, g) in classes)
        bs = sum(mu * abs(b[(p, ck)]) ** 2 for ck, (mu, g) in classes)
        assert abs(cs - 1) < 1e-6 and abs(bs - 1) < 1e-6, (p, cs, bs)
    if bad_markov:
        log(f"  WARNING: {bad_markov} parents with Markov residual > 1e-5")
    if rlist:
        rl = sorted(rlist)
        log(f"  Born-shell disturbance r (r=1 <=> member already "
        	f"bi-normalized at that parent):")
        log(f"    min {rl[0]:.4f}  q25 {rl[len(rl)//4]:.4f}  "
            f"median {rl[len(rl)//2]:.4f}  q75 {rl[3*len(rl)//4]:.4f}  "
            f"max {rl[-1]:.4f}")
    return b, obstructed, skipped

# ---------------- Stage 3: DP + measures -----------------------------------
def new_law_tables(member, label):
    b, obstructed, skipped = born_shell(member)
    npar = sum(1 for p in kk if nelem(p) < NMAX and member[ii[p]] > 1e-12)
    log(f"[{label}] Born-shell: {npar} support parents, "
        f"{len(obstructed)} obstructed (uniform), {skipped} off-support")
    # DP
    Psi = {root: 1.0 + 0j}
    W = {root: 1.0}
    for key in kk:
        if key == root: continue
        Psi[key] = 0.0 + 0j; W[key] = 0.0
    for p in kk:
        for ck, (mu, g) in children.get(p, {}).items():
            if (p, ck) not in b: continue
            Psi[ck] += Psi[p] * mu * b[(p, ck)]
            W[ck] += W[p] * mu * abs(b[(p, ck)]) ** 2
    # theorem check: P(Omega)=1 per level
    for T in range(1, NMAX + 1):
        tot = sum(W[k] for k in levels[T])
        log(f"  P(Omega) at T={T}: {tot:.12f}   "
            f"Q_classid(Omega)={sum(abs(Psi[k])**2 for k in levels[T]):.6f}")
    Qm = {k: abs(Psi[k]) ** 2 for k in kk}
    Pm = {k: W[k] for k in kk}
    # sector records: exact horizon-invariance of past-sector mass under P
    Wsec = sector_dp({k: W[k] for k in levels[4]},
                     lambda p, ck, mu, g:
                     mu * abs(b[(p, ck)]) ** 2 if (p, ck) in b else 0.0)
    sector_invariance(Wsec, f"P,{label}")
    purity_report(Wsec, Pm, f"P,{label}")
    Psisec = sector_dp({k: Psi[k] for k in levels[4]},
                       lambda p, ck, mu, g:
                       mu * b[(p, ck)] if (p, ck) in b else 0.0,
                       dtype=complex)
    purity_report(Psisec, Qm, f"Q,{label}", square=True)
    return Qm, Pm, len(obstructed), npar

log("=== STAGE 2+3: bi-normalized law (Born-shell completion) ===")
RESULTS = {}
for kind in ("maxmin", "deep"):
    Qm, Pm, nobs, npar = new_law_tables(MEMBERS[kind], kind)
    tabQ = stems_table(Qm, kind)
    tabP = stems_table(Pm, kind)
    log(f"[{kind}-completed] COHERENT Q (final-class identified):")
    rQ = print_table(tabQ, f"Q, {kind}-completed")
    log(f"[{kind}-completed] BORN DIAGONAL P (the martingale):")
    rP = print_table(tabP, f"P, {kind}-completed")
    # M_lambda: normalized convex combination of *normalized* Q,P per level
    for lam in (0.25, 0.5, 0.75):
        tabM = {}
        for s in tabQ:
            tabM[s] = [(1 - lam) * q + lam * p
                       for q, p in zip(tabQ[s], tabP[s])]
        # note: Q,P already Omega-normalized per level, and M_lambda of
        # normalized measures is normalized: this matches the audit's
        # measure-level interpolation up to the class identification.
        X, Xm, Xp = churn(tabM)
        log(f"  M_lambda={lam}: X = {X:.4f}  X_minus = {Xm:.4f}  "
            f"X_plus = {Xp:.4f}")
    # interference retention on stems: max |Q-P| entry
    dmax = max(abs(q - p) for s in tabQ
               for q, p in zip(tabQ[s], tabP[s]))
    log(f"  interference on stems: max|Q-P| = {dmax:.4f}")
    RESULTS[kind] = dict(baseline=BASE[kind], Q=rQ, P=rP,
                         obstructed=nobs, parents=npar, dmax=dmax)

log("=== SUMMARY ===")
for kind in ("maxmin", "deep"):
    R = RESULTS[kind]
    log(f"{kind}: old X={R['baseline'][0]:.4f} "
        f"(X-={R['baseline'][1]:.4f}) | "
        f"Q: X={R['Q'][0]:.4f} X-={R['Q'][1]:.4f} | "
        f"P: X={R['P'][0]:.4f} X-={R['P'][1]:.4f} | "
        f"obstructed {R['obstructed']}/{R['parents']} | "
        f"max|Q-P| {R['dmax']:.4f}")
log("readings: (i) X-(Q)<0.2 facts stabilize; (ii) X-(Q)>=0.2 facts only "
    "at lambda=1; (iii) obstruction >5% of parents")
log("DONE")
