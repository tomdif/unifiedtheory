#!/usr/bin/env python3
"""FACT-STABILITY CONJECTURE PROBE (pre-proof reconnaissance).

Conjecture (PI4_FIRST_PREDICTION): the max-entropy pi/4 law has
monotone coherent stem measures (X_minus(Q) = 0 measured to 4
decimals).  Before attempting a theorem, decide WHAT is true:

  (A) EXACTNESS: X_minus(Q) at 1e-12 precision - exact zero or small?
  (B) EXPONENTIAL FAMILY: is ln rho affine in the action gap at every
      parent (hand-verified exactly at the 2-antichain: ratio
      sqrt2+1 = cot(pi/8) per two gap units)?  If yes, path moduli
      telescope like the phases do.
  (C) CLASS FACTORIZATION: is |Psi(C)| = Npaths(C) * e^{a_T + lam S(C)}
      per level (phase-free coherent measure after class
      identification)?  Fit ln(|Psi|/N) against S per level; report
      residuals.

Readings:
  (i)  A exact + B/C exact: the conjecture has a structural mechanism
       (telescoping exponential law); theorem = phase-freeness +
       reduction; Lean-able.
  (ii) A exact but B/C fail: another mechanism; investigate before
       proving.
  (iii) A only approximate: the conjecture as stated is FALSE (report
       the size); the theorem to keep is the lambda-bound already
       proven.
"""
import math, sys
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)

FORBID = set()

# ---------------- build the class-max-entropy law ---------------------------
law = {}
support = {root}; frontier = [root]
rho_records = []
while frontier:
    nxt = []
    for p in frontier:
        if nelem(p) >= NMAX: continue
        cls, keep, mu, A, b = parent_system(p)
        x = born_point(mu, A, b, want="maxent")
        if x is None: continue
        gs = []
        for idx, i in enumerate(keep):
            ck, muc, g = cls[i]
            if x[idx] > 1e-12:
                law[(p, ck)] = (x[idx], g, muc)
                gs.append((g, x[idx], muc))
                if ck not in support:
                    support.add(ck); nxt.append(ck)
        rho_records.append((p, gs))
    frontier = nxt
log(f"law built: {len(law)} edges, support {len(support)}")

# ---------------- (B) affine test -------------------------------------------
log("== (B) ln rho affine in gap, per parent ==")
worst = (0.0, None)
aff_ok = 0; aff_tot = 0
lams = []
for p, gs in rho_records:
    if len(gs) < 3:
        continue
    garr = np.array([g for g, r, m in gs], float)
    larr = np.array([math.log(r) for g, r, m in gs])
    # check classes sharing a gap get equal rho first
    A2 = np.vstack([garr, np.ones(len(gs))]).T
    coef, res2, *_ = np.linalg.lstsq(A2, larr, rcond=None)
    pred = A2 @ coef
    dev = float(np.max(np.abs(pred - larr)))
    aff_tot += 1
    if dev < 1e-8: aff_ok += 1
    lams.append(coef[0])
    if dev > worst[0]: worst = (dev, (nelem(p), len(gs), coef[0]))
log(f"  parents with >=3 supported groups: {aff_tot}; affine to 1e-8: "
    f"{aff_ok}")
log(f"  worst affine deviation: {worst[0]:.3e} at (n, K, lam) = {worst[1]}")
if lams:
    log(f"  lambda (slope) stats: min {min(lams):.6f} max {max(lams):.6f} "
        f"mean {np.mean(lams):.6f}")
    log(f"  reference ln(sqrt(cot(pi/8))) = "
        f"{0.5 * math.log(1 + math.sqrt(2)):.6f}")

# ---------------- DP: Psi and supported path counts -------------------------
S0 = {k: action(levels[nelem(k)][k][1], nelem(k)) for k in allkeys}
Psi = {root: 1.0 + 0j}; Np = {root: 1.0}
for k in allkeys:
    if k != root: Psi[k] = 0.0 + 0j; Np[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        Psi[ck] += Psi[p] * mu * rho * np.exp(1j * gg * PHI4)
        Np[ck] += Np[p] * mu

# ---------------- (C) class factorization -----------------------------------
log("== (C) |Psi(C)| = Npaths(C) e^{a_T + lam S(C)} per level ==")
for T in range(3, NMAX + 1):
    xs, ys = [], []
    for k in levels[T]:
        if abs(Psi[k]) > 1e-300 and Np[k] > 0:
            xs.append(S0[k]); ys.append(math.log(abs(Psi[k]) / Np[k]))
    if len(xs) < 3: continue
    A2 = np.vstack([np.array(xs, float), np.ones(len(xs))]).T
    coef, *_ = np.linalg.lstsq(A2, np.array(ys), rcond=None)
    resid = float(np.max(np.abs(A2 @ coef - ys)))
    log(f"  T={T}: classes {len(xs)}  lam_fit = {coef[0]:+.6f}  "
        f"max residual = {resid:.3e}")
# phase check: arg Psi = phi * (S - S_root) mod 2pi?
worstph = 0.0
for T in range(3, NMAX + 1):
    for k in levels[T]:
        if abs(Psi[k]) > 1e-12:
            ph = np.angle(Psi[k]) - PHI4 * (S0[k] - S0[root])
            ph = (ph + math.pi) % (2 * math.pi) - math.pi
            worstph = max(worstph, abs(ph))
log(f"  phase telescoping: max |arg Psi - phi*DeltaS| mod 2pi = "
    f"{worstph:.3e}")

# ---------------- (A) exact X_minus(Q) --------------------------------------
log("== (A) X_minus(Q) at full precision ==")
stems3 = sorted(levels[3]); stems4 = sorted(levels[4])
STEMS = stems3 + stems4[:6]
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
Xm = 0.0; worst_step = (0.0, None)
tabs = {}
for s in STEMS:
    vals = []
    for T in range(4, NMAX + 1):
        om = sum(abs(Psi[k]) ** 2 for k in levels[T])
        num = sum(abs(Psi[k]) ** 2 for k in levels[T]
                  if contains_stem(k, s))
        vals.append(num / om)
    tabs[s] = vals
    for j in range(1, len(vals) - 1):
        d = vals[j + 1] - vals[j]
        if d < 0:
            Xm += -d
            if -d > worst_step[0]: worst_step = (-d, (s, j))
log(f"  X_minus(Q) over T=5..{NMAX} = {Xm:.3e}")
log(f"  worst single regression = {worst_step[0]:.3e}")
log("  (readings: exact zero -> mechanism hunt; nonzero -> conjecture "
    "false as stated)")
log("DONE")

# ---------------- (D) normalized-ratio margins ------------------------------
log("== (D) A-block growth vs B-block retention per stem/step ==")
worst_margin = (1e9, None)
for s in STEMS:
    inA = {k: contains_stem(k, s) for k in allkeys if nelem(k) >= 4}
    for T in range(4, NMAX):
        NA = sum(abs(Psi[k]) ** 2 for k in levels[T]
                 if inA.get(k, False))
        NB = sum(abs(Psi[k]) ** 2 for k in levels[T]
                 if not inA.get(k, False))
        NA2 = sum(abs(Psi[k]) ** 2 for k in levels[T + 1]
                  if inA.get(k, False))
        NB2 = sum(abs(Psi[k]) ** 2 for k in levels[T + 1]
                  if not inA.get(k, False))
        if NA > 1e-300 and NB > 1e-300:
            gA = NA2 / NA; rB = NB2 / NB
            m = gA / rB
            if m < worst_margin[0]:
                worst_margin = (m, (T, gA, rB))
log(f"  min over stems/steps of (A-growth)/(B-retention) = "
    f"{worst_margin[0]:.6f} at (T, gA, rB) = {worst_margin[1]}")
log("  (>1 everywhere <=> normalized monotonicity; =1 would be tight)")
log("DONE-D")
