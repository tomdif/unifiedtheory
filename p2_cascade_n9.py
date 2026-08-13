#!/usr/bin/env python3
"""P2 SHORE-UP (a): extend the cascade validation to n = 9 exactly.

Builds level 9 (unlabeled causets, expected count 183231), extends the
class-max-entropy pi/4 law through the 16999 level-8 parents, and
tests, STRICTLY OUT OF SAMPLE (constants fixed from transitions
4->5..6->7 as committed in cascade-sigma-2026-08-13):

  V1: sigma(9) prediction: sigma^2(9) = g sigma^2(8) + v + 2cov with
      (g, v, 2cov) = (0.864, 0.289, 0.224) -> predicted sigma(9);
      compare to exact sigma(9).
  V2: transition constants at 8->9: do g, v, cov persist?
  V3: overlap deceleration: c(A, 9) for has_post and stems - the
      cascade-saturation prediction is that ln c increments SHRINK.
"""
import math, time
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)
FORBID = set()
T0 = time.time()

# ---------------- extend tree to n = 9 --------------------------------------
log("building level 9...")
nxt = {}
cnt = 0
for key, (m, rel) in levels[8].items():
    for D in downsets_of(m, rel):
        nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
        nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    cnt += 1
    if cnt % 2000 == 0: log(f"  {cnt}/16999 parents expanded")
levels[9] = nxt
log(f"level 9: {len(nxt)} classes (expect 183231)")
allkeys9 = allkeys + sorted(levels[9])

log("building level-8 children maps...")
for key, (m, rel) in levels[8].items():
    S0 = action(rel, m)
    kid = {}
    for D in downsets_of(m, rel):
        nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
        ck = canon_fast(m + 1, nr)
        g = action(nr, m + 1) - S0
        if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
        else: kid[ck] = (1, g)
    children[key] = kid
log("children maps done")

# ---------------- law through level 8 ---------------------------------------
NMAXOLD = NMAX
law = {}
support = {root}; frontier = [root]
solved = 0
while frontier:
    nxt2 = []
    for p in frontier:
        if nelem(p) >= 9 or p not in children: continue
        cls, keep, mu, A, b = parent_system(p)
        x = born_point(mu, A, b, want="maxent")
        if x is None: continue
        solved += 1
        if solved % 2000 == 0: log(f"  {solved} parents solved")
        for idx, i in enumerate(keep):
            ck, muc, g = cls[i]
            if x[idx] > 1e-12:
                law[(p, ck)] = (x[idx], g, muc)
                if ck not in support:
                    support.add(ck); nxt2.append(ck)
    frontier = nxt2
log(f"law built through level 8: {len(law)} edges, {solved} parents")

R = {root: 1.0}
parents_of = {}
for k in allkeys9:
    if k != root: R[k] = 0.0
for p in allkeys9:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        parents_of.setdefault(ck, []).append((p, mu * rho))

SUP = {n: [k for k in levels[n] if R.get(k, 0) > 1e-300]
       for n in range(4, 10)}
log("R computed; support sizes: "
    + " ".join(f"n={n}:{len(SUP[n])}" for n in range(4, 10)))

# ---------------- V1/V2 -----------------------------------------------------
s2 = {n: float(np.var([math.log(R[k]) for k in SUP[n]]))
      for n in range(4, 10)}
log("sigma^2(n): " + "  ".join(f"n={n}:{s2[n]:.3f}" for n in range(4, 10)))
g_, v_, c_ = 0.864, 0.289, 0.224
pred9 = g_ * s2[8] + v_ + c_
log(f"V1: sigma(9) predicted = {math.sqrt(pred9):.3f}  "
    f"measured = {math.sqrt(s2[9]):.3f}  "
    f"err = {100*abs(math.sqrt(pred9)-math.sqrt(s2[9]))/math.sqrt(s2[9]):.1f}%")

par = SUP[8]; chd = SUP[9]
lnRp = {p: math.log(R[p]) for p in par}
Vp = float(np.var([lnRp[p] for p in par]))
Ls, ms = [], []
for c in chd:
    contribs = parents_of.get(c, [])
    tot = sum(R[p] * w for p, w in contribs)
    if tot <= 0: continue
    Ls.append(math.log(R[c]))
    ms.append(sum((R[p] * w / tot) * lnRp[p] for p, w in contribs))
Ls = np.array(Ls); ms = np.array(ms); ds = Ls - ms
gn = float(np.var(ms)) / Vp
vn = float(np.var(ds))
cn = 2 * float(np.cov(ms, ds)[0, 1])
log(f"V2: transition 8->9 constants: g = {gn:.3f}  v = {vn:.3f}  "
    f"2cov = {cn:+.3f}  (committed fit: 0.864 / 0.289 / +0.224)")

# ---------------- V3: overlap deceleration ----------------------------------
log("V3: overlap c(A, n) through n = 9 (has_post + stems)")
def class_obs(key):
    m, rel = key
    below = [set() for _ in range(m)]; above = [set() for _ in range(m)]
    for a_, b_ in rel:
        below[b_].add(a_); above[a_].add(b_)
    return sum(1 for x in range(m)
               if len(below[x]) + len(above[x]) == m - 1)
stems3 = sorted(levels[3]); stems4 = sorted(levels[4])
STEMS = [("has_post", None)] + [(f"stem{i}", s)
         for i, s in enumerate(stems3 + stems4[:6])]
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
for name, s in STEMS[:6]:
    cs = []
    for n in range(5, 10):
        sup = SUP[n]
        if s is None:
            Ak = [k for k in sup if class_obs(k) > 0]
        else:
            Ak = [k for k in sup if contains_stem(k, s)]
        if not Ak: cs.append(float("nan")); continue
        fR = sum(R[k] for k in Ak) / sum(R[k] for k in sup)
        fQ = sum(R[k] ** 2 for k in Ak) / sum(R[k] ** 2 for k in sup)
        cs.append(fQ / fR ** 2)
    incs = [math.log(cs[i + 1] / cs[i]) for i in range(len(cs) - 1)
            if cs[i] > 0 and cs[i + 1] > 0]
    log(f"  {name:9s} c(5..9) = "
        + "  ".join(f"{x:6.2f}" for x in cs)
        + "   dln-c increments: "
        + " ".join(f"{x:+.3f}" for x in incs))
log(f"total time {time.time()-T0:.0f}s")
log("DONE")
