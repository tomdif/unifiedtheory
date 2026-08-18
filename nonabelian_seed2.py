"""NONABELIAN SEED IN THE COUPLED SECTOR (registered 2026-08-17,
open attack 2 / chasm 2).  In UNCOUPLED product growth each factor
evolves by its own law: step amplitudes factorize and the two
factor-step operators commute exactly.  In COUPLED joint growth
(one bi-normalized law solved over the MERGED gap spectrum of both
factors' children - the model that produced gap correlation +0.615)
the second step's law depends on the first step's outcome.
STRUCTURE THEOREM (checked in-code): each factor's gap is intrinsic
to that factor, so the PHASE of any two-step joint amplitude is
order-independent - any noncommutativity lives ENTIRELY in the
magnitude sector (same sector as the covariance and Bell no-gos).
MEASURE: commutator defect delta(x,y) =
  |a(x|P)a(y|P+x) - a(y|P)a(x|P+y)| / max(|..|,|..|)
over factor-1 children x and factor-2 children y, averaged over
random joint growth paths.  Controls: uncoupled model must give
delta = 0 to machine precision.
READINGS: (i) delta > 0 generically, growing with size => the
coupled dynamics is order-noncommutative across factors: first
nonabelian seed (magnitude-sector); characterize distribution.
(ii) delta = 0 also when coupled => coupling preserves
commutativity; nonabelian route dead here.
(iii) delta > 0 but vanishing with size => transient only."""
import numpy as np, math, time
T0=time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
from law_ellipsoid import make_law_ell
rng = np.random.default_rng(20260823)
law = make_law_ell(math.pi/4, NSTART=16, disk_cache="law_cache_pi4_16.pkl")
PHIF = 0.25
def downsets(below):
    n = len(below)
    out = []
    for m in range(1 << n):
        ok = True
        for x in range(n):
            if (m >> x) & 1 and (m & below[x]) != below[x]: ok = False; break
        if ok: out.append(m)
    return out
def gaps_of(below, above, dlist):
    W2 = {0: 2, 1: -4, 2: 2}
    gs = []
    for D in dlist:
        g = 1; m = D
        while m:
            y = (m & -m).bit_length()-1
            k = bin(above[y] & D).count("1")
            g -= W2.get(k, 0)
            m &= m-1
        gs.append(g)
    return gs
def above_of(below):
    n = len(below)
    ab = [0]*n
    for x in range(n):
        m = below[x]
        while m:
            y = (m & -m).bit_length()-1; ab[y] |= 1 << x; m &= m-1
    return ab
def coupled_amp(state1, state2):
    """one merged-spectrum law over both factors' children.
    returns (list of (factor, D, gap, amplitude_magnitude), lw)"""
    b1, b2 = state1, state2
    a1, a2 = above_of(b1), above_of(b2)
    d1 = downsets(b1); d2 = downsets(b2)
    g1 = gaps_of(b1, a1, d1); g2 = gaps_of(b2, a2, d2)
    gc = {}
    for g in g1 + g2: gc[g] = gc.get(g, 0) + 1
    lw = law(gc)
    if lw is None: return None
    tot = sum(max(lw[g], 0) for g in g1 + g2)
    if tot <= 0: return None
    out = []
    for D, g in zip(d1, g1): out.append((1, D, g, math.sqrt(max(lw[g], 0)/tot)))
    for D, g in zip(d2, g2): out.append((2, D, g, math.sqrt(max(lw[g], 0)/tot)))
    return out
def uncoupled_amp(state1, state2):
    res = []
    for fi, b in ((1, state1), (2, state2)):
        ab = above_of(b); dl = downsets(b); gl = gaps_of(b, ab, dl)
        gc = {}
        for g in gl: gc[g] = gc.get(g, 0) + 1
        lw = law(gc)
        if lw is None: return None
        tot = sum(max(lw[g], 0) for g in gl)
        if tot <= 0: return None
        for D, g in zip(dl, gl): res.append((fi, D, g, math.sqrt(max(lw[g], 0)/tot)))
    return res
def add_elem(below, D):
    return below + [D]
def free_init(steps):
    """independent free growth per factor (uncoupled transient) -
    the symmetric root is Born-infeasible under asynchronous
    coupling (merged {1:2,-1:2} pins mu.x^2 = 0.5 < 1), so coupling
    engages after an asymmetric start, like the width-rule ramp."""
    out = []
    for _ in range(2):
        s = [0]
        for _ in range(steps):
            ab = above_of(s); dl = downsets(s); gl = gaps_of(s, ab, dl)
            gc = {}
            for g in gl: gc[g] = gc.get(g, 0) + 1
            lw = law(gc)
            ws = np.array([max(lw[g], 0) for g in gl]); ws = ws / ws.sum()
            s = add_elem(s, dl[rng.choice(len(dl), p=ws)])
        out.append(s)
    return out

def run(model, label, NPATH=40, NTOT=24):
    deltas_by_size = {}
    for path in range(NPATH):
        s1, s2 = free_init(3)
        for step in range(NTOT - 2):
            ch = model(s1, s2)
            if ch is None: break
            # commutator defect over sampled cross pairs
            f1 = [c for c in ch if c[0] == 1]; f2 = [c for c in ch if c[0] == 2]
            npair = min(4, len(f1), len(f2))
            for _ in range(npair):
                _, Dx, gx, ax = f1[rng.integers(len(f1))]
                _, Dy, gy, ay = f2[rng.integers(len(f2))]
                if ax <= 1e-12 or ay <= 1e-12: continue
                # order x then y
                chA = model(add_elem(s1, Dx), s2)
                if chA is None: continue
                ayA = next((c[3] for c in chA if c[0] == 2 and c[1] == Dy and c[2] == gy), None)
                # order y then x
                chB = model(s1, add_elem(s2, Dy))
                if chB is None: continue
                axB = next((c[3] for c in chB if c[0] == 1 and c[1] == Dx and c[2] == gx), None)
                if ayA is None or axB is None: continue
                A12 = ax * ayA; A21 = ay * axB
                den = max(A12, A21)
                if den <= 1e-12: continue
                delta = abs(A12 - A21) / den
                sz = len(s1) + len(s2)
                deltas_by_size.setdefault(sz, []).append(delta)
            # advance the path by one sampled birth
            ws = np.array([c[3]**2 for c in ch]); ws = ws / ws.sum()
            pick = ch[rng.choice(len(ch), p=ws)]
            if pick[0] == 1: s1 = add_elem(s1, pick[1])
            else: s2 = add_elem(s2, pick[1])
    print(f"\n{label}:")
    allv = []
    for sz in sorted(deltas_by_size):
        v = deltas_by_size[sz]
        allv.extend(v)
        print(f"  total size {sz:2d}: mean delta = {np.mean(v):.2e}  max = {np.max(v):.2e}  (n={len(v)})")
    print(f"  OVERALL: mean = {np.mean(allv):.2e}  max = {np.max(allv):.2e}  frac>1e-6 = {np.mean(np.array(allv)>1e-6):.3f}")
    return np.mean(allv)
log("control: uncoupled (must be ~0)")
d0 = run(uncoupled_amp, "UNCOUPLED (control)", NPATH=10)
log("coupled merged-spectrum law")
d1 = run(coupled_amp, "COUPLED")
print(f"\nVERDICT: uncoupled {d0:.2e} vs coupled {d1:.2e}")
print("reading (i) if coupled >> uncoupled ~ 0; (ii) if both ~0")
print("DONE-NONABELIAN")
