"""TURNOVER CHECK v2: exact class-DP for the BALANCED system
(1,-3,2) phi=0.625pi to n=11.  v1 died (macOS SIGKILL, memory) at
1.2M/1.55M parents of the 10->11 expansion: the Python dict of ~27M
classes x ~450B/entry exceeded RAM.  v2 fix: the FINAL level needs
no representatives (nothing expands past it; n=12 is unreachable by
the v1 gate anyway), so the 10->11 pass emits fixed-width numpy
records (key = 15 uint16: R, ACT+512, N0, 12 sorted packed
(indeg,outdeg,height) triples; value = Are, Aim, P, N1, N2) and
sort-reduces them chunk-wise into a ~2GB master.  Levels 1..10 keep
the v1 dict path (1.55M classes, verified vs reference at 0.8%).
Decision rule (pre-registered): tex_mu increments were
+0.0139/+0.0120/+0.0100; increment at n=11 <= ~+0.008 keeps
deceleration/turnover alive; rebound firms the gate-1 verdict."""
import numpy as np, math, sys, time, resource
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**30
exec(open('selection_and_action.py').read().split('if MODE == "A":')[0])
from law_ellipsoid import make_law_ell
NMAX = 11
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NMAX)}
W = (1,-3,2); PHIF = 0.625
law = make_law_ell(PHIF*math.pi, NSTART=16)   # converged maxent member (JITTER_AUDIT)
warr = np.zeros(NMAX+2, dtype=np.int64)
for k in range(3): warr[k] = W[k]
def sprink(n, T=6000):
    rs=[]; abs_=np.zeros(3)
    for _ in range(T):
        u=rng.random(n); v=rng.random(n)
        idx=np.argsort(u); v=v[idx]
        bel=[0]*n
        for i in range(n):
            for j in range(i):
                if v[j]<v[i]: bel[i] |= 1<<j
        rs.append(sum(bin(b).count("1") for b in bel)/(n*(n-1)/2))
        above=[0]*n
        for x in range(n):
            m=bel[x]
            while m:
                y=(m&-m).bit_length()-1; above[y]|=1<<x; m&=m-1
        for x in range(n):
            m=bel[x]
            while m:
                y=(m&-m).bit_length()-1
                kk=bin(above[y]&bel[x]).count("1")
                if kk<3: abs_[kk]+=1
                m&=m-1
    return float(np.mean(rs)), abs_/T/n
SPR = {n: sprink(n) for n in (8,9,10,11)}
TEX = {}
for n in SPR: log(f"sprinkling n={n}: ab={np.round(SPR[n][1],3)}")
import struct
def pack_below(bel): return struct.pack(f"<{len(bel)}H", *bel)
def unpack_below(b, n): return list(struct.unpack(f"<{n}H", b))

def parent_children(bel, n, A, P, N0, N1, N2, R, ACT):
    """Shared per-parent machinery: returns None (dead parent) or
    (dlist, g, h0, h1, h2, p, enc, Rn) for all children."""
    above = [0]*n
    for x in range(n):
        m = bel[x]
        while m:
            y = (m & -m).bit_length()-1
            above[y] |= 1 << x; m &= m-1
    masks = ARANGE[n]; okm = np.ones(masks.shape[0], dtype=bool)
    for x in range(n):
        bx = bel[x]
        if bx == 0: continue
        okm &= ~(((masks>>x)&1==1)&((masks&bx)!=bx))
    dlist = masks[okm]
    nc = dlist.shape[0]
    g = np.ones(nc, dtype=np.int64)
    h0 = np.zeros(nc, dtype=np.int64); h1 = np.zeros(nc, dtype=np.int64); h2 = np.zeros(nc, dtype=np.int64)
    bits = ((dlist[:, None] >> np.arange(n)) & 1).astype(bool)
    for d in range(n):
        sel = bits[:, d]
        if not sel.any(): continue
        kv = popcount(dlist[sel] & np.int64(above[d])).astype(np.int64)
        g[sel] -= warr[np.minimum(kv, 2)]
        h0[sel] += (kv == 0); h1[sel] += (kv == 1); h2[sel] += (kv == 2)
    gc = {}
    for gg in g.tolist(): gc[gg] = gc.get(gg, 0)+1
    lw = law(gc)
    if lw is None: return None
    p = np.array([lw[gg] for gg in g.tolist()]); p = np.maximum(p, 0)
    s = p.sum()
    if s <= 0: return None
    p = p / s
    indeg = np.array([bin(b).count("1") for b in bel])
    outdeg = np.array([bin(a).count("1") for a in above])
    hgt = np.ones(n, dtype=np.int64)
    for x in sorted(range(n), key=lambda x: bin(bel[x]).count("1")):
        m = bel[x]; best = 0
        while m:
            y = (m&-m).bit_length()-1
            if hgt[y] > best: best = hgt[y]
            m &= m-1
        hgt[x] = best + 1
    popD = bits.sum(axis=1)
    out_ch = outdeg[None, :] + bits
    hnew = 1 + (hgt[None, :] * bits).max(axis=1)
    enc_old = (np.broadcast_to(indeg, (nc, n)) * 4096
               + out_ch * 64 + np.broadcast_to(hgt, (nc, n)))
    enc_new = (popD * 4096 + 0 * 64 + hnew)[:, None]
    enc = np.sort(np.concatenate([enc_old, enc_new], axis=1), axis=1)
    Rn = R + popD
    return dlist, bits, g, h0, h1, h2, p, enc, Rn

# ---- levels 1..10: dict path with representatives ----
states = {b"root": [1+0j, 1.0, pack_below([0]), 0.0, 0.0, 0.0, 0, 0]}
for n in range(1, NMAX-1):
    new = {}
    t0 = time.time(); done = 0
    for key, (A, P, belb, N0, N1, N2, R, ACT) in states.items():
        bel = unpack_below(belb, n)
        out = parent_children(bel, n, A, P, N0, N1, N2, R, ACT)
        if out is None: continue
        dlist, bits, g, h0, h1, h2, p, enc, Rn = out
        plist = p.tolist(); glist = g.tolist()
        for j in range(dlist.shape[0]):
            pp = plist[j]
            if pp < 1e-13: continue
            gg = glist[j]
            ckey = (Rn[j].tobytes() + np.int64(ACT + gg).tobytes()
                    + np.int64(round(N0 + float(h0[j]))).tobytes() + enc[j].tobytes())
            x = math.sqrt(pp)
            a = A * x * complex(math.cos(PHIF*math.pi*gg), math.sin(PHIF*math.pi*gg))
            pr = P * pp
            e = new.get(ckey)
            if e is not None:
                e[0] += a; e[1] += pr
            else:
                cb = bel + [int(dlist[j])]
                new[ckey] = [a, pr, pack_below(cb),
                             N0 + float(h0[j]), N1 + float(h1[j]), N2 + float(h2[j]), int(Rn[j]),
                             ACT + gg]
        done += 1
        if done % 200000 == 0:
            log(f"  level {n}->{n+1}: {done}/{len(states)} parents, {len(new)} classes  rss={rss():.1f}GB")
    states = new
    nn = n+1
    log(f"level {nn}: {len(states)} classes  ({time.time()-t0:.0f}s)  rss={rss():.1f}GB")
    if nn in (8, 9, 10):
        mu_tot = sum(abs(e[0])**2 for e in states.values())
        P_tot = sum(e[1] for e in states.values())
        r_s, ab_s = SPR[nn]
        tMu = tP = rMu = 0.0
        for e in states.values():
            ab = np.array([e[3], e[4], e[5]]) / nn
            t_ = float(np.sqrt(((ab - ab_s)**2).sum()))
            r_ = e[6] / (nn*(nn-1)/2)
            wmu = abs(e[0])**2/mu_tot
            tMu += wmu * t_; tP += (e[1]/P_tot) * t_; rMu += wmu * r_
        log(f"  n={nn}: tex_mu={tMu:.4f}  tex_P={tP:.4f}  r_mu={rMu:.4f}")
        TEX[nn] = tMu

# ---- final level 10->11: representative-free spill path ----
n = NMAX-1  # 10
KW = n + 4   # key width in uint16: R, ACT+512, N0, (n+1) triples = 15 at n=10
CHUNK = 3_000_000
Ks = []; Vs = []; nrows = 0
K_m = None; V_m = None
def merge():
    global Ks, Vs, nrows, K_m, V_m
    if nrows == 0 and K_m is not None: return
    K = np.concatenate(Ks) if Ks else np.empty((0, KW), np.uint16)
    V = np.concatenate(Vs) if Vs else np.empty((0, 5), np.float64)
    if K_m is not None:
        K = np.concatenate([K_m, K]); V = np.concatenate([V_m, V])
    Kv = np.ascontiguousarray(K).view([('b', f'V{2*KW}')]).ravel()
    order = np.argsort(Kv, kind='stable')
    Kv = Kv[order]; K = K[order]; V = V[order]
    newgrp = np.empty(Kv.shape[0], bool); newgrp[0] = True
    newgrp[1:] = Kv[1:] != Kv[:-1]
    first = np.flatnonzero(newgrp)
    gid = np.cumsum(newgrp) - 1
    ng = first.shape[0]
    Vm = np.empty((ng, 5))
    for c in (0, 1, 2):
        Vm[:, c] = np.bincount(gid, weights=V[:, c], minlength=ng)
    Vm[:, 3] = V[first, 3]; Vm[:, 4] = V[first, 4]
    K_m = K[first].copy(); V_m = Vm
    Ks = []; Vs = []; nrows = 0

t0 = time.time(); done = 0
for key, (A, P, belb, N0, N1, N2, R, ACT) in states.items():
    bel = unpack_below(belb, n)
    out = parent_children(bel, n, A, P, N0, N1, N2, R, ACT)
    done += 1
    if out is None: continue
    dlist, bits, g, h0, h1, h2, p, enc, Rn = out
    jj = np.flatnonzero(p >= 1e-13)
    if jj.size == 0: continue
    gg = g[jj]; pp = p[jj]
    Krow = np.empty((jj.size, KW), np.uint16)
    Krow[:, 0] = Rn[jj]
    Krow[:, 1] = (ACT + gg + 512)
    Krow[:, 2] = np.round(N0 + h0[jj]).astype(np.int64)
    Krow[:, 3:] = enc[jj]
    a = A * np.sqrt(pp) * np.exp(1j * PHIF * math.pi * gg)
    Vrow = np.stack([a.real, a.imag, P * pp,
                     N1 + h1[jj].astype(float), N2 + h2[jj].astype(float)], axis=1)
    Ks.append(Krow); Vs.append(Vrow); nrows += jj.size
    if nrows >= CHUNK:
        merge()
        log(f"  merge at {done}/{len(states)} parents: master {K_m.shape[0]} classes  rss={rss():.1f}GB")
    if done % 200000 == 0:
        log(f"  level 10->11: {done}/{len(states)} parents  rss={rss():.1f}GB")
merge()
nn = 11
log(f"level 11: {K_m.shape[0]} classes  ({time.time()-t0:.0f}s)  rss={rss():.1f}GB")
mu = V_m[:, 0]**2 + V_m[:, 1]**2
mu_tot = mu.sum(); P_tot = V_m[:, 2].sum()
r_s, ab_s = SPR[11]
ab = np.stack([K_m[:, 2].astype(float), V_m[:, 3], V_m[:, 4]], axis=1) / nn
t_ = np.sqrt(((ab - np.asarray(ab_s)[None, :])**2).sum(axis=1))
r_ = K_m[:, 0].astype(float) / (nn*(nn-1)/2)
tMu = float((mu/mu_tot * t_).sum())
tP = float((V_m[:, 2]/P_tot * t_).sum())
rMu = float((mu/mu_tot * r_).sum())
log(f"  n=11: tex_mu={tMu:.4f}  tex_P={tP:.4f}  r_mu={rMu:.4f}")
wts = np.sort(mu)[::-1]
c = np.cumsum(wts)/mu_tot
k95 = int(np.searchsorted(c, 0.95))+1; k999 = int(np.searchsorted(c, 0.999))+1
log(f"  mass concentration: 95% in {k95} classes, 99.9% in {k999}")
TEX[11] = tMu
lad = [TEX[k] for k in (8,9,10,11)]
incs = [lad[i+1]-lad[i] for i in range(3)]
log(f"  CORRECTED LADDER tex_mu(8..11) = {['%.4f'%v for v in lad]}")
log(f"  increments: {['%+.4f'%v for v in incs]}  [decelerating+small final => turnover live; steady/rebound => verdict firms]")
log("DONE-TURN2")
