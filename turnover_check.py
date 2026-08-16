"""TURNOVER CHECK: extend the exact class-DP for the BALANCED system
(1,-3,2) phi=0.625pi to n=11 (and n=12 if mass concentrates).
Vectorized child-key construction; texture_mu(11[,12]) decides:
falling/plateau => turnover (manifold hope revives); rising =>
structural verdict final at these weights."""
import numpy as np, math, sys, time
from collections import defaultdict
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
exec(open('selection_and_action.py').read().split('if MODE == "A":')[0])
NMAX = 12
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NMAX+1)}
W = (1,-3,2); PHIF = 0.625
law = make_law(PHIF*math.pi)
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
SPR = {n: sprink(n) for n in (10,11,12)}
for n in SPR: log(f"sprinkling n={n}: ab={np.round(SPR[n][1],3)}")
# state: key(bytes) -> [A, P, below_bytes, N0,N1,N2, R]
import struct
def pack_below(bel): return struct.pack(f"<{len(bel)}H", *bel)
def unpack_below(b, n): return list(struct.unpack(f"<{n}H", b))
states = {b"root": [1+0j, 1.0, pack_below([0]), 0.0, 0.0, 0.0, 0, 0]}
for n in range(1, NMAX):
    new = {}
    t0 = time.time(); done = 0
    for key, (A, P, belb, N0, N1, N2, R, ACT) in states.items():
        bel = unpack_below(belb, n)
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
        if lw is None: continue
        p = np.array([lw[gg] for gg in g.tolist()]); p = np.maximum(p, 0)
        s = p.sum()
        if s <= 0: continue
        p = p / s
        # vectorized per-child invariants
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
        out_ch = np.sort(outdeg[None, :] + bits, axis=1)
        hnew = 1 + (hgt[None, :] * bits).max(axis=1)
        ind_sorted = np.sort(np.concatenate([np.broadcast_to(indeg, (nc, n)), popD[:, None]], axis=1), axis=1)
        h_all = np.sort(np.concatenate([np.broadcast_to(hgt, (nc, n)), hnew[:, None]], axis=1), axis=1)
        Rn = R + popD
        plist = p.tolist(); glist = g.tolist()
        for j in range(nc):
            pp = plist[j]
            if pp < 1e-13: continue
            gg = glist[j]
            ckey = (Rn[j].tobytes() + np.int64(ACT + gg).tobytes()
                    + ind_sorted[j].tobytes() + out_ch[j].tobytes() + h_all[j].tobytes())
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
            log(f"  level {n}->{n+1}: {done}/{len(states)} parents, {len(new)} classes")
    # collision note: ckey embeds action via cumulative? action not in key: add gg cumulative? 
    states = new
    nn = n+1
    log(f"level {nn}: {len(states)} classes  ({time.time()-t0:.0f}s)")
    if nn in (10, 11, 12):
        mu_tot = sum(abs(e[0])**2 for e in states.values())
        P_tot = sum(e[1] for e in states.values())
        r_s, ab_s = SPR.get(nn, (None, None))
        tMu = tP = rMu = 0.0
        for e in states.values():
            ab = np.array([e[3], e[4], e[5]]) / nn
            t_ = float(np.sqrt(((ab - ab_s)**2).sum()))
            r_ = e[6] / (nn*(nn-1)/2)
            wmu = abs(e[0])**2/mu_tot
            tMu += wmu * t_; tP += (e[1]/P_tot) * t_; rMu += wmu * r_
        log(f"  n={nn}: tex_mu={tMu:.4f}  tex_P={tP:.4f}  r_mu={rMu:.4f}")
        # mass concentration for n=12 gating
        if nn == 11:
            wts = sorted((abs(e[0])**2 for e in states.values()), reverse=True)
            c = np.cumsum(wts)/mu_tot
            k95 = int(np.searchsorted(c, 0.95))+1; k999 = int(np.searchsorted(c, 0.999))+1
            log(f"  mass concentration: 95% in {k95} classes, 99.9% in {k999}")
            if len(states) > 4_000_000 and k999 > 3_000_000:
                log("  n=12 too heavy without unacceptable trimming - STOPPING at 11")
                break
            if len(states) > 3_000_000:
                keep = sorted(states.items(), key=lambda kv: -(abs(kv[1][0])**2 + kv[1][1]))[:3_000_000]
                kept_mu = sum(abs(e[0])**2 for _, e in keep)/mu_tot
                kept_P = sum(e[1] for _, e in keep)/P_tot
                log(f"  TRIM to 3M classes: kept mu-mass {kept_mu:.6f}, P-mass {kept_P:.6f}")
                states = dict(keep)
log("DONE-TURN")
