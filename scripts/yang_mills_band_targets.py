"""Numerical attack on the three band-crossing targets of GAP_BAND_STATEMENT.md (T1, T2, T3), 4D SU(2) Wilson action.

Geometry: lattice Lx x M^3, periodic; the spatial links of the layer x0 = 0 are frozen to a boundary condition (BC),
everything else is updated by heat bath + 2 overrelaxation (the sampler of yang_mills_sl_gpu, with a frozen mask).
The frozen layer bounds a slab of depth Lx from both sides; depth of layer x0 is d = min(x0, Lx - x0).
BC families (spatial links of the frozen layer):
  cold  U = 1;  hot  Haar-random (fixed draw);  anti  U_1 = (-1)^{x2}, U_2 = (-1)^{x3}, U_3 = 1, so the (1,2) and
  (2,3) boundary plaquettes are -1 (maximal action);  flux  U_1 = -1 on x2 = 0 (a Z2 vortex pair in the layer).
T2 (BC-uniform decay of correlations): Delta_BC(d) = E_BC[P_s(d)] - E_cold[P_s(d)], P_s(d) the mean spatial
  plaquette of layer d; fitted rate m_BC from Delta(d) ~ e^{-m d} on the points above 3 sigma.
T3 (finite-box criterion input): L0(eps) = smallest depth with max_BC |Delta_BC(d)| < eps, for eps = 1e-2, 1e-3.
T1 (volume-uniform dynamical gap): with the cold BC, run R replica pairs from a cold and a hot interior start;
  D(t) = E[P_cold(t) - P_hot(t)] (mean interior plaquette after t sweeps) ~ e^{-gamma t}; gamma(M) for M = 4, 8, 12.
Written before the run (2026-11-06):
 (1) T2: for beta_std <= 2.5 every BC gives a finite rate m_BC >= 0.5 per lattice unit, BC-independent within 30%
     (the 0++ glueball channel); the rate falls with beta.
 (2) T3: L0(1e-3) <= 6 at beta_std <= 2.3 and grows past 6 by beta_std 3.
 (3) T1: gamma does not decrease from M = 8 to 12 at beta_std <= 2.5 (no volume dependence in the neutral energy
     relaxation), i.e. no sign of a closing dynamical gap in the band.
Added 2026-11-06 (second round), written before these runs:
 adv  (T2, adversarial families): uniform abelian boundary flux phi = 2 pi k / M in the (1,2) and (2,3) planes,
      k = 0..M/2 (k = 0 is cold, k = M/2 is anti-like). Also the electric-flux sector: smeared spatial Polyakov loop
      P_1(d) along x1 under the cold BC (boundary holonomy +1) and the center-flipped BC (U_1 = -1 on one x1-slice of
      the layer: same boundary plaquettes, holonomy -1).
      (4) the worst plaquette influence over the flux family at depth 4 is within a factor 2 of the worst of
          hot/anti (no hidden adversarial direction among smooth fluxes);
      (5) the Polyakov-sector influence |P_1^cold(d) - P_1^flip(d)| decays exponentially with a rate close to
          sigma M (sigma a^2 ~ 0.07 at beta 2.3, 0.035 at 2.5), i.e. SLOWER than the plaquette at M = 12, beta 2.5:
          the long-range sector is the binding constraint for T3's box size.
 auto (T1, slowest sector): periodic N^4, no frozen layer; MC-time autocorrelation of the smeared spatial Polyakov
      loop averages (charged) and their squares (neutral), N = 8, 12, 16.
      (6) at beta 2.3 (confined for N >= 8, beta_c(N_t = 8) = 2.51) the neutral tau_int does not grow from N = 12 to 16; the charged
          one may (center-sector tunnelling is a finite-volume effect outside the neutral target).
Usage: out mode(bc|relax|adv|auto) betas Lx M sweeps [extra]
"""
import os, sys, json, math, time
import torch
dev = os.environ.get('YM_DEV', 'cuda' if torch.cuda.is_available() else 'cpu')
torch.set_default_device(dev)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_sl_gpu as G
DT = torch.float32
G.DT = DT; G.dev = dev; G.CJ = torch.tensor([1., -1, -1, -1], dtype=DT)
qmul, qc, S, staple = G.qmul, G.qc, G.S, G.staple


def kp(k):
    """a0 ~ sqrt(1 - a^2) e^{k a} on [-1, 1]. Kennedy-Pendleton for k >= 1; for small k (where KP can stall, e.g. at
    near-cancelling staples next to a frozen flux layer) exact rejection from the uniform S^3 marginal."""
    out = torch.empty_like(k); big = k >= 1
    if bool(big.any()): out[big] = G.kp(k[big])
    idx = (~big).nonzero(as_tuple=True)[0]
    while idx.numel():
        ks = k[idx].double(); g = torch.randn((idx.numel(), 4), dtype=torch.float64)
        a = g[:, 0] / g.norm(dim=-1); ok = torch.rand(idx.numel(), dtype=torch.float64) <= torch.exp(ks * (a - 1))
        out[idx[ok]] = a[ok].to(DT); idx = idx[~ok]
    return out


def update(U, z, beta, par, free, heat):
    for m in range(4):
        for p in (0, 1):
            K = 2 * beta * qc(staple(U, z, m)); nrm = K.norm(dim=-1)
            mask = (par == p) & (nrm > 1e-12) & free[m]; Kd = K[mask] / nrm[mask][:, None]
            if heat:
                a0 = kp(nrm[mask]); v = torch.randn((a0.numel(), 3), dtype=DT); v = v / v.norm(dim=-1, keepdim=True)
                new = qmul(torch.cat([a0[:, None], torch.sqrt(torch.clamp(1 - a0 ** 2, min=0))[:, None] * v], -1), Kd)
            else:
                new = qmul(qmul(Kd, qc(U[m][mask])), Kd)
            U[m][mask] = new / new.norm(dim=-1, keepdim=True)


def sweep(U, z, beta, par, free):
    update(U, z, beta, par, free, True); update(U, z, beta, par, free, False); update(U, z, beta, par, free, False)


def setup(Lx, M):
    shp = (Lx, M, M, M); xs = torch.stack(torch.meshgrid(*[torch.arange(n) for n in shp], indexing='ij'))
    par = xs.sum(0) % 2; z = torch.ones(shp, dtype=DT)
    free = torch.stack([torch.ones(shp, dtype=torch.bool)] + [xs[0] != 0] * 3)
    return shp, xs, par, z, free


def bc_links(kind, shp, xs, gen):
    U = torch.zeros((4,) + shp + (4,), dtype=DT); U[..., 0] = 1
    lay = xs[0] == 0
    if kind == 'hot':
        for m in (1, 2, 3):
            h = torch.randn(shp + (4,), dtype=DT, generator=gen); h = h / h.norm(dim=-1, keepdim=True); U[m][lay] = h[lay]
    elif kind == 'anti':
        U[1][lay & (xs[2] % 2 == 1)] = torch.tensor([-1., 0, 0, 0]); U[2][lay & (xs[3] % 2 == 1)] = torch.tensor([-1., 0, 0, 0])
    elif kind == 'flux':
        U[1][lay & (xs[2] == 0)] = torch.tensor([-1., 0, 0, 0])
    return U


def layer_plaq(U, z):
    P = G.plaq_re(U, z)
    return torch.stack([P[(1, 2)], P[(1, 3)], P[(2, 3)]]).mean((0, 2, 3, 4))       # (Lx,)


def mode_bc(out, betas, Lx, M, nsw):
    shp, xs, par, z, free = setup(Lx, M); res = []
    gen = torch.Generator(device=dev).manual_seed(7)
    d = torch.minimum(torch.arange(Lx), Lx - torch.arange(Lx)); D = Lx // 2
    for b in betas:
        beta = b / 2; t0 = time.time(); prof = {}
        for kind in ('cold', 'hot', 'anti', 'flux'):
            U = bc_links(kind, shp, xs, gen)
            for _ in range(300): sweep(U, z, beta, par, free)
            rec = []
            for _ in range(nsw):
                sweep(U, z, beta, par, free); lp = layer_plaq(U, z)
                rec.append(torch.stack([lp[d == k].mean() for k in range(1, D + 1)]))
            rec = torch.stack(rec).double(); nb = 20; bm = rec[: (nsw // nb) * nb].reshape(nb, -1, D).mean(1)
            prof[kind] = (rec.mean(0), bm.std(0) / math.sqrt(nb))
        row = dict(mode='bc', bstd=b, Lx=Lx, M=M, sweeps=nsw, P_cold=prof['cold'][0].tolist())
        worst = torch.zeros(D, dtype=torch.float64)
        for kind in ('hot', 'anti', 'flux'):
            dl = prof[kind][0] - prof['cold'][0]; er = torch.sqrt(prof[kind][1] ** 2 + prof['cold'][1] ** 2)
            ok = (dl.abs() > 3 * er).nonzero().flatten().tolist(); rate = None
            ks = [k for k in ok if k == ok[0] + ok.index(k)] if ok and ok[0] == 0 else []   # leading run of significant points
            if len(ks) >= 2:
                y = torch.log(dl.abs()[ks]); x = torch.tensor(ks, dtype=torch.float64) + 1
                rate = float(-((x - x.mean()) * (y - y.mean())).sum() / ((x - x.mean()) ** 2).sum())
            row[kind] = dict(delta=dl.tolist(), err=er.tolist(), n_sig=len(ks), rate=rate)
            worst = torch.maximum(worst, dl.abs() + 2 * er)
        for eps in (1e-2, 1e-3):
            below = (worst < eps).nonzero().flatten().tolist(); row[f'L0_{eps}'] = (below[0] + 1) if below else None
        row['sec'] = round(time.time() - t0, 1); res.append(row); print(json.dumps(row), flush=True)
        json.dump(res, open(out, 'w'), indent=1)


def mode_relax(out, betas, Lx, Ms, T, R):
    res = []
    for M in Ms:
        shp, xs, par, z, free = setup(Lx, M); gen = torch.Generator(device=dev).manual_seed(11)
        interior = (xs[0] != 0)
        for b in betas:
            beta = b / 2; t0 = time.time(); D = torch.zeros(T, dtype=torch.float64); D2 = torch.zeros(T, dtype=torch.float64)
            for r in range(R):
                tr = []
                for start in ('cold', 'hot'):
                    U = bc_links('cold', shp, xs, gen)
                    if start == 'hot':
                        for m in range(4):
                            h = torch.randn(shp + (4,), dtype=DT, generator=gen); h = h / h.norm(dim=-1, keepdim=True)
                            U[m][free[m]] = h[free[m]]
                    pt = []
                    for _ in range(T):
                        sweep(U, z, beta, par, free); P = G.plaq_re(U, z)
                        pt.append(torch.stack([v[interior].mean() for v in P.values()]).mean())
                    tr.append(torch.stack(pt).double())
                dd = tr[0] - tr[1]; D += dd; D2 += dd ** 2
            D /= R; err = torch.sqrt((D2 / R - D ** 2).clamp_min(0) / R)
            ok = (D.abs() > 3 * err).nonzero().flatten().tolist()
            lead = [k for i, k in enumerate(ok) if k == i]
            gamma = None
            if len(lead) >= 4:
                ks = lead[len(lead) // 4:]
                y = torch.log(D.abs()[ks]); x = torch.tensor(ks, dtype=torch.float64)
                gamma = float(-((x - x.mean()) * (y - y.mean())).sum() / ((x - x.mean()) ** 2).sum())
            row = dict(mode='relax', bstd=b, Lx=Lx, M=M, R=R, D=D.tolist()[:40], n_sig=len(lead), gamma=gamma,
                       sec=round(time.time() - t0, 1))
            res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


def flux_bc(k, shp, xs, sigma=3):
    U = torch.zeros((4,) + shp + (4,), dtype=DT); U[..., 0] = 1; M = shp[1]; lay = xs[0] == 0
    phi = 2 * math.pi * k / M
    for m, dep in ((1, 2), (2, 3)):
        ang = phi * xs[dep].to(DT); q = torch.zeros(shp + (4,), dtype=DT)
        q[..., 0] = torch.cos(ang); q[..., sigma] = torch.sin(ang); U[m][lay] = q[lay]
    return U


def mode_adv(out, betas, Lx, M, nsw, only_p1=False):
    shp, xs, par, z, free = setup(Lx, M); res = []
    d = torch.minimum(torch.arange(Lx), Lx - torch.arange(Lx)); D = Lx // 2
    for b in betas:
        beta = b / 2; t0 = time.time(); prof = {}
        cfgs = [('cold', flux_bc(0, shp, xs))] + [(f'flux{k}', flux_bc(k, shp, xs)) for k in range(1, M // 2 + 1)]
        flip = flux_bc(0, shp, xs); flip[1][(xs[0] == 0) & (xs[1] == 0)] = torch.tensor([-1., 0, 0, 0]); cfgs.append(('flip', flip))
        if only_p1: cfgs = [cfgs[0], cfgs[-1]]
        assert float(G.polyakov(flip, 1)[0].mean()) < -0.99   # boundary holonomy of the flipped layer is -1
        for name, U in cfgs:
            for _ in range(300): sweep(U, z, beta, par, free)
            rp = []; rl = []
            for it in range(nsw):
                sweep(U, z, beta, par, free); lp = layer_plaq(U, z)
                rp.append(torch.stack([lp[d == kk].mean() for kk in range(1, D + 1)]))
                if name in ('cold', 'flip') and it % 2 == 0:
                    P1 = G.polyakov(G.smear(U, z, 0.1, 10), 1).mean((1, 2))      # (Lx,) profile in x0
                    rl.append(torch.stack([P1[d == kk].mean() for kk in range(0, D + 1)]))
            rp = torch.stack(rp).double(); nb = 20; bm = rp[: (nsw // nb) * nb].reshape(nb, -1, D).mean(1)
            prof[name] = (rp.mean(0), bm.std(0) / math.sqrt(nb))
            if rl:
                rl = torch.stack(rl).double(); n2 = len(rl); bl = rl[: (n2 // nb) * nb].reshape(nb, -1, D + 1).mean(1)
                prof[name + '_P1'] = (rl.mean(0), bl.std(0) / math.sqrt(nb))
        row = dict(mode='adv', bstd=b, Lx=Lx, M=M, sweeps=nsw)
        for name in [c[0] for c in cfgs[1:]]:
            dl = prof[name][0] - prof['cold'][0]; er = torch.sqrt(prof[name][1] ** 2 + prof['cold'][1] ** 2)
            row[name] = dict(delta=dl.tolist(), err=er.tolist())
        dp = prof['cold_P1'][0] - prof['flip_P1'][0]; ep = torch.sqrt(prof['cold_P1'][1] ** 2 + prof['flip_P1'][1] ** 2)
        row['P1'] = dict(cold=prof['cold_P1'][0].tolist(), flip=prof['flip_P1'][0].tolist(), diff=dp.tolist(), err=ep.tolist())
        row['sec'] = round(time.time() - t0, 1); res.append(row); print(json.dumps(row), flush=True)
        json.dump(res, open(out, 'w'), indent=1)


def mode_auto(out, betas, Ns, nsw):
    res = []
    for N in Ns:
        shp = (N,) * 4; xs = torch.stack(torch.meshgrid(*[torch.arange(n) for n in shp], indexing='ij'))
        par = xs.sum(0) % 2; z = torch.ones(shp, dtype=DT); free = torch.ones((4,) + shp, dtype=torch.bool)
        for b in betas:
            beta = b / 2; t0 = time.time()
            U = torch.zeros((4,) + shp + (4,), dtype=DT); U[..., 0] = 1
            for _ in range(400): sweep(U, z, beta, par, free)
            rec = []
            for _ in range(nsw):
                sweep(U, z, beta, par, free); Us = G.smear(U, z, 0.1, 10)
                rec.append(torch.stack([G.polyakov(Us, m).mean() for m in range(4)]))
            X = torch.stack(rec).double()                    # (T, 4) charged magnetisations
            row = dict(mode='auto', bstd=b, N=N, sweeps=nsw)
            for name, Y in (('charged', X), ('neutral', X ** 2)):
                Y = Y - Y.mean(0); var = (Y ** 2).mean(0); T = len(Y)
                rho = torch.stack([(Y[:T - t] * Y[t:]).mean(0) / var for t in range(0, min(200, T // 4))]).mean(1)
                tau = 0.5; W = None
                for t in range(1, len(rho)):
                    tau += float(rho[t])
                    if t >= 6 * tau: W = t; break
                row[name] = dict(tau_int=tau, window=W, rho=[float(v) for v in rho[:30]], mean=float(X.mean() if name == 'charged' else (X ** 2).mean()))
            row['sec'] = round(time.time() - t0, 1); res.append(row); print(json.dumps(row), flush=True)
            json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    out, mode = sys.argv[1], sys.argv[2]; betas = [float(v) for v in sys.argv[3].split(',')]; Lx = sys.argv[4]
    Lx = int(Lx) if mode != 'auto' else None
    if mode == 'bc': mode_bc(out, betas, Lx, int(sys.argv[5]), int(sys.argv[6]))
    elif mode == 'adv': mode_adv(out, betas, Lx, int(sys.argv[5]), int(sys.argv[6]))
    elif mode == 'p1': mode_adv(out, betas, Lx, int(sys.argv[5]), int(sys.argv[6]), only_p1=True)
    elif mode == 'auto': mode_auto(out, betas, [int(v) for v in sys.argv[4].split(',')], int(sys.argv[5]))
    else: mode_relax(out, betas, Lx, [int(v) for v in sys.argv[5].split(',')], int(sys.argv[6]), int(sys.argv[7]))
