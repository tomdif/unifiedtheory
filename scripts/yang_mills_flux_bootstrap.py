"""Does the electric-flux recursion close as an induction on box size? Constants along the isotropic doubling chain.

Chain (twist plane (1,2), dims (x0, x1, x2, x3)):
  s0 = (L, L, L, L) -> s1 = (L, 2L, L, L) -> s2 = (L, 2L, 2L, L) -> s3 = (2L, 2L, 2L, L) -> s4 = (2L)^4.
Steps 1, 2 double in-plane directions (TwistedFluxRecursion): y(s') <= K y(s)^2, K = Z_0(s)^2 / Z_0(s'),
Z_0 = Z (1 + z)/2. Steps 3, 4 double transverse directions (TwistedFluxThermal): y(s') <= (K_B - z^2)/(K_B + z^2),
K_B = Z_tw(s)^2 / Z_tw(s'), and with K_B = 1 + kappa this is <= 4 y + kappa.

Measured per (beta, L):
  log z(s_i), i = 0..4: twist coefficient c on the (1,2) plaquettes at x1 = x2 = 0, log z = -beta int_{-1}^{1} <sum_stack P> dc,
    7 Gauss-Legendre nodes.
  log Kper_i = 2 log Z(s_i) - log Z(s_{i+1}), i = 0..3, by split/join interpolation on s_{i+1}: the plaquettes in planes
    containing the doubled direction d with base layer x_d in {h - 1, 2h - 1} have weight (1 - lam) as joined and lam as
    split (the d-neighbour of h - 1 becomes 0 and of 2h - 1 becomes h). lam = 1 is two decoupled copies of s_i.
    log Kper = beta int_0^1 <sum (P_split - P_joined)> dlam, 7 nodes. Bulk free energy cancels exactly.
  Then log K_i = log Kper_i + 2 log((1 + z_i)/2) - log((1 + z_{i+1})/2) (in-plane) and
  log K_B,i = log Kper_i + 2 log z_i - log z_{i+1} (transverse).

Structural remark (written before any run, 2026-11-07). The transverse bound is additive: y' <= 4y + kappa with kappa >= the
untwisted thermal free energy, of order e^{-m L} in a gapped box. The true flux ratio is y ~ e^{-sigma L^2}. So the chain
with additive kappa can at best give y(L) <~ e^{-m L}, which feeds Tomboulis-Yaffe only with a vanishing string tension.
An area law needs a MULTIPLICATIVE transverse step. The natural candidate is z(s') >= z(s)^2 under transverse doubling
(F_tw = -log z at most doubles when the twist sheet doubles), which gives y' <= 2y/(1 + y^2) <= 2y.

Written before any run (2026-11-07):
 (12) Bug checks: log Kper_i >= 0 within 2 sigma (Z(2t) <= Z(t)^2 for T >= 0). In-plane steps: y(s_{i+1}) <= K_i y(s_i)^2
      within 2 sigma (a theorem). The lam = 1 half-lattice plaquette equals that of a standalone s_i within 2 sigma.
 (13) Candidate lemma: transverse superadditivity log z(s3) >= 2 log z(s2) and log z(s4) >= 2 log z(s3) holds at every
      beta and L measured (my guess: holds, with F_tw roughly constant when confined and doubling when not).
 (14) Original route (additive kappa): the chained bound Y(2L), from y(s0) and the four measured constants, is below
      y(s0) (contraction) at beta 2.4 for L = 6, and not at beta 2.6 for any L <= 6. At beta 2.4 the transverse kappas
      fall from L = 4 to L = 6; at 2.6 they do not (torelon-dominated, L sqrt(sigma) < 1.2).
Usage: out betas Ls sweeps
"""
import os, sys, json, math, time
import torch
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_band_targets as BT
DT = BT.DT; qmul, qc = BT.qmul, BT.qc
X, W = [torch.tensor(a, dtype=torch.float64) for a in __import__('numpy').polynomial.legendre.leggauss(7)]
PLANES = [(m, n) for m in range(4) for n in range(m + 1, 4)]


class Shift:
    """Forward/backward neighbour maps on tensors (B,) + shp (+ (4,)); lattice direction m is tensor dim m + 1.
    Direction d may be split into two periodic halves of length h."""
    def __init__(self, shp, d=None, h=None):
        self.d = d
        if d is not None:
            n = shp[d]; i = torch.arange(n); f = (i + 1) % n; f[h - 1] = 0; f[n - 1] = h
            b = torch.empty_like(f); b[f] = i; self.f, self.b = f, b

    def __call__(self, t, m, k=1):
        if self.d is not None and m == self.d: return torch.index_select(t, m + 1, self.f if k == 1 else self.b)
        return torch.roll(t, -k, dims=m + 1)


def plaq(U, m, n, sh):
    return qmul(qmul(qmul(U[m], sh(U[n], m)), qc(sh(U[m], n))), qc(U[n]))[..., 0]


def staple(U, m, terms):
    tot = 0.
    for w, sh in terms:
        for n in range(4):
            if n == m: continue
            wt = w.get((min(m, n), max(m, n)))
            if wt is None: continue
            up = qmul(qmul(sh(U[n], m), qc(sh(U[m], n))), qc(U[n])) * wt[..., None]
            bk = qmul(qmul(qc(sh(U[n], m)), qc(U[m])), U[n]) * wt[..., None]
            tot = tot + up + sh(bk, n, -1)
    return tot


def sweep(U, terms, beta, par):
    for heat in (True, False, False):
        for m in range(4):
            for p in (0, 1):
                K = beta * qc(staple(U, m, terms)); nrm = K.norm(dim=-1)        # beta = beta_std: weight exp(beta_std Re tr/2)
                mask = (par == p) & (nrm > 1e-12); Kd = K[mask] / nrm[mask][:, None]
                if heat:
                    a0 = BT.kp(nrm[mask]); v = torch.randn((a0.numel(), 3), dtype=DT); v = v / v.norm(dim=-1, keepdim=True)
                    new = qmul(torch.cat([a0[:, None], torch.sqrt(torch.clamp(1 - a0 ** 2, min=0))[:, None] * v], -1), Kd)
                else:
                    new = qmul(qmul(Kd, qc(U[m][mask])), Kd)
                U[m][mask] = new / new.norm(dim=-1, keepdim=True)


def binned(rec, nb=20):
    a = torch.tensor(rec, dtype=torch.float64); b = torch.stack([q.mean(0) for q in torch.tensor_split(a, nb)])
    return b.mean(0), b.std(0) / math.sqrt(nb)


def run(shp, B, terms, beta, nsw, obs):
    """B independent replicas (one per integration node) updated together; obs(U) returns a length-B list."""
    xs = torch.stack(torch.meshgrid(*[torch.arange(n) for n in shp], indexing='ij')); par = (xs.sum(0) % 2).expand((B,) + shp)
    U = torch.zeros((4, B) + shp + (4,), dtype=DT); U[..., 0] = 1
    for _ in range(300): sweep(U, terms, beta, par)
    rec = []
    for _ in range(nsw): sweep(U, terms, beta, par); rec.append(obs(U))
    return binned(rec)


def bfield(shp, vals):
    return torch.tensor(vals, dtype=DT).view((-1,) + (1,) * 4).expand((len(vals),) + shp).contiguous()


def log_z(shp, beta, nsw):
    B = len(X); one = torch.ones((B,) + shp, dtype=DT); sh = Shift(shp)
    st = one.clone(); st[:, :, 0, 0, :] = bfield(shp, X.tolist())[:, :, 0, 0, :]
    w = {p: one for p in PLANES}; w[(1, 2)] = st
    mu, er = run(shp, B, [(w, sh)], beta, nsw, lambda U: plaq(U, 1, 2, sh)[:, :, 0, 0, :].sum((1, 2)).tolist())
    return float(-beta * (W * mu).sum()), float(beta * ((W * er) ** 2).sum().sqrt()), mu.tolist()


def log_kper(shp, d, beta, nsw, half_check=False):
    h = shp[d] // 2; shJ, shS = Shift(shp), Shift(shp, d, h)
    xd = torch.arange(shp[d]).view([-1 if k == d else 1 for k in range(4)]).expand(shp)
    bnd = ((xd == h - 1) | (xd == 2 * h - 1)).to(DT); dpl = [p for p in PLANES if d in p]
    lam = ((X + 1) / 2).tolist(); B = len(lam); one = torch.ones((B,) + shp, dtype=DT)
    L = bfield(shp, lam) * bnd
    wJ = {p: (one - L if p in dpl else one) for p in PLANES}; wS = {p: L for p in dpl}
    def obs(U): return sum(((plaq(U, *p, shS) - plaq(U, *p, shJ)) * bnd).sum((1, 2, 3, 4)) for p in dpl).tolist()
    mu, er = run(shp, B, [(wJ, shJ), (wS, shS)], beta, nsw, obs)
    extra = None
    if half_check:   # lam = 1 exactly: mean plaquette of the first half vs a standalone half lattice
        o1 = torch.ones((1,) + shp, dtype=DT); b1 = bnd.expand((1,) + shp)
        wJ1 = {p: (o1 - b1 if p in dpl else o1) for p in PLANES}; wS1 = {p: b1 for p in dpl}; sel = xd < h
        mh, eh = run(shp, 1, [(wJ1, shJ), (wS1, shS)], beta, nsw,
                     lambda U: [float(sum(plaq(U, *p, shS)[0][sel].mean() for p in PLANES) / 6)])
        hs = list(shp); hs[d] = h; hs = tuple(hs); sh0 = Shift(hs); o = torch.ones((1,) + hs, dtype=DT)
        ms, es = run(hs, 1, [({p: o for p in PLANES}, sh0)], beta, nsw,
                     lambda U: [float(sum(plaq(U, *p, sh0).mean() for p in PLANES) / 6)])
        extra = dict(half=[float(mh[0]), float(eh[0])], standalone=[float(ms[0]), float(es[0])])
    return float(beta * (W / 2 * mu).sum()), float(beta * ((W / 2 * er) ** 2).sum().sqrt()), mu.tolist(), extra


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; Ls = [int(x) for x in sys.argv[3].split(',')]
    nsw = int(sys.argv[4]); res = []
    for L in Ls:
        sh = [(L, L, L, L), (L, 2 * L, L, L), (L, 2 * L, 2 * L, L), (2 * L, 2 * L, 2 * L, L), (2 * L,) * 4]; dirs = [1, 2, 0, 3]
        for b in betas:
            t0 = time.time(); row = dict(L=L, bstd=b, sweeps=nsw, shapes=sh, dirs=dirs, logz=[], logkper=[])
            for i, s in enumerate(sh):
                lz, ez, pr = log_z(s, b, nsw); row['logz'].append(dict(v=lz, e=ez, prof=pr)); print('z', L, b, s, lz, ez, flush=True)
            for i in range(4):
                lk, ek, pr, ex = log_kper(sh[i + 1], dirs[i], b, nsw, half_check=(i == 0))
                row['logkper'].append(dict(v=lk, e=ek, prof=pr, check=ex)); print('K', L, b, i, lk, ek, ex, flush=True)
            row['sec'] = round(time.time() - t0, 1); res.append(row); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
