"""U(1) negative control for the sector-slab scaling test (GAP §13-14).

Compact U(1) lattice gauge theory, action beta sum_p c_p cos(theta_p), with a Z2 twist (c = -1) on the (1,2) plaquettes
at x1 = x2 = 0. The quantities are the same as for SU(2) (scripts/yang_mills_sector_slab.py): log z by 7-node Gauss
integration over c, and the slab sector difference S = 2 z D / (1 - z^2), where D = (1/L) sum_box (<cos>_tw - <cos>)
over planes (0,3), (1,3), (2,3). Exact heatbath: each link's conditional law is von Mises, plus one overrelaxation per
sweep. U(1) has a confining phase for beta < ~1.0 and a Coulomb phase above it.

Written 2026-11-09, before any run:
 (23) Coulomb phase, beta = 1.5, L = 4, 6, 8: y does not decay with L (y(8) >= y(4)/2), and |S| grows at least like
      L^2 (fitted p >= 2). Confined phase, beta = 0.8: y(4) < 0.1. This checks that the test can register the
      abelian (deconfined) behaviour that the hypothesis must exclude.
Usage: out betas Ls sweeps
"""
import os, sys, json, math, time
import numpy as np
import torch
DT = torch.float64
X, W = [torch.tensor(a, dtype=DT) for a in np.polynomial.legendre.leggauss(7)]
PLANES = [(m, n) for m in range(4) for n in range(m + 1, 4)]


def sh(t, m, k=1): return torch.roll(t, -k, dims=m + 1)


def plaq(T, m, n): return T[m] + sh(T[n], m) - sh(T[m], n) - T[n]


def staple(T, m, w):
    """Complex A with local action beta Re(e^{i theta_m(x)} A)."""
    A = 0.
    for n in range(4):
        if n == m: continue
        c = w[(min(m, n), max(m, n))]
        up = torch.exp(1j * (sh(T[n], m) - sh(T[m], n) - T[n])) * c
        cb = sh(c, n, -1)
        dn = torch.exp(1j * (-sh(sh(T[n], m), n, -1) - sh(T[m], n, -1) + sh(T[n], n, -1))) * cb
        A = A + up + dn
    return A


def sweep(T, w, beta, par):
    for heat in (True, False):
        for m in range(4):
            for p in (0, 1):
                A = staple(T, m, w); mask = par == p; a = A[mask]
                k = beta * a.abs(); phi = torch.angle(a)
                if heat:
                    vm = torch.distributions.VonMises(torch.zeros_like(k), k.clamp(min=1e-8)).sample()
                    T[m][mask] = vm - phi
                else:
                    T[m][mask] = -2 * phi - T[m][mask]


def run(L, B, w, beta, nsw, obs):
    shp = (L,) * 4
    xs = torch.stack(torch.meshgrid(*[torch.arange(L)] * 4, indexing='ij')); par = (xs.sum(0) % 2).expand((B,) + shp)
    T = torch.zeros((4, B) + shp, dtype=DT)
    for _ in range(300): sweep(T, w, beta, par)
    rec = []
    for _ in range(nsw): sweep(T, w, beta, par); rec.append(obs(T))
    a = torch.tensor(rec, dtype=DT); b = torch.stack([q.mean(0) for q in torch.tensor_split(a, 20)])
    return b.mean(0), b.std(0) / math.sqrt(20)


def weights(L, vals):
    B = len(vals); one = torch.ones((B,) + (L,) * 4, dtype=DT); st = one.clone()
    st[:, :, 0, 0, :] = torch.tensor(vals, dtype=DT).view(-1, 1, 1)
    w = {p: one for p in PLANES}; w[(1, 2)] = st; return w


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; Ls = [int(x) for x in sys.argv[3].split(',')]
    nsw = int(sys.argv[4]); res = []
    for b in betas:
        for L in Ls:
            t0 = time.time()
            w = weights(L, X.tolist())
            mu, er = run(L, len(X), w, b, nsw, lambda T: torch.cos(plaq(T, 1, 2))[:, :, 0, 0, :].sum((1, 2)).tolist())
            lz = float(-b * (W * mu).sum()); ez = float(b * ((W * er) ** 2).sum().sqrt())
            w2 = weights(L, [1.0, -1.0])
            m2, e2 = run(L, 2, w2, b, nsw, lambda T: (sum(torch.cos(plaq(T, m, 3)).sum((1, 2, 3, 4)) for m in range(3)) / L).tolist())
            D = float(m2[1] - m2[0]); eD = float(math.hypot(e2[0], e2[1]))
            res.append(dict(bstd=b, L=L, logz=lz, elogz=ez, D=D, eD=eD, sweeps=nsw, sec=round(time.time() - t0, 1)))
            print('U1', b, L, lz, ez, D, eD, flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
