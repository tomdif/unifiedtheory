"""Block convexity at block side s = 2 and 4 on the same configurations: does coarse-graining average out the
non-convex region? (follow-up to yang_mills_block_bakry_emery / yang_mills_block_polymer)

Per block B of side s: all links fixed except those with both endpoints in B; lam_B = lambda_min of the Riemannian
Hessian of beta S in those links (geodesic chart), kappa_B = 2 + lam_B (Bakry-Emery). For s = 4 the block has
768 links (2304 dof), so lam_B is computed by Lanczos with full reorthogonalisation, batched over all blocks of a
parity class (their Hessians are exactly block diagonal), using Hessian-vector products of the lattice action.
The free value lam0(s) (U = 1, per unit beta) is computed the same way. Validation: s = 2 Lanczos against the dense
96 x 96 eigensolver of yang_mills_block_bakry_emery on one configuration (YM_DENSE_CHECK=1; max error 1e-13 at N 8).
Blocks of side 4 have 16 deep-interior sites whose gauge directions are exact zero modes; they are removed by a
complete axial gauge inside the block (see class_layout). Device: YM_DEV=cuda.
Written before the run (2026-11-06):
 (1) lam0(4) < lam0(2) = 3 (Dirichlet: lowest mode ~ 1/s^2), so Ric = 2 is relatively larger at s = 4.
 (2) at beta_std 3-4 the side-4 BE-bad fraction is >= the probability that at least one of its 16 side-2 sub-blocks
     is BE-bad: lambda_min of a larger block is dominated by its worst region (no averaging). The ratio
     lam_B/(beta lam0(s)) has a LOWER median at s = 4 than at s = 2 for every beta.
 (3) hence the convex window moves to larger beta when the block grows: the beta where p_bad(BE) reaches 1% is
     higher at s = 4 than at s = 2 (4.2 at s = 2, from the side-2 scan).
Usage: out N betas n_conf sides [k_lanczos] [sweeps_between]
"""
import os, sys, json, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_block_bakry_emery as BC
import torch
from torch.func import grad, jvp
G = BC.G; DT = BC.DT


def class_layout(N, s, cls):
    """mask (4,N^4) of interior links of class-cls blocks of side s; bid (N^4) block id or -1; number of blocks."""
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij'))
    blk = xs // s; off = xs % s; h = N // (2 * s)
    incls = torch.ones((N,) * 4, dtype=torch.bool)
    for d in range(4): incls &= (blk[d] % 2 == cls[d])
    bid = torch.zeros((N,) * 4, dtype=torch.long)
    for d in range(4): bid = bid * h + blk[d] // 2
    bid = torch.where(incls, bid, torch.full_like(bid, h ** 4))       # dummy index h^4 for outside
    mask = torch.stack([incls & (off[m] <= s - 2) for m in range(4)])
    # complete axial gauge inside the block: for every deep-interior site x (offset 1..s-2 in all directions) the
    # link (x - e0 -> x) is held fixed. Triangular in x_0, Haar Faddeev-Popov factor 1: the conditional law of the
    # remaining links is the gauge-fixed conditional measure, and the interior gauge zero modes are removed.
    deep = incls.clone()
    for d in range(4): deep &= (off[d] >= 1) & (off[d] <= s - 2)
    mask[0] &= ~torch.roll(deep, -1, dims=0)
    return mask, bid, h ** 4


def make_hvp(U, z, beta, N):
    def f(E):
        Up = torch.stack([G.qmul(BC.qexp2(E[m]), U[m]) for m in range(4)])
        return BC.action(Up, z, beta)
    g = grad(f); E0 = torch.zeros((4,) + (N,) * 4 + (3,), dtype=DT)
    return lambda v: jvp(g, (E0,), (v,))[1]


def lanczos_min(hvp, mask, bid, nb, k, gen):
    m3 = mask[..., None].to(DT)
    def bdot(a, b):                                       # per-block inner products, (nb,)
        site = (a * b).sum(-1).sum(0)                     # (N^4)
        return torch.zeros(nb + 1, dtype=DT).index_add_(0, bid.flatten(), site.flatten())[:nb]
    def bcast(sb):                                        # (nb,) -> lattice field (1,N^4,1)
        return torch.cat([sb, torch.zeros(1, dtype=DT)])[bid][None, ..., None]
    v = torch.randn((4,) + bid.shape + (3,), dtype=DT, generator=gen) * m3
    v = v * bcast(bdot(v, v).rsqrt())
    V = [v]; A = []; B = []; vprev = torch.zeros_like(v); bprev = torch.zeros(nb, dtype=DT)
    for j in range(k):
        w = hvp(V[-1]) * m3
        a = bdot(V[-1], w); A.append(a)
        w = w - bcast(a) * V[-1] - bcast(bprev) * vprev
        for _ in range(2):
            for q in V: w = w - bcast(bdot(q, w)) * q
        bn = bdot(w, w).sqrt()
        if j == k - 1: break
        dead = bn < 1e-8 * (a.abs() + 1)                  # invariant subspace found: restart with a fresh vector
        if bool(dead.any()):
            r = torch.randn(w.shape, dtype=DT, generator=gen) * m3
            for _ in range(2):
                for q in V: r = r - bcast(bdot(q, r)) * q
            r = r * bcast(bdot(r, r).clamp_min(1e-300).rsqrt())
            dsite = bcast(dead.to(DT))
            w = torch.where(dsite > 0, r, w * bcast(1 / torch.where(dead, torch.ones_like(bn), bn)))
            bn = torch.where(dead, torch.zeros_like(bn), bn)
        else:
            w = w * bcast(1 / bn)
        B.append(bn); vprev = V[-1]; bprev = bn; V.append(w)
    A = torch.stack(A, 1); Bm = torch.stack(B, 1) if B else torch.zeros(nb, 0, dtype=DT)
    T = torch.diag_embed(A) + torch.diag_embed(Bm, 1) + torch.diag_embed(Bm, -1)
    return torch.linalg.eigvalsh(T)[:, 0]


def all_blocks(U, z, beta, N, s, k, gen):
    hvp = make_hvp(U, z, beta, N); out = []
    for c in range(16):
        mask, bid, nb = class_layout(N, s, [(c >> d) & 1 for d in range(4)])
        out.append(lanczos_min(hvp, mask, bid, nb, k, gen))
    return torch.cat(out)


def main():
    out = sys.argv[1]; N = int(sys.argv[2]); betas = [float(b) for b in sys.argv[3].split(',')]
    nconf = int(sys.argv[4]); sides = [int(v) for v in sys.argv[5].split(',')]
    k = int(sys.argv[6]) if len(sys.argv) > 6 else 60; between = int(sys.argv[7]) if len(sys.argv) > 7 else 20
    torch.manual_seed(2); gen = torch.Generator(device=BC.DEV).manual_seed(3)
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij')); par = xs.sum(0) % 2
    z1 = torch.ones((N,) * 4, dtype=DT); U1 = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U1[..., 0] = 1
    lam0 = {s: float(all_blocks(U1, z1, 1.0, N, s, k, gen).min()) for s in sides}
    res = [dict(kind='free', N=N, lam0={str(s): v for s, v in lam0.items()}, k=k)]
    print(json.dumps(res[0]), flush=True)
    z = G.twist(N).to(DT)
    for b in betas:
        beta = b / 2; t0 = time.time()
        U = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U[..., 0] = 1
        U[1][xs[1] == 0] = torch.tensor([0., 1, 0, 0], dtype=DT); U[2][xs[2] == 0] = torch.tensor([0., 0, 1, 0], dtype=DT)
        for _ in range(300): G.sweep(U, z, beta, None, par)
        L = {s: [] for s in sides}; dense_check = None
        for ic in range(nconf):
            for _ in range(between): G.sweep(U, z, beta, None, par)
            for s in sides: L[s].append(all_blocks(U, z, b, N, s, k, gen))
            if ic == 0 and 2 in sides and os.environ.get('YM_DENSE_CHECK'):
                dn = torch.linalg.eigvalsh(BC.block_hessians(U, z, b, N))[:, 0]
                dense_check = float((dn - L[2][0]).abs().max())
        row = dict(kind='beta', N=N, bstd=b, dense_vs_lanczos_maxerr=dense_check)
        for s in sides:
            Ls = torch.cat(L[s]); r = Ls / (b * lam0[s])
            row[f's{s}'] = dict(nblocks=int(Ls.numel()), frac_BE_bad=float((Ls + 2 <= 0).double().mean()),
                                frac_hess_neg=float((Ls <= 0).double().mean()),
                                ratio_q=[float(torch.quantile(r, q)) for q in (0.01, 0.1, 0.5, 0.9)],
                                kappa_q=[float(torch.quantile(Ls + 2, q)) for q in (0.01, 0.1, 0.5)])
        row['sec'] = round(time.time() - t0, 1)
        res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
