"""How often is a side-2 block of 4D SU(2) lattice YM inside the convex regime? (Bakry-Emery per block)

Context (Twisted/README, "Lean: TwistedHolderStep", "Lean: TwistedTiltBL"). The proved convex RG step and the
localization bound alpha_t <= 1/(lam + t) need an action whose Hessian is >= lam. On SU(2)^links the right local
quantity is the Bakry-Emery curvature Ric + Hess(beta S), Ric = 2 on the unit 3-sphere (Haar metric).
For each thermalized configuration and each 2^4 block, condition on every link except the 32 links with both
endpoints in the block (Dirichlet data: no gauge zero modes, since every block site touches a fixed link). Compute
the 96 x 96 Riemannian Hessian H_B of beta S in the geodesic chart U_l -> exp(eps_l) U_l and record
  lam_B = lambda_min(H_B),  kappa_B = lam_B + 2 (Bakry-Emery),  lam_B / (beta lam0),
where lam0 = lambda_min of the free block Hessian (U = 1, per unit beta). beta S = beta_std sum_p (1 - (1/2) tr U_p).
Blocks are processed in 16 parity classes, so that blocks in one class share no plaquette and the Hessian of the
class restricted to its links is exactly block diagonal (one batch of 96 Hessian-vector products per class).
Written before any run (2026-11-05):
 (1) lam_B/(beta lam0) has median -> 1 with spread ~ beta^{-1/2} at weak coupling (beta_std >= 8).
 (2) the fraction of blocks with kappa_B <= 0 is > 5% at beta_std 2.5 and < 1% at beta_std 8, decaying
     faster than any power of 1/beta (rare large-field blocks).
 (3) the fraction with lam_B < lam0 beta / 2 (half the free convexity) does NOT vanish at beta_std 2.5-4: the
     physical window is not uniformly convex at block scale 2, so a large-field / polymer bookkeeping is needed.
Usage: out N betas n_conf [sweeps_between]
"""
import os, sys, json, math, time
os.environ.setdefault('OMP_NUM_THREADS', '4')
import torch
torch.set_num_threads(4)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_sl_gpu as G
from torch.func import grad, jvp, vmap

DT = torch.float64
DEV = os.environ.get('YM_DEV', 'cpu')
torch.set_default_device(DEV)
G.DT = DT
G.dev = DEV
G.CJ = torch.tensor([1., -1, -1, -1], dtype=DT)


def qexp2(v):
    """exp of a pure quaternion, exact to second order (enough for the Hessian at eps = 0)."""
    return torch.cat([1 - 0.5 * (v * v).sum(-1, keepdim=True), v], -1)


def action(U, z, beta):
    return beta * sum((1 - P).sum() for P in G.plaq_re(U, z).values())


def interior_dirs(N, cls):
    """96 direction tensors (4,N,N,N,N,3): dof k = (m, offset o with o_m = 0, a), placed in every block of class cls."""
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij'))
    blk = xs // 2; off = xs % 2
    incls = torch.ones((N,) * 4, dtype=torch.bool)
    for d in range(4): incls &= (blk[d] % 2 == cls[d])
    dirs = []; labels = []
    for m in range(4):
        for o in range(16):
            ov = [(o >> d) & 1 for d in range(4)]
            if ov[m]: continue
            mask = incls.clone()
            for d in range(4): mask &= (off[d] == ov[d])
            for a in range(3):
                E = torch.zeros((4,) + (N,) * 4 + (3,), dtype=DT); E[m, ..., a][mask] = 1
                dirs.append(E); labels.append((m, o, a))
    return torch.stack(dirs), incls, blk


def block_hessians(U, z, beta, N):
    """Return list of (96x96 Hessian) for every block, all 16 classes."""
    def f(E):
        Up = torch.stack([G.qmul(qexp2(E[m]), U[m]) for m in range(4)])
        return action(Up, z, beta)
    g = grad(f); E0 = torch.zeros((4,) + (N,) * 4 + (3,), dtype=DT)
    out = []
    for c in range(16):
        cls = [(c >> d) & 1 for d in range(4)]
        D, incls, blk = interior_dirs(N, cls)
        HV = vmap(lambda e: jvp(g, (E0,), (e,))[1])(D)          # (96, 4,N,N,N,N,3)
        # column k for block b = HV[k] restricted to block b's interior dofs = sum over the same pattern D[j]
        # H[b][j,k] = sum over block b sites of D[j] * HV[k]
        bid = (blk[0] // 2) * (N // 4) ** 3 + (blk[1] // 2) * (N // 4) ** 2 + (blk[2] // 2) * (N // 4) + blk[3] // 2
        nb = (N // 4) ** 4
        oneh = torch.zeros((nb,) + (N,) * 4, dtype=DT)
        oneh[bid[incls], incls.nonzero(as_tuple=True)[0], incls.nonzero(as_tuple=True)[1],
             incls.nonzero(as_tuple=True)[2], incls.nonzero(as_tuple=True)[3]] = 1
        # H[b,j,k] = sum_{m,x,a} oneh[b,x] D[j,m,x,a] HV[k,m,x,a]
        H = torch.einsum('bwxyz,jmwxyza,kmwxyza->bjk', oneh, D, HV)
        out.append(0.5 * (H + H.transpose(1, 2)))
    return torch.cat(out)


def main():
    out = sys.argv[1]; N = int(sys.argv[2]); betas = [float(b) for b in sys.argv[3].split(',')]
    nconf = int(sys.argv[4]); between = int(sys.argv[5]) if len(sys.argv) > 5 else 20
    assert N % 4 == 0
    torch.manual_seed(0)
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij')); par = xs.sum(0) % 2
    z1 = torch.ones((N,) * 4, dtype=DT)
    U1 = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U1[..., 0] = 1
    H0 = block_hessians(U1, z1, 1.0, N); lam0 = float(torch.linalg.eigvalsh(H0)[:, 0].min())
    lam0max = float(torch.linalg.eigvalsh(H0)[:, -1].max())
    print(json.dumps(dict(kind='free', N=N, lam0=lam0, lam0max=lam0max)), flush=True)
    res = [dict(kind='free', N=N, lam0=lam0, lam0max=lam0max)]
    z = G.twist(N).to(DT)
    for b in betas:
        beta = b / 2; t0 = time.time()
        U = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U[..., 0] = 1
        U[1][xs[1] == 0] = torch.tensor([0., 1, 0, 0], dtype=DT); U[2][xs[2] == 0] = torch.tensor([0., 0, 1, 0], dtype=DT)
        for _ in range(300): G.sweep(U, z, beta, None, par)
        lams = []; plaq = []
        for ic in range(nconf):
            for _ in range(between): G.sweep(U, z, beta, None, par)
            H = block_hessians(U, z, b, N)
            lams.append(torch.linalg.eigvalsh(H)[:, 0])
            plaq.append(float(torch.stack(list(G.plaq_re(U, z).values())).mean()))
        L = torch.cat(lams); r = L / (b * lam0)
        row = dict(kind='beta', N=N, bstd=b, nblocks=int(L.numel()), plaq=sum(plaq) / len(plaq), lam0=lam0,
                   frac_BE_bad=float((L + 2 <= 0).double().mean()), frac_hess_neg=float((L <= 0).double().mean()),
                   frac_below_half=float((r < 0.5).double().mean()),
                   ratio_q=[float(torch.quantile(r, q)) for q in (0.001, 0.01, 0.1, 0.5, 0.9)],
                   ratio_std=float(r.std()), min_kappa=float((L + 2).min()), sec=round(time.time() - t0, 1))
        res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
