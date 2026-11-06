"""Are the non-convex blocks rare and isolated enough for a polymer expansion? (follow-up to yang_mills_block_bakry_emery)

Same per-block quantity: kappa_B = 2 + lambda_min(Hess beta S) over the 32 interior links of a 2^4 block with all
other links fixed (Bakry-Emery curvature, Ric = 2). A block is "bad" at threshold c if kappa_B < c * beta * lam0
(lam0 = 3, the free value per unit beta); c = 0 is plain Bakry-Emery failure. Two blocks interact iff they share a
plaquette: block offsets with |d|_inf = 1 and at most two nonzero coordinates (8 face + 24 edge = 32 neighbours).
Measured on N = 8 (4^4 blocks, periodic) with 16 configurations per beta:
  p_bad(c), the pair ratio r = P(B, B' both bad) / p_bad^2 over interacting pairs, and the Kotecky-Preiss-type
  activity margin  e * 32 * p_bad * r  (< 1 is a crude sufficient condition for a convergent cluster expansion of
  independent-ish bad blocks with 32 neighbours; r measures how far from independent they are).
Written before the run (2026-11-06):
 (1) p_bad(0) falls at least exponentially in beta over 3..6 and is < 0.3% at beta 5.
 (2) bad blocks are weakly correlated at beta 4: r <= 5.
 (3) the margin e*32*p_bad(0)*r is < 1 for beta >= 4.5, but for c = 1/2 (half the free convexity, the regime where
     the proved convex step keeps an O(1) constant) it is > 1 for every beta <= 6.
Usage: out N betas n_conf [sweeps_between]
"""
import os, sys, json, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_block_bakry_emery as BC
import torch
G = BC.G; DT = BC.DT


def block_coords(N):
    h = N // 4; out = []
    for c in range(16):
        cls = [(c >> d) & 1 for d in range(4)]
        for b in range(h ** 4):
            dig = [(b // h ** (3 - d)) % h for d in range(4)]
            out.append([2 * dig[d] + cls[d] for d in range(4)])
    return torch.tensor(out)


def neighbour_pairs(N):
    C = block_coords(N); M = N // 2
    idx = {tuple(c.tolist()): i for i, c in enumerate(C)}
    offs = []
    for o in range(81):
        d = [(o // 3 ** k) % 3 - 1 for k in range(4)]
        nz = sum(x != 0 for x in d)
        if 1 <= nz <= 2: offs.append(d)
    assert len(offs) == 32
    pairs = []
    for i, c in enumerate(C.tolist()):
        for d in offs:
            j = idx[tuple((c[k] + d[k]) % M for k in range(4))]
            if j > i: pairs.append((i, j))
    return torch.tensor(pairs)


def main():
    out = sys.argv[1]; N = int(sys.argv[2]); betas = [float(b) for b in sys.argv[3].split(',')]
    nconf = int(sys.argv[4]); between = int(sys.argv[5]) if len(sys.argv) > 5 else 20
    torch.manual_seed(1)
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij')); par = xs.sum(0) % 2
    P = neighbour_pairs(N); z = G.twist(N).to(DT); lam0 = 3.0; res = []
    for b in betas:
        beta = b / 2; t0 = time.time()
        U = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U[..., 0] = 1
        U[1][xs[1] == 0] = torch.tensor([0., 1, 0, 0], dtype=DT); U[2][xs[2] == 0] = torch.tensor([0., 0, 1, 0], dtype=DT)
        for _ in range(300): G.sweep(U, z, beta, None, par)
        K = []
        for ic in range(nconf):
            for _ in range(between): G.sweep(U, z, beta, None, par)
            K.append(2 + torch.linalg.eigvalsh(BC.block_hessians(U, z, b, N))[:, 0])
        K = torch.stack(K)                                   # (nconf, nblocks)
        row = dict(N=N, bstd=b, nblocks=int(K.numel()), npairs=int(P.shape[0] * nconf), sec=None)
        for c in (0.0, 0.25, 0.5):
            bad = (K < c * b * lam0).double(); p = float(bad.mean())
            pb = float((bad[:, P[:, 0]] * bad[:, P[:, 1]]).mean())
            r = pb / p ** 2 if p > 0 else None
            row[f'c{c}'] = dict(p_bad=p, p_pair=pb, r=r, margin=(math.e * 32 * p * r) if r is not None else 0.0)
        row['kappa_q'] = [float(torch.quantile(K.flatten(), q)) for q in (0.001, 0.01, 0.5)]
        row['sec'] = round(time.time() - t0, 1)
        res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
