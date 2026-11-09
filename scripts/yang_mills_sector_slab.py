"""Does the flux-sector difference on a transverse cut scale like a string (L) or a volume (L^3)?

Box L^4, twist in the (1,2) plane. The cut for doubling direction 3 is a slab x3 = const. Its plaquettes are those in
planes (0,3), (1,3), (2,3): 3 L^3 of them. For these plaquettes:
- the twisted expectation is translation-invariant (they are never in the twist stack, which can be moved anywhere by a
  change of variables);
- the sector difference is exactly <O>_0 - <O>_e = 2 z (<O>_tw - <O>) / (1 - z^2).
So the slab sum is S(L) = 2 z D / (1 - z^2), where D = (1/L) sum_box (<P>_tw - <P>) over those planes, from one twisted
and one untwisted run (batched, B = 2), and z comes from F.log_z.

The transverse step costs about the integral of S over the split/join path (TwistedFluxBasis, GAP §12). The area law
needs that cost to be o(L^2). The elementary bound is O(L^3). A delocalised flux string predicts O(L).
Even L only, because the checkerboard update needs even periodic sizes.

Written 2026-11-09, before any run:
 (22) At beta 2.3 and 2.4, with L = 4, 6, 8: the scaling exponent p of |S| ~ L^p, from a fit over L = 4..8, is below 2
      at both beta (sub-area), and S/L^3 decreases from L = 4 to L = 8. My central guess is p ~ 1.
Usage: out betas Ls sweeps
"""
import os, sys, json, time, math
import torch
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_flux_bootstrap as F


def slab_diff(L, beta, nsw):
    shp = (L,) * 4; B = 2; one = torch.ones((B,) + shp, dtype=F.DT); sh = F.Shift(shp)
    st = one.clone(); st[1, :, 0, 0, :] = -1.0                       # replica 0 untwisted, replica 1 twisted
    w = {p: one for p in F.PLANES}; w[(1, 2)] = st
    obs = lambda U: (sum(F.plaq(U, m, 3, sh).sum((1, 2, 3, 4)) for m in range(3)) / L).tolist()
    mu, er = F.run(shp, B, [(w, sh)], beta, nsw, obs)
    return float(mu[1] - mu[0]), float(math.hypot(er[0], er[1])), mu.tolist()


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; Ls = [int(x) for x in sys.argv[3].split(',')]
    nsw = int(sys.argv[4]); res = []
    for b in betas:
        for L in Ls:
            t0 = time.time(); D, eD, raw = slab_diff(L, b, nsw); lz, ez, _ = F.log_z((L,) * 4, b, nsw)
            res.append(dict(bstd=b, L=L, D=D, eD=eD, slab=raw, logz=lz, elogz=ez, sweeps=nsw, sec=round(time.time() - t0, 1)))
            print('S', b, L, D, eD, lz, ez, flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
