"""Statement (S) of TwistedFluxInduction, tested where the twist free energy is resolvable (numerics, not a proof).

The induction to an area law needs a multiplicative transverse step F(2t) <= c F(t), F = -log z the (1,2) twist free
energy, for a doubling of a direction transverse to the twist plane. On the isotropic chain F was mostly ~0 +- 0.2
(unresolvable). Here the in-plane sides are fixed at P = 8 and x0 = 8, where F = O(1) at beta 2.5-2.6, and the
transverse side x3 = C is doubled: shapes (8, 8, 8, C) for C in {4, 6, 8, 12, 16, 24}. Ratio R(C) = F(2C)/F(C).
The earlier failure was C = 4 -> 8 at beta 2.5 and 2.6 (F(4) ~ 0, F(8) ~ 1.1 and 2.5).

Written before any run (2026-11-08):
 (16) R(C) <= 2.6 within 2 sigma for every C >= 6 at beta 2.5 and 2.6 (S holds with c = 2.6 once the transverse side
      is >= 6). R(4) > 2.6 at both beta, reproducing the side-4 failure.
 (17) Asymptotic extensivity: R(12) and R(8) lie in [1.6, 2.4] (F ~ linear in the transverse side, the flux-tube /
      magnetic-flux picture).
Usage: out betas Cs sweeps
"""
import os, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_flux_bootstrap as F


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; Cs = [int(c) for c in sys.argv[3].split(',')]
    nsw = int(sys.argv[4]); res = []
    for b in betas:
        for C in Cs:
            t0 = time.time(); lz, ez, pr = F.log_z((8, 8, 8, C), b, nsw)
            res.append(dict(bstd=b, C=C, shape=[8, 8, 8, C], logz=lz, err=ez, prof=pr, sweeps=nsw, sec=round(time.time() - t0, 1)))
            print('z', b, C, lz, ez, flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
