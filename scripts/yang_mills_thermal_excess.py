"""The in-plane constant K-bar as a thermal excess: a cheap direct test.

Step 0 of the flux-bootstrap chain doubles direction 1 of an L^4 box. With direction 1 as time and the spatial box
L^3 fixed, Z(t) = Tr T^t, and log Kper = 2 log Z(L) - log Z(2L). Write P(t) = sum_{i>0} e^{-t(E_i - E_0)} for the
untwisted thermal excess at temperature 1/t. Then, exactly (TwistedThermalExcess.lean):
  log(1 + P(L)) <= log Kper <= 2 log(1 + P(L)),
and with 0 <= z, z' <= 1 the in-plane constant obeys K <= 2 Kper. So K-bar is equivalent to the thermal excess at T = 1/L
being bounded. Benchmarks:
  - Free massless gluons (6 dof, Stefan-Boltzmann at LT = 1): log(1 + P) ~ pi^2/15 ~ 0.66, log Kper ~ 1.23.
  - Gapped box: P ~ e^{-mL} -> 0.
  - Small physical box at weak coupling: the flat-connection (toron) and electric-flux levels have spacing ~ g^2 / L, so
    P grows like a power of 1/g^2 = beta/4 at fixed lattice L. So K-bar cannot hold uniformly in beta at a fixed
    lattice L, only above a physical size L0.

Written 2026-11-09, before any run of this script:
 (18) Gapped decrease: log Kper_0 at beta 2.5, L = 8 is below 1.0 (previous: 2.66(22) at L = 4, 1.64(35) at L = 6).
 (19) Small-box growth: at L = 4, log Kper_0 increases with beta over 2.6, 3.0, 4.0, and log Kper_0(4.0) exceeds
      log Kper_0(2.6) by more than 1.0 (2 sigma).
Usage: out jobs sweeps   with jobs = "beta:L,beta:L,..."
"""
import os, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_flux_bootstrap as F


def main():
    out = sys.argv[1]; jobs = [(float(a), int(b)) for a, b in (j.split(':') for j in sys.argv[2].split(','))]
    nsw = int(sys.argv[3]); res = []
    for b, L in jobs:
        t0 = time.time(); lk, ek, pr, _ = F.log_kper((L, 2 * L, L, L), 1, b, nsw)
        res.append(dict(bstd=b, L=L, logkper0=lk, err=ek, prof=pr, sweeps=nsw, sec=round(time.time() - t0, 1)))
        print('K0', b, L, lk, ek, flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
