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
Results 2026-11-09: L4: 3.73(23) at 2.6, 2.46(22) at 3.0, 5.10(47) at 4.0; beta 2.5 L8: 1.25(55). (18) fails on the
central value (1.25 > 1.0, 0.5 sigma). (19) fails: not monotone (drop 2.6 -> 3.0 at 4 sigma).
Added 2026-11-09 after those results, before any further run. Hypothesis: log Kper_0 is set by T/T_c with T = 1/L
(SU(2) beta_c(N_t): 4 -> 2.30, 6 -> 2.43, 8 -> 2.51, so N_t^c(2.5) ~ 7.7, N_t^c(2.6) ~ 10-11). All small values so far
(beta 2.4 L8: 0.07, beta 2.3 L6: 0.40) are the only boxes with L > N_t^c. If true, L0(beta) = N_t^c(beta) = 1/(a T_c),
which scales with the physical length 1/T_c.
 (20) beta 2.5, L = 12 (T/T_c ~ 0.65): log Kper_0 < 0.8. beta 2.6, L = 12 (T/T_c ~ 0.9): log Kper_0 < 1.0.
      beta 2.6, L = 8 (T/T_c ~ 1.3): log Kper_0 > 1.5.
Results 2026-11-09: beta 2.5 L12: -0.08(99) [< 0.8 holds, not significant]; beta 2.6 L12: 2.78(102) [< 1.0 FAILS,
1.8 sigma]; beta 2.6 L8: 2.29(80) [> 1.5 holds, 1 sigma]. (20) fails as written. Errors at L = 12 (~1) are too large to
discriminate; the observable sums ~6 L^3 boundary plaquettes, so variance grows like L^3.
Added 2026-11-09 after (20), before any further run:
 (21) Rerun of (20) at L = 12 with 6x the sweeps (48000), same thresholds: beta 2.5 L12 < 0.8 and beta 2.6 L12 < 1.0.
      If beta 2.6 L12 stays above 1.0 at 2 sigma, the T/T_c hypothesis with N_t^c(2.6) ~ 10-11 is refuted, or L0 is
      larger than 1/(a T_c) for aspect-ratio-1 boxes.
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
