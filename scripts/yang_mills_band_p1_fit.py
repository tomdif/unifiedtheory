"""Fit the center-sector boundary influence profile Delta(d) = P1_cold(d) - P1_flip(d) to A cosh(m (D - d)).

The slab of yang_mills_band_targets.py (mode p1/adv) is bounded by the same frozen layer on both sides, so the
lowest flux state gives a cosh centred at mid-slab D = Lx/2. Fit window d >= dmin (default 2, to stay outside the
stout-smearing radius of the frozen layer); weighted least squares, A profiled analytically, m on a grid; the 1-sigma
interval is Delta chi^2 = 1. Prints m with interval and the electric-flux prediction sigma a^2 M - pi/(3M).
Usage: python3 yang_mills_band_p1_fit.py file.json [sigma_a2_by_beta as b:s,b:s] [dmin]
"""
import sys, json, math

def fit(diff, err, D, dmin):
    ds = [d for d in range(dmin, D + 1) if err[d] > 0]
    def chi2(m):
        f = [math.cosh(m * (D - d)) for d in ds]
        w = [1 / err[d] ** 2 for d in ds]
        A = sum(wi * fi * diff[d] for wi, fi, d in zip(w, f, ds)) / sum(wi * fi * fi for wi, fi in zip(w, f))
        return sum(wi * (diff[d] - A * fi) ** 2 for wi, fi, d in zip(w, f, ds)), A
    grid = [i * 0.002 for i in range(1, 2001)]
    vals = [(chi2(m)[0], m) for m in grid]
    c0, m0 = min(vals)
    inside = [m for c, m in vals if c <= c0 + 1]
    return m0, min(inside), max(inside), c0, len(ds) - 2

if __name__ == '__main__':
    R = json.load(open(sys.argv[1]))
    sig = {float(k): float(v) for k, v in (kv.split(':') for kv in sys.argv[2].split(','))} if len(sys.argv) > 2 else {}
    dmin = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    for r in R:
        P = r['P1']; D = r['Lx'] // 2; M = r['M']
        m0, lo, hi, c0, dof = fit(P['diff'], P['err'], D, dmin)
        pred = sig[r['bstd']] * M - math.pi / (3 * M) if r['bstd'] in sig else float('nan')
        print('beta %.2f M %2d  m = %.3f [%.3f, %.3f]  chi2/dof = %.1f/%d  pred sigma M - pi/3M = %.3f'
              % (r['bstd'], M, m0, lo, hi, c0, dof, pred))
