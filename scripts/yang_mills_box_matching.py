"""Do the convex-RG regime and the finite-box regime meet at one coupling? (numerics, not a proof)

GAP_BAND_STATEMENT §2b: fine-direction blocks are convex/dilute (Peierls bounds met) for beta_eff >~ 2.45-3.
§6/§8b: boundary influence on UV observables (plaquettes, 2x2 loops) in contractible boxes dies within 3-5 lattice units at
beta 2.3-2.5. If a finite-box mixing criterion also holds for LONG-WAVELENGTH observables at some beta* in the convex
regime with a modest box, the proof architecture needs no band crossing towards strong coupling. It needs only a
matching at beta*: a convex multiscale RG from the UV down to beta_eff = beta*, plus a finite-box criterion for the
effective measure at beta*. Long-wavelength observables are the issue: plaquettes are boundary-layer (UV) quantities,
while the influence on smooth observables should decay at the 0++ mass, which shrinks in lattice units as beta grows.

Contractible box C = [1, L0]^4 in periodic N = L0 + 2, frozen two-layer shell (as yang_mills_box_vortex.py).
BCs: cold, hot (frozen Haar draw), vortex (thin tau_3 vortex, flux pi, holonomy ~ -0.95 around the box).
Observables: energy proxy e = 1 - mean plaquette over the interior plaquettes at a site, after stout smearing rho = 0.1
with n = 0, 5, 20 steps (flow time ~ 0.1 n, smoothing radius sqrt(8t) ~ 0, 2, 4), as profiles in the Chebyshev depth
from the shell. The smearing uses staples from plaquettes inside C only, so the observable is a gauge-invariant
function of the interior links alone (it never reads the boundary); near the faces it is a Neumann-type smoothing. Influence: Delta(d) = max over hot/vortex of |<e>_BC - <e>_cold| / <e>_cold.

Written before any run (2026-11-07):
 (10) For the n = 20 (radius ~4) observable the decay rate of Delta(d) at large depth falls with beta roughly like the
      0++ mass in lattice units (a m ~ 0.7 at 2.5): the rate at 3.0 is at most 0.6x the rate at 2.5.
 (11) Matching: there is a beta* in [2.5, 2.8] where (a) the fine-direction non-convex fraction is <= 3.2% (§2b:
      true from 2.5 up), and (b) the n = 20 relative influence is below 1e-2 by depth 7 in an L0 = 16 box.
      At 3.0, (b) fails: influence at depth 7 is >= 1e-2.
Usage: out betas L0 sweeps [measure_every]
"""
import os, sys, json, math, time
import torch
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_box_vortex as V
BT = V.BT; G = V.G; DT = V.DT
NS = (0, 5, 20)


def interior_masks(inC):
    """pm[(m, n)][x] = 1 iff the plaquette at x in plane (m, n) has all four corners in C."""
    S = BT.S; pm = {}
    for m in range(4):
        for n in range(4):
            if m != n: pm[(m, n)] = (inC & S(inC, m) & S(inC, n) & S(S(inC, m), n)).to(DT)
    return pm


def smear_interior(U, pm, free, rho, nst):
    """Stout smearing of the free links with staples from interior plaquettes only: a gauge-covariant map of the
    interior links alone, so the flowed observable never reads the frozen boundary."""
    qmul, qc, S = BT.qmul, BT.qc, BT.S
    for _ in range(nst):
        new = []
        for m in range(4):
            st = 0.
            for n in range(4):
                if n == m: continue
                up = qmul(qmul(S(U[n], m), qc(S(U[m], n))), qc(U[n])) * pm[(m, n)][..., None]
                bk = qmul(qmul(qc(S(U[n], m)), qc(U[m])), U[n]) * pm[(m, n)][..., None]
                st = st + up + S(bk, n, -1)
            v = rho * qmul(qc(st), qc(U[m]))[..., 1:]
            th = v.norm(dim=-1, keepdim=True)
            e = torch.cat([torch.cos(th), torch.sinc(th / math.pi) * v], -1)
            nm = qmul(e, U[m]); nm = torch.where(free[m][..., None], nm, U[m]); new.append(nm)
        U = torch.stack(new)
    return U


def energy_profile(U, L0, dep, pm, free):
    out = []; Us = U; prev = 0
    for n in NS:
        if n > prev: Us = smear_interior(Us, pm, free, 0.1, n - prev); prev = n
        P = G.plaq_re(Us, torch.ones(U.shape[1:5], dtype=DT))
        num = sum(P[(a, b)] * pm[(a, b)] for (a, b) in P); den = sum(pm[(a, b)] for (a, b) in P)
        e = 1 - num / den.clamp(min=1)
        out.append([float(e[(dep == d) & (den > 0)].mean()) for d in range(L0 // 2)])
    return out


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; L0 = int(sys.argv[3]); nsw = int(sys.argv[4])
    every = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    N, shp, xs, inC, free, par, dep = V.geometry(L0); z = torch.ones(shp, dtype=DT); pm = interior_masks(inC)
    gen = torch.Generator(device=BT.dev).manual_seed(11)
    res = []
    for b in betas:
        beta = b / 2; t0 = time.time(); row = dict(L0=L0, bstd=b, sweeps=nsw, every=every, ns=list(NS))
        for kind in ('cold', 'hot', 'vortex'):
            if kind == 'vortex': U = V.vortex_links(N, L0, 1.5)
            else:
                U = torch.zeros((4,) + shp + (4,), dtype=DT); U[..., 0] = 1
                if kind == 'hot':
                    h = torch.randn((4,) + shp + (4,), dtype=DT, generator=gen); U = h / h.norm(dim=-1, keepdim=True)
            for _ in range(300): BT.sweep(U, z, beta, par, free)
            rec = []
            for i in range(nsw):
                BT.sweep(U, z, beta, par, free)
                if i % every == 0: rec.append(energy_profile(U, L0, dep, pm, free))
            A = torch.tensor(rec, dtype=torch.float64)                     # (nmeas, len(NS), depths)
            bins = torch.stack([q.mean(0) for q in torch.tensor_split(A, 20)])
            row[kind] = dict(mean=bins.mean(0).tolist(), err=(bins.std(0) / math.sqrt(20)).tolist())
        row['sec'] = round(time.time() - t0, 1)
        res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
