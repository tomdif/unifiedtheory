"""Is the center-sector obstruction to a finite-box criterion (GAP_BAND_STATEMENT §8) an artifact of periodic slabs?

In the slab of yang_mills_band_targets.py the transverse directions are periodic, so a center-flipped boundary
holonomy is invisible to every plaquette and couples to the non-contractible Polyakov loop. A Dobrushin-Shlosman /
Martinelli-Olivieri criterion on Z^4 uses contractible boxes, where no such loop exists. The nearest analogue is a
thick center vortex in the frozen shell. Its holonomy around the box is -1, it is not gauge-equivalent to the cold
boundary, and away from its core each boundary plaquette is perturbed only slightly.

Geometry: periodic N^4, N = L0 + 2. Free links are those with both endpoints in the cube C = [1, L0]^4; all other links
are frozen (a shell of two site layers). Boundary conditions:
  cold      all frozen links 1;
  vortex_s  a U(1) (tau_3) vortex of flux pi through the (1,2) plane with a Gaussian profile of width s, centred on the
            axis of C, extended along x0 and x3, plus the compensating anti-vortex in the shell corner; built from
            Delta psi = f by FFT, so plaquette angles equal f exactly. s = 1.5 (thin) and s = L0/4 (thick).
Observables, as profiles in the depth d of (x0, x3) from the x0/x3 faces of C (where the vortex sheet enters):
r x r Wilson loops in the (1,2) plane LINKED with the vortex axis (centred on it) and UNLINKED (same plane, shifted
so the axis is just outside); and the (1,2) plaquette by Chebyshev depth. Influence Delta(d) = <O>_cold - <O>_vortex.
The (1,2) cross-section of C has side L0, the analogue of the transverse size M of the periodic slab, where the
flipped-holonomy influence on the Polyakov loop decayed at rate m(M) ~ sigma_eff M.

Written before any run (2026-11-06):
 (8) Center-specific influence exists near the face: at beta 2.5 the linked r = 2 loop has |Delta(d=1)| at least 3x the
     unlinked one, for the thin vortex, at L0 = 8.
 (9) Decisive for T3, on the linked r = 2 profile at beta 2.5 (decay rate m from |Delta(d)| over the resolved depths):
     H_local  m is at least 0.5 per lattice unit and does not grow with L0 (L0 = 16 vs 8 within 30%): the influence
              travels as a glueball, the slab obstruction is an artifact of periodic transverse directions, and the
              finite-box size is the plaquette-level one of §6;
     H_center m grows with the cross-section, m(16)/m(8) >= 1.6, as in the slab (flux-energy, area-type decay).
     My guess is H_center at beta 2.5: the thick vortex is a center flux the interior must carry or expel.
Usage: out betas L0s sweeps [r_list]
"""
import os, sys, json, math, time
import torch
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import yang_mills_band_targets as BT
G = BT.G; DT = BT.DT; qmul, qc, S = BT.qmul, BT.qc, BT.S


def geometry(L0):
    N = L0 + 2; shp = (N,) * 4
    xs = torch.stack(torch.meshgrid(*[torch.arange(N)] * 4, indexing='ij'))
    inC = ((xs >= 1) & (xs <= L0)).all(0)
    free = torch.stack([inC & S(inC, m) for m in range(4)])                  # both endpoints in C
    par = xs.sum(0) % 2
    dep = torch.minimum(xs - 1, L0 - xs).amin(0)                             # Chebyshev depth, 0 on the faces of C
    return N, shp, xs, inC, free, par, dep


def vortex_links(N, L0, s):
    """theta_1(x) = -(psi(x) - psi(x - e2)), theta_2(x) = psi(x) - psi(x - e1) on the (1,2) torus; plaquette angle = Lap psi = f."""
    i = torch.arange(N, dtype=torch.float64)
    def bump(c):
        d1 = (i[:, None] - c + N / 2) % N - N / 2; d2 = (i[None, :] - c + N / 2) % N - N / 2
        g = torch.exp(-(d1 ** 2 + d2 ** 2) / (2 * s * s)); return g / g.sum()
    f = math.pi * (bump(L0 / 2) - bump(N - 1.0))          # anti-vortex: plaquette between layers N-1 and 0 (shell)
    k = 2 * math.pi * torch.fft.fftfreq(N, dtype=torch.float64)
    lap = (2 * torch.cos(k)[:, None] - 2) + (2 * torch.cos(k)[None, :] - 2); lap[0, 0] = 1
    psi = torch.fft.ifft2(torch.fft.fft2(f.to(torch.complex128)) / lap).real
    th1 = -(psi - torch.roll(psi, 1, 1)); th2 = psi - torch.roll(psi, 1, 0)
    chk = th1 + torch.roll(th2, -1, 0) - torch.roll(th1, -1, 1) - th2
    assert float((chk - f).abs().max()) < 1e-9
    U = torch.zeros((4,) + (N,) * 4 + (4,), dtype=DT); U[..., 0] = 1
    for m, th in ((1, th1), (2, th2)):
        t = th.to(DT)[None, :, :, None].expand(N, N, N, N)
        U[m][..., 0] = torch.cos(t); U[m][..., 3] = torch.sin(t)
    return U


def line(U, m, r):
    L = U[m]
    for k in range(1, r): L = qmul(L, S(U[m], m, k))
    return L


def loops(U, a, b, r):
    """Re 1/2 tr of the r x r loop in plane (a, b) with lower-left corner x, as a field."""
    La, Lb = line(U, a, r), line(U, b, r)
    return qmul(qmul(qmul(La, S(Lb, a, r)), qc(S(La, b, r))), qc(Lb))[..., 0]


def measure(U, z, L0, rs, dep):
    """Profiles in the depth d03 = min distance of (x0, x3) to the x0/x3 faces of C, where the vortex sheet enters."""
    c = L0 // 2; out = {}
    q = torch.arange(1, L0 + 1); d1 = torch.minimum(q - 1, L0 - q); d03 = torch.minimum(d1[:, None], d1[None, :])
    for r in rs:
        lo = c + 1 - r // 2                            # loop [lo, lo + r] contains the axis at c + 1/2
        W12 = loops(U, 1, 2, r)[1:L0 + 1, :, :, 1:L0 + 1]
        lk = W12[:, lo, lo, :]
        out[f'link{r}'] = [float(lk[d03 == d].mean()) for d in range(L0 // 2)]
        if c + 1 + r <= L0:
            ul = W12[:, c + 1, lo, :]
            out[f'unl{r}'] = [float(ul[d03 == d].mean()) for d in range(L0 // 2)]
    P = G.plaq_re(U, z)[(1, 2)]
    out['plaq'] = [float(P[dep == d].mean()) for d in range(L0 // 2)]
    return out


def main():
    out = sys.argv[1]; betas = [float(b) for b in sys.argv[2].split(',')]; L0s = [int(x) for x in sys.argv[3].split(',')]
    nsw = int(sys.argv[4]); rs0 = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else [2, 4]
    res = []
    for L0 in L0s:
        N, shp, xs, inC, free, par, dep = geometry(L0); z = torch.ones(shp, dtype=DT)
        rs = [r for r in rs0 if r <= L0 - 2]
        for b in betas:
            beta = b / 2; t0 = time.time(); row = dict(L0=L0, bstd=b, sweeps=nsw)
            for kind, s in (('cold', None), ('vortex_thin', 1.5), ('vortex_thick', L0 / 4)):
                U = vortex_links(N, L0, s) if s else torch.zeros((4,) + shp + (4,), dtype=DT)
                if not s: U[..., 0] = 1
                hol = None
                if s:   # frozen holonomy around the box in the (1,2) plane at x0 = x3 = 0 (shell): expect -1
                    hol = float(loops(U, 1, 2, L0 - 1)[0, 1, 1, 0])   # around the axis, in the shell layer x0 = 0
                for _ in range(300): BT.sweep(U, z, beta, par, free)
                rec = []
                for _ in range(nsw):
                    BT.sweep(U, z, beta, par, free); rec.append(measure(U, z, L0, rs, dep))
                nb = 20; d = {}
                for k in rec[0]:
                    arr = torch.tensor([x[k] for x in rec], dtype=torch.float64)
                    bins = torch.stack([q.mean(0) for q in torch.tensor_split(arr, nb)])
                    d[k] = dict(mean=bins.mean(0).tolist(), err=(bins.std(0) / math.sqrt(nb)).tolist())
                row[kind] = dict(obs=d, frozen_loop=hol)
            row['sec'] = round(time.time() - t0, 1)
            res.append(row); print(json.dumps(row), flush=True); json.dump(res, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
