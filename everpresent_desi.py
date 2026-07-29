#!/usr/bin/env python3
"""Everpresent-Lambda vs DESI DR2: confrontation-lite (shape statistics).

Perturbative overlay on the LCDM background (no back-reaction; honest for the
w(z)-shape and Omega_L(z) statistics that discriminate the two amplitude laws):

  CLASSIC:  rho_L = amp * y(V)/sqrt(V)   (ADGS/DNY Model 1)   ~ 1/t^2 tracking
  ACTION :  rho_L = amp * y4(V)/V^(1/4)  (our MC-validated Var S ~ N T^2 edge) ~ 1/t

y, y4 = standardized independent-increment processes in V (resp. V^{3/2}).
Amplitudes calibrated so median |rho_L(today)| = 0.69 rho_c0 (shape test).
DESI DR2 (arXiv:2503.14738): DESY5 (w0,wa)=(-0.752+-0.057, -0.86+0.23-0.20);
Pantheon+ (-0.838+-0.055, -0.62+0.22-0.19).  Everpresent-classic CMB problem
(DNY 2307.13743) should appear as Omega_L(z=1100) ~ O(today's); action law
predicts Omega_L(rec) suppressed by ~t_rec/t_0.
"""
import numpy as np

rng = np.random.default_rng(11)
Om, Or, OL = 0.31, 9.0e-5, 0.69
rho_c0 = 3.0

# ---- LCDM background ----
n = 6000
a = np.geomspace(1e-9, 1.0, n)
H = np.sqrt((Om/a**3 + Or/a**4 + OL))          # H/H0
t = np.zeros(n); eta = np.zeros(n)
t[0] = a[0]**2/(2*np.sqrt(Or)); eta[0] = a[0]/np.sqrt(Or)
for i in range(1, n):
    da = a[i]-a[i-1]; aH = 0.5*(a[i]*H[i]+a[i-1]*H[i-1])
    t[i] = t[i-1] + da/aH
    eta[i] = eta[i-1] + da/(0.5*(a[i]**2*H[i]+a[i-1]**2*H[i-1]))
# past-lightcone 4-volume V(t) = (4pi/3) int dt' a'^3 (eta-eta')^3
I0 = np.concatenate([[0], np.cumsum(0.5*(a[1:]**3+a[:-1]**3)*np.diff(t))])
I1 = np.concatenate([[0], np.cumsum(0.5*(a[1:]**3*eta[1:]+a[:-1]**3*eta[:-1])*np.diff(t))])
I2 = np.concatenate([[0], np.cumsum(0.5*(a[1:]**3*eta[1:]**2+a[:-1]**3*eta[:-1]**2)*np.diff(t))])
I3 = np.concatenate([[0], np.cumsum(0.5*(a[1:]**3*eta[1:]**3+a[:-1]**3*eta[:-1]**3)*np.diff(t))])
V = (4*np.pi/3)*(eta**3*I0 - 3*eta**2*I1 + 3*eta*I2 - I3)
V = np.maximum.accumulate(np.maximum(V, 1e-300))
print(f"background: t0={t[-1]:.3f}/H0  eta0={eta[-1]:.3f}  V0={V[-1]:.2f}/H0^4")

def realizations(law, n_real=600):
    W = V if law == "classic" else V**1.5
    dW = np.diff(W, prepend=0.0)
    out = np.zeros((n_real, n))
    for r in range(n_real):
        xi = rng.normal(size=n)
        B = np.cumsum(np.sqrt(np.maximum(dW,0))*xi)     # Brownian in W
        y = B/np.sqrt(W)
        out[r] = y/np.sqrt(V) if law == "classic" else y/V**0.25
    return out

def cpl_fit(rhoL, zmax=1.0):
    sel = a >= 1/(1+zmax)
    r = rhoL[sel]
    if np.any(np.sign(r) != np.sign(r[-1])): return None
    w = -1 - np.gradient(np.log(np.abs(r)), np.log(a[sel]))/3
    X = np.vstack([np.ones(sel.sum()), 1-a[sel]]).T
    return np.linalg.lstsq(X, w, rcond=None)[0]

for law in ["classic", "action"]:
    R = realizations(law)
    med = np.median(np.abs(R[:,-1])); amp = OL*rho_c0/med
    R = R*amp
    print(f"\n=== {law.upper()}  (shape-calibration amp={amp:.3g}; "
          f"needed dimensionless amplitude = {amp/(8*np.pi):.3g} in 8*pi*alpha convention)")
    pos = R[:,-1] > 0
    fits = [cpl_fit(r) for r in R[pos]]
    fits = np.array([f for f in fits if f is not None])
    i_rec = np.argmin(np.abs(a - 1/1101))
    OmL_rec = np.abs(R[:,i_rec])/(np.abs(R[:,i_rec]) + Om*rho_c0*1101**3 + Or*rho_c0*1101**4)
    print(f"  rho_L>0 today: {pos.mean():.2f};  monotone-sign CPL windows: {len(fits)}/{pos.sum()}")
    if len(fits):
        w0, wa = fits[:,0], fits[:,1]
        print(f"  w0 median {np.median(w0):+.3f}  [16,84]: [{np.percentile(w0,16):+.3f},{np.percentile(w0,84):+.3f}]")
        print(f"  wa median {np.median(wa):+.3f}  [16,84]: [{np.percentile(wa,16):+.3f},{np.percentile(wa,84):+.3f}]")
        dq = ((w0 > -1) & (w0 < -0.5) & (wa < 0) & (wa > -2)).mean()
        print(f"  fraction in DESI-like box (-1<w0<-0.5, -2<wa<0): {dq:.2f}")
    print(f"  |Omega_L|(z=1100): median {np.median(OmL_rec):.2e}  95%: {np.percentile(OmL_rec,95):.2e}")
