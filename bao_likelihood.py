#!/usr/bin/env python3
"""DESI DR2 BAO likelihood (realization-marginalized) for the everpresent laws.

Data: verbatim DESI DR2 Table 4 (arXiv:2503.14738). Validation targets:
LCDM chi2/dof = 10.2/11 at Om = 0.2975; w0waCDM Delta-chi2_MAP = -4.7.
Models: LCDM | CPL | deterministic action drift rho_DE ~ V^{-1/4} |
stochastic ACTION (fixed l_k branch) | stochastic CLASSIC (running/Karolyhazy
branch). Flat universe: rho_DE(0) = (1-Om-Or) rho_c; shape from realization.
Profile (Om, beta = c/(100 h rd)) per model/realization. Not a full cosmology
fit (no SN/CMB); BAO-only, background V(a) from LCDM (leading order).
"""
import numpy as np
from scipy import optimize

C_KMS = 299792.458
DATA = [  # name, z, kind, val, err, corr(DM,DH)
 ("BGS",0.295,"DV",7.942,0.075,None),
 ("LRG1",0.510,"MH",(13.588,21.863),(0.167,0.425),-0.459),
 ("LRG2",0.706,"MH",(17.351,19.455),(0.177,0.330),-0.404),
 ("LRG3+ELG1",0.934,"MH",(21.576,17.641),(0.152,0.193),-0.416),
 ("ELG2",1.321,"MH",(27.601,14.176),(0.318,0.221),-0.434),
 ("QSO",1.484,"MH",(30.512,12.817),(0.760,0.516),-0.500),
 ("Lya",2.330,"MH",(38.988,8.632),(0.531,0.101),-0.431)]
Or = 9.0e-5

def chi2_of(Efun, Om, beta):
    # beta = c/(100 h rd) -> DM/rd = beta * int dz/E ; DH/rd = beta/E
    zg = np.linspace(0, 2.4, 481)
    Eg = Efun(zg, Om)
    if np.any(~np.isfinite(Eg)) or np.any(Eg <= 0): return 1e10
    invE = 1/Eg
    cum = np.concatenate([[0], np.cumsum(0.5*(invE[1:]+invE[:-1])*np.diff(zg))])
    def DM(z): return beta*np.interp(z, zg, cum)
    def DH(z): return beta/np.interp(z, zg, Eg)
    c2 = 0.0
    for name,z,kind,val,err,r in DATA:
        if kind=="DV":
            dv = (z*DM(z)**2*DH(z))**(1/3)
            c2 += ((dv-val)/err)**2
        else:
            dm, dh = DM(z), DH(z)
            dM, dH = dm-val[0], dh-val[1]
            sM, sH = err
            det = (sM*sH)**2*(1-r*r)
            c2 += (dM*dM*sH*sH - 2*r*sM*sH*dM*dH + dH*dH*sM*sM)/det
    return c2

def fit(Efun, x0=(0.30, 29.5)):
    res = optimize.minimize(lambda p: chi2_of(Efun, p[0], p[1]), x0,
                            method="Nelder-Mead",
                            options={"xatol":1e-4,"fatol":1e-4,"maxiter":600})
    return res.fun, res.x

# --- background V(a) (LCDM) for the shape laws ---
n = 4000
a_bg = np.geomspace(1e-9, 1.0, n)
Om0 = 0.31
H_bg = np.sqrt(Om0/a_bg**3 + Or/a_bg**4 + (1-Om0-Or))
t = np.zeros(n); eta = np.zeros(n)
t[0] = a_bg[0]**2/(2*np.sqrt(Or)); eta[0] = a_bg[0]/np.sqrt(Or)
for i in range(1,n):
    da = a_bg[i]-a_bg[i-1]
    t[i] = t[i-1]+da/(0.5*(a_bg[i]*H_bg[i]+a_bg[i-1]*H_bg[i-1]))
    eta[i] = eta[i-1]+da/(0.5*(a_bg[i]**2*H_bg[i]+a_bg[i-1]**2*H_bg[i-1]))
I = lambda k: np.concatenate([[0],np.cumsum(0.5*(a_bg[1:]**3*eta[1:]**k+a_bg[:-1]**3*eta[:-1]**k)*np.diff(t))])
I0,I1,I2,I3 = I(0),I(1),I(2),I(3)
V = np.maximum((4*np.pi/3)*(eta**3*I0-3*eta**2*I1+3*eta*I2-I3),1e-300)
V = np.maximum.accumulate(V)

def shape_to_E(shape_a):    # shape(a) normalized at a=1; flatness closure
    def Efun(z, Om):
        a = 1/(1+z)
        f = np.interp(a, a_bg, shape_a)/shape_a[-1]
        return np.sqrt(np.maximum(Om/a**3 + Or/a**4 + (1-Om-Or)*f, 1e-12))
    return Efun

# --- models ---
E_lcdm = lambda z,Om: np.sqrt(Om*(1+z)**3+Or*(1+z)**4+(1-Om-Or))
c2, p = fit(E_lcdm); print(f"LCDM:      chi2 = {c2:6.2f}  (target 10.2)  Om={p[0]:.4f} beta={p[1]:.3f}")
chi2_ref = c2

def E_cpl(z,Om,w0,wa):
    a = 1/(1+z)
    f = a**(-3*(1+w0+wa))*np.exp(-3*wa*(1-a))
    return np.sqrt(Om*(1+z)**3+Or*(1+z)**4+(1-Om-Or)*f)
res = optimize.minimize(lambda p: chi2_of(lambda z,Om: E_cpl(z,Om,p[2],p[3]), p[0], p[1]),
                        (0.35,29.5,-0.6,-1.5), method="Nelder-Mead",
                        options={"maxiter":3000,"xatol":1e-4,"fatol":1e-4})
print(f"CPL:       chi2 = {res.fun:6.2f}  (target ~5.5)  w0={res.x[2]:+.2f} wa={res.x[3]:+.2f}")

c2d, pd = fit(shape_to_E(V**-0.25))
print(f"DET-ACTION chi2 = {c2d:6.2f}  Delta vs LCDM = {c2d-chi2_ref:+.2f}  Om={pd[0]:.4f}")

rng = np.random.default_rng(23)
def realization(p):
    W = V**(1.5 if p==0.25 else 1.0)
    dW = np.diff(W, prepend=0.0)
    B = np.cumsum(np.sqrt(np.maximum(dW,0))*rng.normal(size=n))
    return B/np.sqrt(W)/V**p
for label, p, nr in [("ACTION", 0.25, 150), ("CLASSIC", 0.5, 150)]:
    d2 = []
    for _ in range(nr):
        sh = realization(p)
        if abs(sh[-1]) < 1e-12: continue
        if sh[-1] < 0: sh = -sh          # sign symmetry: take rho_DE(0)>0 branch
        c2r, _ = fit(shape_to_E(sh))
        if c2r < 1e9: d2.append(c2r - chi2_ref)
    d2 = np.array(d2)
    print(f"STOCH-{label}: n={len(d2)}  Delta-chi2 vs LCDM: median {np.median(d2):+.2f}  "
          f"best {d2.min():+.2f}  frac<0 (beats LCDM): {(d2<0).mean():.2f}  "
          f"frac<-4.7 (matches w0waCDM): {(d2<-4.7).mean():.2f}")
