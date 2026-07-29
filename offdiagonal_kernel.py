#!/usr/bin/env python3
"""Off-diagonal covariance of the BDG noise field (factorized-weight channel).

C(d;T) = int_{J^-(x) cap J^-(x')} f4D(tau1^4) f4D(tau2^4) d4y, tips split by
spatial d (kernel units).  Cone-adapted reduction: the inner angular integral
is (2rd)^-1 * int_{wm}^{wp} f4D(w^2) dw with w = tau2^2 -- for large depth the
band covers the full w-mass int_0^inf f4D(w^2) dw = (1/2) M[f4D](1/2) = 0
[LEAN: f4D_w_mass_zero], so the IR divergence CANCELS at d > 0.
Verified: C(d;T) is T-independent (T = 25..400); C ~ 1/d at small d; dead by
d ~ 2; C3 = int 4pi d^2 C dd ~ 0.31.  Diagonal (f4Dsq) object grows ~ T^2.
=> per-point no-self-averaging + full self-averaging of extended observables.
"""
import numpy as np
from scipy import integrate

f4D = lambda z: np.exp(-z)*(1 - 9*z + 8*z**2 - (4/3)*z**3)
wg = np.linspace(0, 12, 24001)
Gc = integrate.cumulative_trapezoid(f4D(wg**2), wg, initial=0.0)
def G(a, b):
    a = np.clip(a, 0, 12); b = np.clip(b, 0, 12)
    return np.interp(b, wg, Gc) - np.interp(a, wg, Gc)

def C(d, T=100.0, taum=3.0, nt=100):
    taus = np.linspace(1e-3, taum, nt); dt = taus[1]-taus[0]
    tot = 0.0
    for t1 in taus:
        def rint(r):
            wp = t1*t1 + 2*r*d - d*d
            if wp <= 0: return 0.0
            wm = max(t1*t1 - 2*r*d - d*d, 0.0)
            return G(wm, wp) * r*r/np.sqrt(r*r+t1*t1)/(2*r*d)
        val, _ = integrate.quad(rint, 1e-3, T, limit=400)
        tot += f4D(t1**4)*t1*val*dt
    return 2*np.pi*tot

if __name__ == "__main__":
    print("zero check:", integrate.quad(lambda w: f4D(w**2), 0, 40, limit=200)[0])
    ds = np.array([0.05,0.1,0.2,0.35,0.5,0.75,1.0,1.25,1.5,2.0])
    Cs = np.array([C(d) for d in ds])
    for d, c in zip(ds, Cs): print(f"  C({d:5.2f}) = {c:9.4f}")
    C3 = integrate.trapezoid(4*np.pi*ds**2*Cs, ds)
    print(f"C3 = {C3:.4f}")
    # Lambda-channel identification vs Das-Nasiri-Yazdi alpha fit (arXiv:2307.13743)
    A = (24/np.pi)*np.sqrt((8/3)*C3)   # time-extent O(1) pending
    for alpha in [0.0068, 0.0085, 0.0102]:
        lk = np.sqrt(A/(8*np.pi*alpha))
        print(f"  alpha = {alpha:.4f}  ->  l_k = {lk:.2f} l_p  (eps = {lk**-4:.2e})")
