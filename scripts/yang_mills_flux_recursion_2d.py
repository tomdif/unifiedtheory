"""Exact 2D SU(2) check of the flux-sector doubling inequality (exact sums, not Monte Carlo).

With time along direction 1, Z_tw = Tr(Omega T^t) and Z = Tr(T^t), so Z_0 = (Z + Z_tw)/2 and Z_1 = (Z - Z_tw)/2 are traces of T^t on the two
eigenspaces of the center operator Omega. T >= 0 gives Z_1(2t) <= Z_1(t)^2, hence y(2t) <= K(t) y(t)^2, with y = Z_1/Z_0 = (1-z)/(1+z) and K(t) = Z_0(t)^2/Z_0(2t).
On the 2D torus with area A: Z_0 = sum_{n odd} a_n^A, Z_1 = sum_{n even} a_n^A, a_n = (2/x) I_n(x), x = beta_std.
Doubling both sides: y(4A) <= K(A)^2 K(2A) y(A)^4. Any violation is a bug in the derivation.
"""
import numpy as np
from scipy.special import ive
def parts(x,A):
    n=np.arange(1,400); la=np.log(2/x)+np.log(ive(n,x))+x; la=np.where(np.isfinite(la),la,-np.inf)
    ref=la[0]; o=np.exp(A*(la[0::2]-ref)).sum(); e=np.exp(A*(la[1::2]-ref)).sum()
    return o,e,A*ref
def Z0(x,A):
    o,e,r=parts(x,A); return np.log(o)+r
def y(x,A):
    o,e,r=parts(x,A); return e/o
bad=0; print(' x     A     y(A)        y(4A)       K3          K3*y^4      y*=K3^(-1/3)')
for x in (0.5,1,2,4,8,16,32):
    for A in (1,2,4,8,16,64):
        lK1=2*Z0(x,A)-Z0(x,2*A); lK2=2*Z0(x,2*A)-Z0(x,4*A); K3=np.exp(2*lK1+lK2)
        a,b=y(x,A),y(x,4*A); s1=y(x,2*A)<=np.exp(lK1)*a*a*(1+1e-12); s2=b<=np.exp(lK2)*y(x,2*A)**2*(1+1e-12); s3=b<=K3*a**4*(1+1e-12)
        bad+=(not s1)+(not s2)+(not s3)
        print(f'{x:5.1f} {A:4d} {a:.4e} {b:.4e} {K3:.4e} {K3*a**4:.4e} {K3**(-1/3):.4f}')
print('violations',bad)
