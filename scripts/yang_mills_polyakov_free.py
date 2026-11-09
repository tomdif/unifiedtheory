"""Leading-order (Gaussian) Euclidean correlator of g = sum P1^2 around the twist-eating vacuum (exact sums).

At quadratic order the fluctuation of the color component a^1 is a free lattice Maxwell field, periodic in directions
1, 3 and time, antiperiodic in direction 2. dP1(x2,x3) is proportional to the x1 zero mode of A^1_1, which is
linearized-gauge invariant. Wick: C(t)/C(0) = sum_k G_k(t)^2 f_k / sum_k G_k(0)^2 f_k, with G_k(t) = e^{-w t}/(2 sinh w),
2 cosh w - 2 = khat^2, k = (pi(2m+1)/n, 2 pi m'/n), and f_k = exp(-4 t_f khat^2) for 3D flow time t_f (0: unflowed).
Independent of beta. Prints C(t)/C(0) at t = 1, round(n/3), n/2, and the ratio at t = n/3 for n -> large.
Usage: flowc (t_f = n^2/flowc; 0 = no flow)
"""
import sys, numpy as np
fc=float(sys.argv[1])
for n in (6,8,10,12,16,24,32,64,128):
    m=np.arange(n); k2=np.pi*(2*m+1)/n; k3=2*np.pi*m/n
    kh=(4*np.sin(k2[:,None]/2)**2+4*np.sin(k3[None,:]/2)**2).ravel()
    w=np.arccosh(1+kh/2); tf=n*n/fc if fc>0 else 0.
    f=np.exp(-4*tf*kh)
    def C(t): return (np.exp(-2*w*t)/(4*np.sinh(w)**2)*f).sum()
    ts=max(1,round(n/3))
    print(n, 'C1=%.3f'%(C(1)/C(0)), 'C(n/3)=%.3f (t=%d)'%(C(ts)/C(0),ts), 'C(n/3 exact)=%.3f'%(C(n/3)/C(0)),
          'C(n/2)=%.3f'%(C(n/2)/C(0)))
