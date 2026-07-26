"""2-loop running to tighten sin^2 theta_W(M_Z). Coupled 2-loop gauge RGEs:
  d(a_i^-1)/dt = -b_i/2pi - (1/8pi^2) sum_j B_ij alpha_j  (+ top-Yukawa, incl. below)
SM 2-loop matrix B (GUT-norm); new matter (octet+triplet+VL) at 1-loop above a common
threshold M_new; M_GUT fixed at reduced Planck; solve (sin^2thetaW, M_new) for unification.
Compare to 1-loop."""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import fsolve
PI=np.pi
MZ=91.1876
A=127.951; T=8.47                     # 1/alpha_EM, 1/alpha_3 at M_Z (inputs)
MG=2.435e18                            # reduced Planck (framework), fixed M_GUT
b_SM=np.array([41/10,-19/6,-7.0])
B_SM=np.array([[199/50,27/10,44/5],[9/10,35/6,12],[11/10,9/2,-26]])  # SM 2-loop, GUT-norm
# top-Yukawa 2-loop gauge contribution coeffs (GUT-norm), enter with + in d(a^-1)/dt
C_top=np.array([17/10,3/2,2.0])
db_new=np.array([2/5, 8/3+2/3, 4.0])  # octet(0,0,4)+triplet(0,8/3,0)+VL(2/5,2/3,0)
tGUT=np.log(MG/MZ)

def integrate(s, tnew, two_loop, yukawa):
    a=np.array([(3/5)*(1-s)*A, s*A, T])  # a_i^-1 at M_Z
    # crude top-Yukawa: alpha_t = y_t^2/4pi, y_t~0.94 at MZ falling; use representative running
    def rhs(t,y,active_b):
        ainv=y; al=1/ainv
        d=-active_b/(2*PI)
        if two_loop:
            d=d-(1/(8*PI**2))*(B_SM@al)
        if yukawa:
            # approximate alpha_t(mu): 0.075 at MZ -> ~0.02 high; smooth
            mu=MZ*np.exp(t); at=0.075/(1+0.06*np.log(mu/MZ))
            d=d+(1/(8*PI**2))*C_top*at*(4*PI)   # +C_top y_t^2/(8pi^2); y_t^2=4pi*at
        return d
    # segment 1: MZ->M_new (SM), segment 2: M_new->M_GUT (SM+new)
    sol1=solve_ivp(rhs,[0,tnew],a,args=(b_SM,),rtol=1e-9,atol=1e-12,dense_output=True)
    a_mid=sol1.y[:,-1]
    sol2=solve_ivp(rhs,[tnew,tGUT],a_mid,args=(b_SM+db_new,),rtol=1e-9,atol=1e-12)
    return sol2.y[:,-1]  # a_i^-1 at M_GUT

def solve_s(two_loop, yukawa):
    def eqs(x):
        s,tnew=x
        aG=integrate(s,tnew,two_loop,yukawa)
        return [aG[0]-aG[1], aG[1]-aG[2]]
    sol,info,ier,msg=fsolve(eqs,[0.238,np.log(1e5/MZ)],full_output=True)
    s,tnew=sol; aG=integrate(s,tnew,two_loop,yukawa)
    return s, MZ*np.exp(tnew), (aG[0]+aG[1]+aG[2])/3, ier

for label,tl,yuk in [("1-loop",False,False),("2-loop gauge",True,False),("2-loop + top Yukawa",True,True)]:
    s,Mnew,invG,ier=solve_s(tl,yuk)
    print(f"{label:22s}: sin^2thetaW(MZ) = {s:.4f}   M_new = {Mnew:.2e} GeV   1/aGUT = {invG:.1f}   {'ok' if ier==1 else 'FAIL'}")
print(f"{'measured':22s}: sin^2thetaW(MZ) = 0.23122")
