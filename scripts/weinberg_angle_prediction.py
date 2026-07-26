"""sin^2 theta_W(M_Z) as an OUTPUT of unification, with the framework's full predicted
matter content. Inputs: measured alpha_EM(M_Z), alpha_3(M_Z). Impose alpha_1=alpha_2=
alpha_3 at M_GUT. Predict sin^2 theta_W(M_Z). SM gives the classic 0.207 (10% low)."""
import numpy as np
from scipy.optimize import brentq
TWO_PI=2*np.pi
MZ=91.1876
A   = 127.951           # 1/alpha_EM(M_Z)
inv_a3 = 8.47           # 1/alpha_3(M_Z)
bSM = np.array([41/10, -19/6, -7.0])

# --- single-scale (all new matter effectively light): sin^2 from the b-ratio ---
def s_from_bratio(b):
    rho = (b[0]-b[1])/(b[1]-b[2])
    return (3*A/5 + rho*inv_a3)/(A*(rho + 8/5))

print("SINGLE-SCALE (all new matter at M_Z) closed-form sin^2 theta_W(M_Z):")
print(f"  SM only:                      {s_from_bratio(bSM):.4f}   (classic ~0.207, 10% low)")
octet=np.array([0,0,4.]); triplet=np.array([0,8/3,0.]); vlL=np.array([2/5,2/3,0.])
print(f"  SM + octet+triplet+1 VL:      {s_from_bratio(bSM+octet+triplet+vlL):.4f}")
print(f"  SM + octet+triplet (no VL):   {s_from_bratio(bSM+octet+triplet):.4f}")
print(f"  measured:                     0.23122")
print()

# --- proper thresholds: triplet@2.7TeV (DM), octet+VL@M_new, require M_GUT=reduced Planck ---
MG = 2.435e18           # reduced Planck (framework-derived), fixed
M3 = 2700.0             # triplet DM
def run_invs(s, Lnew):
    a1Z=(3/5)*(1-s)*A; a2Z=s*A; a3Z=inv_a3
    LZ=np.log(MG/MZ); L3=np.log(MG/M3)
    # per-particle db (Dirac): triplet@M3 (0,8/3,0); octet@Mnew (0,0,4); VL@Mnew (2/5,2/3,0)
    a1=a1Z-(1/TWO_PI)*(bSM[0]*LZ + 0*L3 + (2/5)*Lnew)
    a2=a2Z-(1/TWO_PI)*(bSM[1]*LZ + (8/3)*L3 + (2/3)*Lnew)
    a3=a3Z-(1/TWO_PI)*(bSM[2]*LZ + 0*L3 + 4*Lnew)
    return a1,a2,a3
def solve_threshold():
    # two conditions a1=a2, a2=a3 at MG; unknowns s, Lnew.
    from scipy.optimize import fsolve
    def eqs(x):
        s,Lnew=x
        a1,a2,a3=run_invs(s,Lnew)
        return [a1-a2, a2-a3]
    sol=fsolve(eqs,[0.23, np.log(MG/1e10)],full_output=True)
    x,info,ier,msg=sol
    s,Lnew=x; a1,a2,a3=run_invs(s,Lnew)
    Mnew=MG*np.exp(-Lnew)
    return s,Mnew,(a1+a2+a3)/3,ier
s,Mnew,invGUT,ier=solve_threshold()
print("PROPER THRESHOLDS: triplet@2.7TeV DM, octet+VL@M_new, M_GUT=reduced Planck FIXED:")
print(f"  predicted sin^2 theta_W(M_Z) = {s:.4f}   (measured 0.23122)")
print(f"  octet+VL threshold M_new     = {Mnew:.2e} GeV")
print(f"  1/alpha_GUT                  = {invGUT:.1f}   (framework algebraic 32pi/3 = {32*np.pi/3:.1f})")
print(f"  solver ok: {ier==1}")
