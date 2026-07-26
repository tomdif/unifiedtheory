"""Add VL leptons to octet+triplet and solve 1-loop unification with a common new
threshold M_new. Solve the two conditions (a1=a2=a3 at M_GUT) for (M_new, M_GUT)."""
import numpy as np

TWO_PI = 2*np.pi
a = np.array([59.01, 29.59, 8.47])          # 1/alpha_i at M_Z, GUT-normalized
bSM = np.array([41/10, -19/6, -7.0])

def Tidx(rep):  # (T1,T2,T3) per WEYL fermion; rep=(d3,d2,Y) with d=SU(N) dim
    d3,d2,Y = rep
    T1 = (3/5)*(Y**2)*d3*d2                  # hypercharge, summed over all states
    T2 = (1/2)*d3 if d2==2 else (2.0 if d2==3 else 0.0)*d3   # T(fund SU2)=1/2, T(adj)=2
    T3 = (1/2)*d2 if d3==3 else (3.0 if d3==8 else 0.0)*d2   # T(fund SU3)=1/2, T(adj)=3
    return np.array([T1,T2,T3])

def db(rep, nWeyl):  # beta shift from nWeyl copies
    return (2/3)*Tidx(rep)*nWeyl

def solve(dB):
    """dB = total beta shift above M_new. Solve for t=ln(Mnew/MZ), s=ln(MGUT/Mnew)."""
    B = bSM + dB
    bs, Bs = bSM/TWO_PI, B/TWO_PI
    # A_ij = bs_ij * t + Bs_ij * s   (i,j)=(0,1),(1,2)
    M = np.array([[bs[0]-bs[1], Bs[0]-Bs[1]],
                  [bs[1]-bs[2], Bs[1]-Bs[2]]])
    rhs = np.array([a[0]-a[1], a[1]-a[2]])
    t,s = np.linalg.solve(M, rhs)
    # 1/alpha_GUT
    invaGUT = a[0] - bs[0]*t - Bs[0]*s
    return t,s,invaGUT

def report(name, dB):
    t,s,inv = solve(dB)
    MZ=91.19
    Mnew = MZ*np.exp(t); MGUT=MZ*np.exp(t+s)
    phys = (t>-0.01) and (s>0) and (MGUT<2e18) and (inv>0)
    print(f"{name:40s} M_new={Mnew:.2e} GeV  M_GUT={MGUT:.2e} GeV  1/aGUT={inv:.1f}  {'PHYSICAL' if phys else 'unphysical'}")

octet   = db((8,1,0), 2)   # Dirac octet
triplet = db((1,3,0), 2)   # Dirac triplet
vlL     = db((1,2, 0.5), 2) + db((1,2,-0.5),2)  # one Dirac VL lepton doublet = 2 Weyl w/ Y=+-1/2
vlE     = db((1,1, 1.0), 2) + db((1,1,-1.0),2)  # one Dirac VL charged singlet

print("target (b2-b3)/(b1-b2) =", round((a[1]-a[2])/(a[0]-a[1]),4))
report("octet+triplet (Y=0 only)", octet+triplet)
for nL in range(0,5):
  for nE in range(0,5):
    dB = octet+triplet + nL*vlL + nE*vlE
    t,s,inv = solve(dB); MZ=91.19; Mnew=MZ*np.exp(t); MGUT=MZ*np.exp(t+s)
    if (t>-0.02) and (s>0.1) and (1e2<MGUT<5e17) and (5<inv<60) and (Mnew<1e12):
      print(f"  UNIFIES: octet+triplet + {nL} VL-doublet + {nE} VL-singlet -> "
            f"M_new={Mnew:.1e}  M_GUT={MGUT:.2e}  1/aGUT={inv:.1f}")
