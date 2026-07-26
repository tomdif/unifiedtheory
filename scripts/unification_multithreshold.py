"""Multi-threshold 1-loop unification with the Y=0 triplet pinned at the thermal
dark-matter mass (~2.7 TeV). Each new particle enters at its own scale:
  1/a_i(mu) = a_i(MZ) - (1/2pi)[ bSM_i ln(mu/MZ) + sum_p db^p_i ln(mu/M_p) ]  (mu>all M_p)
Solve alpha1=alpha2=alpha3 at M_GUT.  triplet fixed; scan the VL-doublet scale,
solve for M_GUT and the octet scale."""
import numpy as np
TWO_PI = 2*np.pi
MZ = 91.1876
a  = np.array([59.01, 29.59, 8.47])         # 1/alpha_i(MZ), GUT norm
bSM = np.array([41/10, -19/6, -7.0])

# beta shifts (Dirac = 2 Weyl); triplet only b2, octet only b3, VL doublet b1&b2
db3 = np.array([0.0, 8/3, 0.0])             # Y=0 EW triplet  (dark matter)
db8 = np.array([0.0, 0.0, 4.0])             # color octet
dbL = np.array([2/5, 2/3, 0.0])             # one VL lepton doublet (1,2,+-1/2)

M3 = 2700.0                                  # triplet = thermal wino DM mass
u3 = np.log(M3/MZ)

def solve(uL):
    """given uL=ln(M_L/MZ) solve for x=ln(MGUT/MZ) and u8=ln(M8/MZ)."""
    # unknown vector v=(x,u8). Build 2 conditions (a1-a2),(a2-a3).
    # 1/a_i(MGUT)= a_i - (1/2pi)[bSM_i x + db3_i (x-u3) + db8_i (x-u8) + dbL_i (x-uL)]
    # coeff of x in 1/a_i : -(1/2pi)(bSM_i+db3_i+db8_i+dbL_i) ; coeff of u8: +(1/2pi)db8_i
    B = bSM+db3+db8+dbL
    # condition f_i(x,u8) := a_i - (1/2pi)[B_i x - db3_i u3 - db8_i u8 - dbL_i uL] equal for all i
    # diff (i-j)=0 : (a_i-a_j) - (1/2pi)[(B_i-B_j)x - (db8_i-db8_j)u8 - (db3_i-db3_j)u3 - (dbL_i-dbL_j)uL]=0
    def row(i,j):
        cx  = (B[i]-B[j])/TWO_PI
        cu8 = -(db8[i]-db8[j])/TWO_PI
        rhs = (a[i]-a[j]) + (1/TWO_PI)*( (db3[i]-db3[j])*u3 + (dbL[i]-dbL[j])*uL )
        return [cx, cu8], rhs
    r1,rhs1 = row(0,1); r2,rhs2 = row(1,2)
    M = np.array([r1,r2]); rhs=np.array([rhs1,rhs2])
    x,u8 = np.linalg.solve(M,rhs)
    invG = a[0] - (1/TWO_PI)*(B[0]*x - db3[0]*u3 - db8[0]*u8 - dbL[0]*uL)
    return x,u8,invG

print(f"Triplet (Y=0 EW, dark matter) PINNED at M3 = {M3/1000:.1f} TeV\n")
print(f"{'M_VL (GeV)':>12} {'M_octet (GeV)':>14} {'M_GUT (GeV)':>13} {'1/aGUT':>7}  status")
for uL in np.log(np.array([1e3,1e4,1e6,1e8,1e10,1e12,1e14])/MZ):
    x,u8,invG = solve(uL)
    MG=MZ*np.exp(x); M8=MZ*np.exp(u8); ML=MZ*np.exp(uL)
    ok = (M8>M3) and (M8<MG) and (ML>MZ) and (MG<3e18) and (0<invG<60) and (MG>M8)
    print(f"{ML:>12.1e} {M8:>14.2e} {MG:>13.2e} {invG:>7.1f}  {'PHYSICAL' if ok else 'unphysical (ordering/scale)'}")

print("\nNote: triplet at 2.7 TeV contributes to b2 over the whole desert -> its long")
print("lever arm is what makes octet/VL/M_GUT fall where they do. Check the branch")
print("where octet is also near the DM scale (a full TeV-scale 'gaugino' multiplet):")
# force octet and triplet both at ~few TeV, solve for VL scale + MGUT instead
def solve2(u8):
    B=bSM+db3+db8+dbL
    def row(i,j):
        cx=(B[i]-B[j])/TWO_PI; cuL=-(dbL[i]-dbL[j])/TWO_PI
        rhs=(a[i]-a[j])+(1/TWO_PI)*((db3[i]-db3[j])*u3+(db8[i]-db8[j])*u8)
        return [cx,cuL],rhs
    r1,rhs1=row(0,1); r2,rhs2=row(1,2)
    x,uL=np.linalg.solve(np.array([r1,r2]),np.array([rhs1,rhs2]))
    invG=a[0]-(1/TWO_PI)*(B[0]*x-db3[0]*u3-db8[0]*u8-dbL[0]*uL)
    return x,uL,invG
for M8 in [2.7e3, 1e4, 1e5]:
    x,uL,invG = solve2(np.log(M8/MZ))
    MG=MZ*np.exp(x); ML=MZ*np.exp(uL)
    print(f"  octet@{M8:.1e} GeV -> VL@{ML:.2e} GeV, M_GUT={MG:.2e} GeV, 1/aGUT={invG:.1f}")
