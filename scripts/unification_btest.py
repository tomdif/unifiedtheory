"""B-test: three 1-loop lines 1/alpha_i unify iff (b2-b3)/(b1-b2) = A23/A12,
with A_ij = 1/alpha_i - 1/alpha_j at M_Z (measured). Fermion in rep R adds
(2/3)*T(R_i) per Weyl to b_i. Adjoint content is octet(8,1,0)+triplet(1,3,0)+
singlet(1,1,0), ALL hypercharge 0. Question: does the ADJOINT CONTENT unify?"""

# measured couplings at M_Z (GUT-normalized 1/alpha_1)
inv_a1, inv_a2, inv_a3 = 59.0, 29.6, 8.5
A12 = inv_a1 - inv_a2
A23 = inv_a2 - inv_a3
target = A23 / A12
print(f"Unification target A23/A12 = {target:.4f}")

def bratio(b1,b2,b3):
    return (b2-b3)/(b1-b2)

# SM one-loop
b_sm = (41/10, -19/6, -7)
print(f"SM:                    b={tuple(round(x,3) for x in b_sm)}  B-ratio={bratio(*b_sm):.4f}")

# Dynkin indices: T(adj SU(3))=3, T(adj SU(2))=2 ; hypercharge T1=(3/5)*Y^2*states
def add(b, dT, nWeyl):  # dT=(T1,T2,T3), nWeyl multiplicity
    return tuple(b[i] + (2/3)*dT[i]*nWeyl for i in range(3))

# adjoint content, take as Dirac (2 Weyl) octet + Dirac triplet (Y=0 -> no b1 shift)
b = add(b_sm, (0,0,3), 2)   # octet Dirac
b = add(b, (0,2,0), 2)      # triplet Dirac
print(f"SM + octet + triplet (Dirac):  b={tuple(round(x,3) for x in b)}  B-ratio={bratio(*b):.4f}")

# Weyl version
bw = add(add(b_sm,(0,0,3),1),(0,2,0),1)
print(f"SM + octet + triplet (Weyl):   b={tuple(round(x,3) for x in bw)}  B-ratio={bratio(*bw):.4f}")

# what does it take? add VL lepton doublets (1,2,-1/2) -- carry hypercharge, shift b1,b2
# T1 for one Weyl (1,2,y): (3/5)*y^2 * 2(doublet states)/2 ... use (3/5)*Y^2 summed over states
def vl_lepton_doublet_weyl():  # (1,2,1/2)+(1,2,-1/2) = one Dirac doublet = 2 Weyl
    T1 = (3/5)*( (1/2)**2 )*2   # 2 states in doublet, |Y|=1/2
    T2 = 1/2 * 2 / 2            # T(fund SU2)=1/2 per Weyl doublet... T2=1/2 each
    return (T1, 1/2, 0)
print("\n--- can the ADJOINT CONTENT alone reach target? ---")
print(f"  adjoint (octet+triplet+singlet, all Y=0): B-ratio={bratio(*b):.4f} vs target {target:.4f}")
print(f"  -> shift {bratio(*b)-bratio(*b_sm):+.4f} from SM; target needs {target-bratio(*b_sm):+.4f}")
gap = target - bratio(*b)
print(f"  RESIDUAL GAP to target after octet+triplet: {gap:+.4f}")
print("  octet+triplet are Y=0 -> CANNOT move b1; reaching target needs HYPERCHARGED matter")
print("  (VL leptons), which the adjoint/connection sector (all Y=0) does NOT supply.")
