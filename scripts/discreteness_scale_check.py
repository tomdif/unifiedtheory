"""Is the framework's discreteness scale ~10^19 GeV, and is that a DERIVATION or an
INPUT? Honest accounting."""
import numpy as np
MP   = 1.2209e19     # Planck mass (non-reduced), GeV
MPr  = 2.435e18      # reduced Planck mass, GeV
inv_alpha_framework = 32*np.pi/3   # framework's algebraic boundary value 1/alpha = 32pi/3

print("DISCRETENESS SCALE")
print(f"  framework input (PhysicsFromCounting: 'ONE measured constant M_P')  = {MP:.3e} GeV")
print(f"  = ell_Planck at Planck density (CouplingUnification: ell=rho^-1/4)   -> NOT derived, INPUT")
print()
print("GAUGE-UNIFICATION SCALE (output of RG running, triplet@2.7 TeV DM, multi-threshold)")
for label,MG,inv in [("VL@1e14",6.9e18,32.9),("VL@1e8",1.62e19,31.5),("VL@1e3",3.29e19,30.2)]:
    print(f"  {label:8s}: M_GUT = {MG:.2e} GeV   M_GUT/M_P = {MG/MP:.2f}   1/alpha_GUT(run) = {inv}")
print()
print("UNIFIED COUPLING (independent cross-check)")
print(f"  framework algebraic 1/alpha = 32*pi/3 = {inv_alpha_framework:.2f}")
print(f"  RG running at the meeting scale        = 30 - 33")
print()
print("SORKIN Lambda (why the cosmological constant does NOT fix the scale)")
print("  Lambda_pred = 1/sqrt(V):  ell_disc CANCELS  (Lambda_abs = 1/(ell^2 sqrt(N)),")
print("  N = V/ell^4  ->  Lambda_abs = 1/sqrt(V), independent of ell_disc).")
print("  So the CC is a successful Lambda<->V postdiction, NOT a scale determination.")
print()
print("VERDICT")
print("  * Discreteness scale = M_P ~ 1.22e19 GeV is INPUT (one measured constant), not derived.")
print("  * NON-TRIVIAL: RG running of the MEASURED low-E couplings, with the framework's")
print("    PREDICTED matter (adjoint octet+triplet + 2.7 TeV triplet DM + minimal VL),")
print("    unifies at M_GUT ~ (0.6 - 2.7) x M_P -- i.e. AT the discreteness scale --")
print("    with 1/alpha ~ 33 = the framework's independent algebraic 32pi/3.")
print("  * So it is NOT two independent computations of 10^19 agreeing; the scale is Planck")
print("    by construction. What lands on 10^19 non-trivially is the gauge-unification OUTPUT")
print("    (both the scale, ~M_P, and the coupling, ~32pi/3).")
