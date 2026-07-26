"""NEW derivation: proton lifetime from the framework's now-DERIVED unification scale.
M_GUT = reduced Planck mass (from EH coefficient c=1/2), alpha_GUT = 3/(32pi).
tau_p ~ (1/alpha_GUT^2) M_X^4 / m_p^5  (dimension-4 baryon-number operator)."""
import numpy as np
GeV_inv_to_s = 6.582e-25          # 1/GeV in seconds
s_per_yr = 3.156e7
mp = 0.938                         # proton mass, GeV
alpha_GUT = 3/(32*np.pi)           # framework algebraic value
MX_framework = 2.435e18            # reduced Planck mass (DERIVED this session, c=1/2)
MX_standard  = 2.0e16              # standard non-SUSY GUT scale (for comparison)
MX_susy      = 2.0e16              # MSSM

def tau_p(MX, alpha):
    tau_GeVinv = (1/alpha**2) * MX**4 / mp**5      # ~ dimensionful, GeV^-1
    return tau_GeVinv * GeV_inv_to_s / s_per_yr    # years

print("PROTON LIFETIME (dimension-6, p -> e+ pi0 scaling)")
print(f"  framework:  M_GUT = reduced Planck = {MX_framework:.2e} GeV, 1/a = {1/alpha_GUT:.1f}")
print(f"              tau_p ~ {tau_p(MX_framework, alpha_GUT):.1e} years")
print(f"  standard GUT: M_GUT = {MX_standard:.0e} GeV  -> tau_p ~ {tau_p(MX_standard, 1/40):.1e} years")
print(f"  experimental bound (Super-K, p->e+pi0):  ~ 2.4e34 years")
print()
ratio = tau_p(MX_framework, alpha_GUT)/2.4e34
print(f"  framework tau_p / experimental bound = {ratio:.1e}")
print("  => framework predicts the proton is EFFECTIVELY STABLE (beyond any conceivable")
print("     experiment), and DISTINCT from standard GUTs (which sit near the bound).")
print()
# Top-down cross-check: sin^2 theta_W(M_Z) from 3/8 at reduced Planck (SM 1-loop)
print("TOP-DOWN CROSS-CHECK: sin^2 theta_W(M_Z) run down from 3/8 at M_GUT")
MZ=91.19; TWO_PI=2*np.pi
b=(41/10,-19/6,-7.0)
for MX,lab in [(MX_framework,"reduced Planck"),(2e16,"2e16 (standard)")]:
    t=np.log(MX/MZ)
    inv_aGUT=1/alpha_GUT
    # 1/a_i(MZ) = inv_aGUT + (b_i/2pi) t   (running down: add b_i*t/2pi)
    inv1=inv_aGUT+b[0]/TWO_PI*t; inv2=inv_aGUT+b[1]/TWO_PI*t; inv3=inv_aGUT+b[2]/TWO_PI*t
    # sin^2 = (3/5 * 1/a1) / (1/a2 + 3/5 * 1/a1)  ... using a_Y=3/5 a_1
    s2 = ( (3/5)*inv1 ) / ( inv2 + (3/5)*inv1 )
    aem_inv = inv2 + (3/5)*inv1
    print(f"  M_GUT={lab:16s}: sin^2θ_W(M_Z)={s2:.3f}  1/a_EM(M_Z)={aem_inv:.1f}  1/a3(M_Z)={inv3:.1f}")
print(f"  measured: sin^2θ_W=0.2312, 1/a_EM=127.9, 1/a3=8.5  (SM-only running, no adjoint matter)")
