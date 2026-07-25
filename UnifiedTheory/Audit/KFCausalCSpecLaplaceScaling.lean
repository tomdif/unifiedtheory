/-
  Audit/KFCausalCSpecLaplaceScaling.lean   (Volume sector → discharging tier 3)

  Tier 3 of the BDG continuum/residue derivations -- the ρ → ∞ ASYMPTOTIC SCALING that
  the goal-B/C theorems take as a per-layer hypothesis -- is NOT Lorentzian geometry.  Its
  analytic engine is the Laplace transform of a monomial, pure real analysis:

      ∫_0^∞ e^{-ρ t} t^n dt  =  n! / ρ^{n+1}.

  This is PROVED here (from Mathlib's Gamma integral + a change of variables), discharging
  the tier-3 scaling to a theorem.  After the tier-1 geometry writes a layer contribution
  as such an integral (with `n` set by the layer index and the shell-measure power), the
  `ρ^{-(n+1)}` factor -- hence the discreteness scale `ρ^{-2/d} ~ ℓ²` of the residue -- is
  now a consequence, not an assumed asymptotic.

  So the tier-3 citation shrinks to: "the layer contribution IS a monomial Laplace
  integral" (tier-1 geometry) + this lemma (proved).

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory Real Set

namespace UnifiedTheory.Audit.KFCausalCSpecLaplaceScaling

/-- The Gamma monomial integral: `∫_0^∞ e^{-x} x^n dx = n!`.  (Mathlib's Gamma integral,
with the `rpow`/`pow` bridge on `Ioi 0`.) -/
theorem gamma_monomial_integral (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ n = (Nat.factorial n : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial n, Real.Gamma_eq_integral (by positivity)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [← Real.rpow_natCast x n, show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring]

/-- **Monomial Laplace scaling (tier-3 engine).**  `∫_0^∞ e^{-ρ t} t^n dt = n! / ρ^{n+1}`
for `ρ > 0`.  The `ρ^{-(n+1)}` factor is the source of the discreteness scaling in the
BDG residue; here it is a theorem, not an assumption. -/
theorem laplace_monomial (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(ρ * t)) * t ^ n = (Nat.factorial n : ℝ) / ρ ^ (n + 1) := by
  have hcov := integral_comp_mul_left_Ioi (fun u => Real.exp (-u) * u ^ n) 0 hρ
  simp only [mul_zero, smul_eq_mul] at hcov
  rw [gamma_monomial_integral n] at hcov
  -- hcov : ∫ t in Ioi 0, exp(-(ρ*t)) * (ρ*t)^n = ρ⁻¹ * n!
  have hρn : ρ ^ n ≠ 0 := pow_ne_zero n hρ.ne'
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have key : (fun t => Real.exp (-(ρ * t)) * t ^ n)
      = fun t => (ρ ^ n)⁻¹ * (Real.exp (-(ρ * t)) * (ρ * t) ^ n) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [key, integral_const_mul, hcov, pow_succ]
  field_simp

#print axioms gamma_monomial_integral
#print axioms laplace_monomial

end UnifiedTheory.Audit.KFCausalCSpecLaplaceScaling
