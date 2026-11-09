/- The removable scalar quotient in the squeeze commutator, with its
actual zero value. No vector generator derivative is needed. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
import Mathlib.Analysis.Calculus.DSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (difference)

def realDifference (d a : ℝ) : ℝ := Real.exp (d*a)-Real.exp (-(d*a))

theorem realDifference_derivative (d a : ℝ) :
    HasDerivAt (realDifference d) (d*(Real.exp (d*a)+Real.exp (-(d*a)))) a := by
  have hd := (((hasDerivAt_id a).const_mul d).exp).sub
    (((hasDerivAt_id a).const_mul d).neg.exp)
  convert hd using 1
  dsimp
  ring

def normalized (a : ℝ) (i : Fin 8) : ℂ := (dslope (realDifference (degree i)) 0 a : ℝ)

theorem normalized_zero (i : Fin 8) : normalized 0 i = (2*degree i : ℝ) := by
  rw [normalized,dslope_same,(realDifference_derivative (degree i) 0).deriv]
  simp only [mul_zero,neg_zero,Real.exp_zero]
  congr 1
  ring

theorem normalized_continuous (i : Fin 8) : Continuous (fun a => normalized a i) := by
  apply Complex.continuous_ofReal.comp
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha : a = 0
  · subst a
    exact continuousAt_dslope_same.mpr (realDifference_derivative (degree i) 0).differentiableAt
  · exact (continuousAt_dslope_of_ne ha).mpr
      (realDifference_derivative (degree i) a).continuousAt

theorem normalized_scale (a : ℝ) (i : Fin 8) : (a:ℂ)*normalized a i = difference a i := by
  have he := sub_smul_dslope (realDifference (degree i)) (0:ℝ) a
  simp only [sub_zero,smul_eq_mul,realDifference,mul_zero,neg_zero,Real.exp_zero,
    sub_self,sub_zero] at he
  unfold normalized difference
  exact_mod_cast he

theorem normalized_quotient (a : ℝ) (ha : a ≠ 0) (i : Fin 8) :
    normalized a i = (a:ℂ)⁻¹*difference a i := by
  rw [← normalized_scale]
  simp only [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha),one_mul]

#print axioms realDifference_derivative
#print axioms normalized_zero
#print axioms normalized_continuous
#print axioms normalized_scale
#print axioms normalized_quotient
end
end UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients
