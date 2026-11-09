/- A uniform small-squeeze bound on the actual full commutator output.
This controls every energy factor without a generator domain premise. -/
import UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalSqueezeRateBound
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
open UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients (realDifference realDifference_derivative)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)

def slopeBound : ℝ := 4*Real.exp 2

theorem slopeBound_positive : 0 < slopeBound := by unfold slopeBound; positivity

theorem degree_bound (i : Fin 8) : |degree i| ≤ 2 := by
  fin_cases i <;> norm_num [degree]

theorem difference_bound (a : ℝ) (ha : |a| ≤ 1) (i : Fin 8) :
    ‖difference a i‖ ≤ slopeBound*|a| := by
  have hb (b : ℝ) (hb : b ∈ Icc (-1:ℝ) 1) :
      ‖degree i*(Real.exp (degree i*b)+Real.exp (-(degree i*b)))‖ ≤ slopeBound := by
    have hp : |degree i*b| ≤ 2 := by
      rw [abs_mul]
      have hab : |b| ≤ 1 := abs_le.mpr hb
      nlinarith [degree_bound i,abs_nonneg (degree i),abs_nonneg b]
    have he := Real.exp_le_exp.mpr (abs_le.mp hp).2
    have hn := Real.exp_le_exp.mpr (neg_le.mpr (abs_le.mp hp).1)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
    unfold slopeBound
    nlinarith [degree_bound i,abs_nonneg (degree i),Real.exp_pos (2:ℝ)]
  have he := (convex_Icc (-1:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun b (_ : b ∈ Icc (-1:ℝ) 1) => (realDifference_derivative (degree i) b).hasDerivWithinAt)
    hb (by norm_num : (0:ℝ) ∈ Icc (-1:ℝ) 1) (abs_le.mp ha)
  simpa only [realDifference,mul_zero,neg_zero,Real.exp_zero,sub_self,sub_zero,
    Real.norm_eq_abs, difference,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using he

theorem differenceOutput_bound (a : ℝ) (ha : |a| ≤ 1) (x : Output (Fin 8) Hilbert) :
    ‖differenceOutput a x‖ ≤ (slopeBound*|a|)*‖x‖ := by
  have hc : 0 ≤ slopeBound*|a| := mul_nonneg slopeBound_positive.le (abs_nonneg _)
  have hs : ‖differenceOutput a x‖^2 ≤ (slopeBound*|a|)^2*‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [differenceOutput_apply,norm_smul,LinearIsometryEquiv.norm_map,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (difference_bound a ha i) 2)
      (sq_nonneg _)
  nlinarith [norm_nonneg (differenceOutput a x),norm_nonneg x,mul_nonneg hc (norm_nonneg x)]

theorem differenceOutputLp_bound (a : ℝ) (ha : |a| ≤ 1) (x : EnergyOutputSpace) :
    ‖differenceOutputLp a x‖ ≤ (slopeBound*|a|)*‖x‖ := by
  have hc : 0 ≤ slopeBound*|a| := mul_nonneg slopeBound_positive.le (abs_nonneg _)
  have ho : ‖differenceOutput a‖ ≤ slopeBound*|a| :=
    ContinuousLinearMap.opNorm_le_bound _ hc (differenceOutput_bound a ha)
  exact ((differenceOutput a).norm_compLp_le x).trans
    (mul_le_mul_of_nonneg_right ho (norm_nonneg x))

#print axioms slopeBound_positive
#print axioms degree_bound
#print axioms difference_bound
#print axioms differenceOutput_bound
#print axioms differenceOutputLp_bound
end
end UnifiedTheory.Audit.KFCausalSqueezeRateBound
