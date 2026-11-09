/- The proved radial time-window constant is bounded uniformly on
every bounded neutral-frequency interval, at fixed positive cutoffs. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialResponseWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalRadialResponseFrequencyBound
noncomputable section
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (stripBound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (kineticConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialResponseWindow (windowBound)

theorem stripBound_frequency (ε δ v V : ℝ) (hδ : 0 < δ) (hv : |v| ≤ V) :
    stripBound ε δ v ≤ stripBound ε δ V := by
  apply Real.exp_le_exp.mpr
  have hs := pow_le_pow_left₀ (abs_nonneg v) hv 2
  rw [sq_abs] at hs
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) (by positivity)

theorem responseConstant_frequency (ε δ v V : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hv : |v| ≤ V) :
    responseConstant ε δ v ≤ responseConstant ε δ V :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (stripBound_frequency ε δ v V hδ hv) (by norm_num)) (by positivity)

theorem kineticConstant_frequency (ε δ v V : ℝ) (hv : |v| ≤ V) :
    kineticConstant ε δ v ≤ kineticConstant ε δ V := by
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  unfold kineticConstant KFCausalNeutralPositionRadialKineticGraph.responseConstant
  rw [abs_of_nonneg hV]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hv) (Real.sqrt_nonneg _)) (by positivity)

theorem windowBound_nonneg (ε δ v B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    0 ≤ windowBound ε δ v B := by
  exact add_nonneg (mul_nonneg (responseConstant_nonneg ε δ v hε) hB)
    (mul_nonneg (mul_nonneg (by norm_num)
      (KFCausalNeutralPositionRadialKineticGraph.responseConstant_nonneg ε δ v)) (Real.sqrt_nonneg _))

theorem windowBound_frequency (ε δ v V B : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hB : 0 ≤ B) (hv : |v| ≤ V) : windowBound ε δ v B ≤ windowBound ε δ V B :=
  add_le_add (mul_le_mul_of_nonneg_right (responseConstant_frequency ε δ v V hε hδ hv) hB)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (kineticConstant_frequency ε δ v V hv) (by norm_num))
      (Real.sqrt_nonneg _))

#print axioms stripBound_frequency
#print axioms responseConstant_frequency
#print axioms kineticConstant_frequency
#print axioms windowBound_nonneg
#print axioms windowBound_frequency

end
end UnifiedTheory.Audit.KFCausalRadialResponseFrequencyBound
