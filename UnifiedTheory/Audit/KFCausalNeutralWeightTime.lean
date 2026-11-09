/- The neutral-test error coefficients are exactly time independent.
Only ratios among the three matter-channel weights occur, so their common
exponential time factor cancels, including when a coupling vanishes. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator
import UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralWeightTime
noncomputable section
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (weight_transition timeScale)

theorem weightedLinear_apply (w : Fin 8 → ℂ) (y : Outputs) :
    weightedLinear w y = WithLp.toLp 2
      ![0,0,0,0,0,-(w 5*(w 7)⁻¹) • y 7,(-2:ℂ) • ((w 6*(w 5)⁻¹) • y 5),0] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [weightedLinear,linearTerm,scaleOutput,mix,mixValues,smul_add,smul_sub,smul_smul]
  all_goals module

theorem weightedQuadratic_apply (w : Fin 8 → ℂ) (y : Outputs) :
    weightedQuadratic w y = WithLp.toLp 2 ![0,0,0,0,0,0,(w 6*(w 7)⁻¹) • y 7,0] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [weightedQuadratic,quadraticTerm,scaleOutput,mix,mixValues,smul_add,smul_sub,smul_smul]
  all_goals module

theorem ratio_scale (a b c : ℂ) (ha : a ≠ 0) :
    (a*b)*(a*c)⁻¹ = b*c⁻¹ := by
  rw [mul_inv_rev]
  calc
    a*b*(c⁻¹*a⁻¹) = (a*a⁻¹)*(b*c⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ ha,one_mul]

theorem matter_ratio_time (m g k s t : ℝ) (i j : Fin 8) (hi : ¬ i.val < 3) (hj : ¬ j.val < 3) :
    energyWeight m g k t i*(energyWeight m g k t j)⁻¹ =
      energyWeight m g k s i*(energyWeight m g k s j)⁻¹ := by
  rw [weight_transition m g k s t i,weight_transition m g k s t j]
  simp only [timeScale,if_neg hi,if_neg hj]
  exact ratio_scale _ _ _ (by simp)

theorem weightedLinear_time (m g k s t : ℝ) :
    weightedLinear (energyWeight m g k t) = weightedLinear (energyWeight m g k s) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [weightedLinear_apply,weightedLinear_apply,
    matter_ratio_time m g k s t 5 7 (by decide) (by decide),
    matter_ratio_time m g k s t 6 5 (by decide) (by decide)]

theorem weightedQuadratic_time (m g k s t : ℝ) :
    weightedQuadratic (energyWeight m g k t) = weightedQuadratic (energyWeight m g k s) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [weightedQuadratic_apply,weightedQuadratic_apply,
    matter_ratio_time m g k s t 6 7 (by decide) (by decide)]

theorem speedBound_time (m g k s t H v : ℝ) :
    speedBound (energyWeight m g k t) H v = speedBound (energyWeight m g k s) H v := by
  simp only [speedBound,weightedLinear_time m g k s t,weightedQuadratic_time m g k s t]

theorem speedBound_nonneg (w : Fin 8 → ℂ) (H v : ℝ) (hH : 0 ≤ H) : 0 ≤ speedBound w H v := by
  unfold speedBound
  positivity

#print axioms weightedLinear_apply
#print axioms weightedQuadratic_apply
#print axioms ratio_scale
#print axioms matter_ratio_time
#print axioms weightedLinear_time
#print axioms weightedQuadratic_time
#print axioms speedBound_time
#print axioms speedBound_nonneg

end
end UnifiedTheory.Audit.KFCausalNeutralWeightTime
