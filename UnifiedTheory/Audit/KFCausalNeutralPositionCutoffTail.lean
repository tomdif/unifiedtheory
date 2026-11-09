/- A quantitative L2 cutoff-removal estimate controlled by the actual
charged mixed-plane tail. The bound is uniform in neutral frequency and
does not assume that the cutoff preserves the charge-averaged form. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (input)
open UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharge (norm_difference_square)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (momentum position symmetricIndex)

def scalarError (δ r : ℝ) : ℝ := (Real.exp (-2*δ*r^2)-1)^2

theorem scalarError_bounds (δ : ℝ) (hδ : 0 ≤ δ) (r : ℝ) :
    0 ≤ scalarError δ r ∧ scalarError δ r ≤ 1 := by
  have he : Real.exp (-2*δ*r^2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hp := (Real.exp_pos (-2*δ*r^2)).le
  constructor
  · exact sq_nonneg _
  · unfold scalarError
    nlinarith [sq_nonneg (Real.exp (-2*δ*r^2))]

theorem scalarError_local (δ : ℝ) (hδ : 0 ≤ δ) (r R : ℝ) (hr : r^2 ≤ R^2) :
    scalarError δ r ≤ 4*δ^2*R^4 := by
  have he : Real.exp (-2*δ*r^2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  have hb : |Real.exp (-2*δ*r^2)-1| ≤ 2*δ*R^2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    nlinarith [Real.add_one_le_exp (-2*δ*r^2),
      mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*δ)]
  calc
    scalarError δ r = |Real.exp (-2*δ*r^2)-1|^2 := (sq_abs _).symm
    _ ≤ (2*δ*R^2)^2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by ring

theorem errorDensity_integrable (δ : ℝ) (hδ : 0 ≤ δ) (f : Hilbert) :
    Integrable (fun x : Joint 2 4 => scalarError δ (x (.inr 2))*‖(chargeCoordinates f) x‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates f))).mp
    (Lp.memLp (chargeCoordinates f))
  have hc : Continuous (fun x : Joint 2 4 => scalarError δ (x (.inr 2))) := by
    unfold scalarError
    fun_prop
  apply hi.mono' (hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2))
  filter_upwards [] with x
  change ‖scalarError δ (x (.inr 2))*‖(chargeCoordinates f) x‖^2‖ ≤ ‖(chargeCoordinates f) x‖^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (scalarError_bounds δ hδ _).1 (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (scalarError_bounds δ hδ _).2

theorem norm_difference_tail (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h R : ℝ) (f : Hilbert) :
    ‖input ε δ v hε hδ f-KFCausalNeutralPositionCharge.action v f‖^2 ≤
      4*δ^2*R^4*‖f‖^2+planeTail h R 1 f := by
  let S := {x : Joint 2 4 | R^2 ≤ momentum h 1 x^2+position 1 x^2}
  have hS : MeasurableSet S := by
    apply measurableSet_le measurable_const
    unfold momentum position
    fun_prop
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates f))).mp
    (Lp.memLp (chargeCoordinates f))
  have hm : (∫ x : Joint 2 4, ‖(chargeCoordinates f) x‖^2) = ‖f‖^2 := by
    rw [← KFCausalAveragedEnergyGraph.l2_norm_square,chargeCoordinates.norm_map]
  rw [norm_difference_square,← hm,planeTail,← integral_indicator hS,← integral_const_mul,
    ← integral_add (hi.const_mul _) (hi.indicator hS)]
  apply integral_mono_ae (errorDensity_integrable δ hδ.le f) ((hi.const_mul _).add (hi.indicator hS))
  filter_upwards [] with x
  change scalarError δ (x (.inr 2))*‖(chargeCoordinates f) x‖^2 ≤
    4*δ^2*R^4*‖(chargeCoordinates f) x‖^2+S.indicator (fun y => ‖(chargeCoordinates f) y‖^2) x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    apply (mul_le_of_le_one_left (sq_nonneg _) (scalarError_bounds δ hδ.le _).2).trans
    exact le_add_of_nonneg_left (by positivity)
  · rw [Set.indicator_of_notMem hx,add_zero]
    have hr : (x (.inr 2))^2 ≤ R^2 := by
      change ¬R^2 ≤ momentum h 1 x^2+(x (.inr 2))^2 at hx
      nlinarith [sq_nonneg (momentum h 1 x)]
    exact mul_le_mul_of_nonneg_right (scalarError_local δ hδ.le _ R hr) (sq_nonneg _)

theorem expectation_difference (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    ‖inner ℂ f (input ε δ v hε hδ f)-inner ℂ f (KFCausalNeutralPositionCharge.action v f)‖ ≤
      ‖f‖*‖input ε δ v hε hδ f-KFCausalNeutralPositionCharge.action v f‖ := by
  rw [← inner_sub_right]
  exact norm_inner_le_norm _ _

#print axioms scalarError_bounds
#print axioms scalarError_local
#print axioms errorDensity_integrable
#print axioms norm_difference_tail
#print axioms expectation_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail
