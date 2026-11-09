/- Quantitative removal of the charge-compatible radial cutoff. The
error is controlled by the existing second charged-plane tail, uniformly
in the neutral-position frequency. This is an L2 estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialTail
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
open UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail (scalarError scalarError_bounds scalarError_local)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_norm)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (momentum position)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)

def radiusError (h δ : ℝ) (x : Joint 2 4) : ℝ :=
  (Real.exp (-2*δ*planeRadius (momentumScale h) x)-1)^2

theorem radiusError_eq (h δ : ℝ) (x : Joint 2 4) :
    radiusError h δ x = scalarError δ (Real.sqrt (planeRadius (momentumScale h) x)) := by
  rw [scalarError,Real.sq_sqrt (planeRadius_nonneg _ _)]
  rfl

theorem radiusError_bounds (h δ : ℝ) (hδ : 0 ≤ δ) (x : Joint 2 4) :
    0 ≤ radiusError h δ x ∧ radiusError h δ x ≤ 1 := by
  rw [radiusError_eq]
  exact scalarError_bounds δ hδ _

theorem radiusError_local (h δ : ℝ) (hδ : 0 ≤ δ) (x : Joint 2 4) (R : ℝ)
    (hx : planeRadius (momentumScale h) x ≤ R^2) : radiusError h δ x ≤ 4*δ^2*R^4 := by
  rw [radiusError_eq]
  exact scalarError_local δ hδ _ R (by rw [Real.sq_sqrt (planeRadius_nonneg _ _)]; exact hx)

theorem norm_difference_square (h δ v : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    ‖action h δ v hδ f-KFCausalNeutralPositionCharge.action v f‖^2 =
      ∫ x : Joint 2 4, radiusError h δ x*‖(chargeCoordinates f) x‖^2 := by
  rw [← chargeCoordinates.norm_map (action h δ v hδ f-KFCausalNeutralPositionCharge.action v f),
    map_sub,KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (chargeCoordinates (action h δ v hδ f))
      (chargeCoordinates (KFCausalNeutralPositionCharge.action v f)),
    action_coe h δ v hδ f,KFCausalNeutralPositionCharge.charge_action_coe v f] with x hs hm hp
  rw [hs]
  simp only [Pi.sub_apply,hm,hp]
  have he : symbol h δ v x*(chargeCoordinates f) x-scalar (v*x (.inr 3))*(chargeCoordinates f) x =
      ((Real.exp (-2*δ*planeRadius (momentumScale h) x)-1:ℝ):ℂ)*
        (scalar (v*x (.inr 3))*(chargeCoordinates f) x) := by
    unfold symbol
    push_cast
    ring
  rw [he,norm_mul,norm_mul,scalar_norm,one_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

theorem errorDensity_integrable (h δ : ℝ) (hδ : 0 ≤ δ) (f : Hilbert) :
    Integrable (fun x : Joint 2 4 => radiusError h δ x*‖(chargeCoordinates f) x‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates f))).mp
    (Lp.memLp (chargeCoordinates f))
  have hc : Continuous (radiusError h δ) := by
    unfold radiusError planeRadius
    fun_prop
  apply hi.mono' (hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2))
  filter_upwards [] with x
  change ‖radiusError h δ x*‖(chargeCoordinates f) x‖^2‖ ≤ ‖(chargeCoordinates f) x‖^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (radiusError_bounds h δ hδ _).1 (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (radiusError_bounds h δ hδ _).2

theorem norm_difference_tail (h δ v : ℝ) (hδ : 0 < δ) (R : ℝ) (f : Hilbert) :
    ‖action h δ v hδ f-KFCausalNeutralPositionCharge.action v f‖^2 ≤
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
  apply integral_mono_ae (errorDensity_integrable h δ hδ.le f) ((hi.const_mul _).add (hi.indicator hS))
  filter_upwards [] with x
  change radiusError h δ x*‖(chargeCoordinates f) x‖^2 ≤
    4*δ^2*R^4*‖(chargeCoordinates f) x‖^2+S.indicator (fun y => ‖(chargeCoordinates f) y‖^2) x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    apply (mul_le_of_le_one_left (sq_nonneg _) (radiusError_bounds h δ hδ.le _).2).trans
    exact le_add_of_nonneg_left (by positivity)
  · rw [Set.indicator_of_notMem hx,add_zero]
    have hr : planeRadius (momentumScale h) x ≤ R^2 := by
      exact (not_le.mp hx).le
    exact mul_le_mul_of_nonneg_right (radiusError_local h δ hδ.le x R hr) (sq_nonneg _)

theorem expectation_difference (h δ v : ℝ) (hδ : 0 < δ) (f : Hilbert) :
    ‖inner ℂ f (action h δ v hδ f)-inner ℂ f (KFCausalNeutralPositionCharge.action v f)‖ ≤
      ‖f‖*‖action h δ v hδ f-KFCausalNeutralPositionCharge.action v f‖ := by
  rw [← inner_sub_right]
  exact norm_inner_le_norm _ _

#print axioms radiusError_eq
#print axioms radiusError_bounds
#print axioms radiusError_local
#print axioms norm_difference_square
#print axioms errorDensity_integrable
#print axioms norm_difference_tail
#print axioms expectation_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialTail
