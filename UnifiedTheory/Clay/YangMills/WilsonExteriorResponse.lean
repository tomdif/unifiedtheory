/- Source-weighted actual response for rotations chosen from a block's
retained exterior. Conditional ground normalization is preserved before
integrating the correlated true exterior law. -/
import UnifiedTheory.Clay.YangMills.WilsonConditionalEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonExteriorResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonStationaryEntropy WilsonBlockRotation CompactDensityEntropy WilsonAveragedResponse
open WilsonPhysicalResponse WilsonGroundLocalComparison

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def selected (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (U : Slice n) : Slice n :=
  extend n S (q (outsideProjection n S U))*U

omit [NeZero n] in
theorem selected_continuous (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (hq : Continuous q) : Continuous (selected n S q) :=
  ((extend_continuous n S).comp (hq.comp (outsideProjection_continuous n S))).mul continuous_id

omit [NeZero n] in
theorem selected_assemble (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (r : Outside n S) (a : Inside n S) :
    selected n S q (WilsonBlockMarginal.assemble S (r,a)) =
      WilsonBlockMarginal.assemble S (r,q r*a) := by
  rw [selected, outsideProjection_assemble, extend_assemble]

theorem outside_integral (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (H : Outside n S → ℝ) (hH : Continuous H) :
    (∫ U, H (outsideProjection n S U) ∂groundLaw n β hβ) =
      ∫ r, H r ∂outsideLaw n β hβ S := by
  rw [outsideLaw_eq_map, integral_map
    (outsideProjection_continuous n S).measurable.aemeasurable hH.aestronglyMeasurable]

/-- The actual marginal may correlate the exterior weight and the chosen rotation. -/
theorem weighted_entropy_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (hq : Continuous q)
    (w : Outside n S → ℝ) (hw : Continuous w) (hw0 : ∀ r, 0 ≤ w r) :
    (∫ U, w (outsideProjection n S U)*rowEntropy n β hβ U (selected n S q U)
      ∂groundLaw n β hβ) ≤
      18*β*(∫ U, w (outsideProjection n S U)*cost n S (q (outsideProjection n S U))
        ∂groundLaw n β hβ) := by
  letI := outsideLaw_probability n β hβ S
  have hrow : Continuous (fun U : Slice n => rowEntropy n β hβ U (selected n S q U)) :=
    (rowEntropy_continuous n β hβ).comp (f := fun U : Slice n => (U,selected n S q U))
      (continuous_id.prodMk (selected_continuous n S q hq))
  have hF : Continuous (fun U : Slice n =>
      w (outsideProjection n S U)*rowEntropy n β hβ U (selected n S q U)) :=
    (hw.comp (outsideProjection_continuous n S)).mul hrow
  have hC : Continuous (fun r : Outside n S => w r*cost n S (q r)) :=
    hw.mul ((cost_continuous n S).comp hq)
  rw [← disintegration n β hβ S _ hF,
    outside_integral n β hβ S (fun r => w r*cost n S (q r)) hC]
  simp only [outsideProjection_assemble, selected_assemble]
  simp_rw [integral_const_mul]
  change (∫ r, w r*WilsonConditionalEntropy.meanEntropy n β hβ S r (q r)
    ∂outsideLaw n β hβ S) ≤ 18*β*(∫ r, w r*cost n S (q r) ∂outsideLaw n β hβ S)
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun r => mul_nonneg (hw0 r)
      (WilsonConditionalEntropy.meanEntropy_nonneg n β hβ S r (q r))))
    (continuous_integrable (outsideLaw n β hβ S) _ (continuous_const.mul hC))
  apply Filter.Eventually.of_forall
  intro r
  have h := mul_le_mul_of_nonneg_left
    (WilsonConditionalEntropy.meanEntropy_bound n β hβ S r (q r)) (hw0 r)
  simp only [Pi.mul_apply]
  nlinarith

/-- Both the rotation and its nonnegative source weight may depend on the actual exterior. -/
theorem weighted_response_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (hq : Continuous q)
    (w : Outside n S → ℝ) (hw : Continuous w) (hw0 : ∀ r, 0 ≤ w r)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ U, w (outsideProjection n S U)*
      (rowMean n β hβ f U-rowMean n β hβ f (selected n S q U))^2 ∂groundLaw n β hβ) ≤
      18*β*(hi-lo)^2*(∫ U, w (outsideProjection n S U)*
        cost n S (q (outsideProjection n S U)) ∂groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  have hW := hw.comp (outsideProjection_continuous n S)
  have hP := rowMean_continuous n β hβ f
  have hR := ((hP.sub (hP.comp (selected_continuous n S q hq))).pow 2)
  have hE : Continuous (fun U : Slice n => rowEntropy n β hβ U (selected n S q U)) :=
    (rowEntropy_continuous n β hβ).comp (f := fun U : Slice n => (U,selected n S q U))
      (continuous_id.prodMk (selected_continuous n S q hq))
  have h := integral_mono (continuous_integrable (groundLaw n β hβ) _ (hW.mul hR))
    (continuous_integrable (groundLaw n β hβ) _ (continuous_const.mul (hW.mul hE)))
    (fun U => by
      have h := mul_le_mul_of_nonneg_left
        (response_sq_le_rowEntropy n β hβ U (selected n S q U) f lo hi hf)
        (hw0 (outsideProjection n S U))
      simp only [Pi.mul_apply, Function.comp_apply]
      nlinarith)
  simp only [Pi.mul_apply, Function.comp_apply] at h
  rw [integral_const_mul] at h
  have hb := mul_le_mul_of_nonneg_left (weighted_entropy_bound n β hβ S q hq w hw hw0)
    (sq_nonneg (hi-lo))
  nlinarith

/-- Exact binding to the original full transfer on physical observables. -/
theorem physical_weighted_response_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3))
    (q : Outside n S → Inside n S) (hq : Continuous q)
    (w : Outside n S → ℝ) (hw : Continuous w) (hw0 : ∀ r, 0 ≤ w r)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ U, w (outsideProjection n S U)*
      ((∫ v, transition n β hβ U v*f v ∂WilsonSlabOperator.measure n) -
        (∫ v, transition n β hβ (selected n S q U) v*f v ∂WilsonSlabOperator.measure n))^2
      ∂groundLaw n β hβ) ≤ 18*β*(hi-lo)^2*
        (∫ U, w (outsideProjection n S U)*cost n S (q (outsideProjection n S U))
          ∂groundLaw n β hβ) := by
  simp_rw [← rowMean_eq_full n β hβ f hinv]
  exact weighted_response_bound n β hβ S q hq w hw hw0 f lo hi hf

end
end UnifiedTheory.Clay.YangMills.WilsonExteriorResponse
