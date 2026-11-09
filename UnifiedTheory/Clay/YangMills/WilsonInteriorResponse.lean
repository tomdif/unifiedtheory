/- Interior-dependent nonnegative weights in actual physical response.
The new error is the symmetric source energy of the square-root weight.
It is explicit and is not assumed to be paid for by transfer variance loss. -/
import UnifiedTheory.Clay.YangMills.WilsonWeightedEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonInteriorResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonStationaryEntropy CompactDensityEntropy WilsonAveragedResponse WilsonPhysicalResponse
open WilsonGroundLocalComparison WilsonWeightedEntropy

variable (n : ℕ) [NeZero n]

theorem square_weight_response (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (F f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ U, (F U)^2*(rowMean n β hβ f U-rowMean n β hβ f (q*U))^2 ∂groundLaw n β hβ) ≤
      (hi-lo)^2*(18*β*WilsonJointRotation.cost n q*mass n β hβ F +
        (sourceEnergy n β hβ q F+sourceEnergy n β hβ q⁻¹ F)/2) := by
  letI := groundLaw_probability n β hβ
  have hP := rowMean_continuous n β hβ f
  have hE : Continuous (fun U => (F U)^2*rowEntropy n β hβ U (q*U)) :=
    (F.continuous.pow 2).mul ((rowEntropy_continuous n β hβ).comp
      (f := fun U : Slice n => (U,q*U))
      (continuous_id.prodMk (continuous_const.mul continuous_id)))
  have hR : Continuous (fun U => (F U)^2*
      (rowMean n β hβ f U-rowMean n β hβ f (q*U))^2) :=
    (F.continuous.pow 2).mul ((hP.sub
      (hP.comp (f := fun U : Slice n => q*U) (continuous_const.mul continuous_id))).pow 2)
  have h := integral_mono (continuous_integrable (groundLaw n β hβ) _ hR)
    (continuous_integrable (groundLaw n β hβ) _ (continuous_const.mul hE)) (fun U => by
      have hh := mul_le_mul_of_nonneg_left
        (response_sq_le_rowEntropy n β hβ U (q*U) f lo hi hf) (sq_nonneg (F U))
      simp only [Pi.mul_apply]
      nlinarith)
  simp only [Pi.mul_apply] at h
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (WilsonWeightedEntropy.bound n β hβ q F)
    (sq_nonneg (hi-lo)))

/-- The responding observable uses the original full transfer on physical sources. -/
theorem physical_square_weight_response (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (F f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ U, (F U)^2*((∫ v, transition n β hβ U v*f v ∂WilsonSlabOperator.measure n) -
      (∫ v, transition n β hβ (q*U) v*f v ∂WilsonSlabOperator.measure n))^2
      ∂groundLaw n β hβ) ≤
      (hi-lo)^2*(18*β*WilsonJointRotation.cost n q*mass n β hβ F +
        (sourceEnergy n β hβ q F+sourceEnergy n β hβ q⁻¹ F)/2) := by
  simp_rw [← rowMean_eq_full n β hβ f hinv]
  exact square_weight_response n β hβ q F f lo hi hf

omit [NeZero n] in
def sqrtWeight (w : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨fun U => Real.sqrt (w U), w.continuous.sqrt⟩

omit [NeZero n] in
theorem sqrtWeight_square (w : C(Slice n, ℝ)) (hw : ∀ U, 0 ≤ w U) (U : Slice n) :
    (sqrtWeight n w U)^2 = w U := Real.sq_sqrt (hw U)

/-- Any continuous nonnegative weight, with no exterior-only restriction. -/
theorem nonnegative_weight_response (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (w f : C(Slice n, ℝ)) (hw : ∀ U, 0 ≤ w U) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ U, w U*((∫ v, transition n β hβ U v*f v ∂WilsonSlabOperator.measure n) -
      (∫ v, transition n β hβ (q*U) v*f v ∂WilsonSlabOperator.measure n))^2
      ∂groundLaw n β hβ) ≤
      (hi-lo)^2*(18*β*WilsonJointRotation.cost n q*(∫ U, w U ∂groundLaw n β hβ) +
        (sourceEnergy n β hβ q (sqrtWeight n w)+
          sourceEnergy n β hβ q⁻¹ (sqrtWeight n w))/2) := by
  have h := physical_square_weight_response n β hβ q (sqrtWeight n w) f hinv lo hi hf
  simpa only [mass, sqrtWeight_square n w hw] using h

end
end UnifiedTheory.Clay.YangMills.WilsonInteriorResponse
