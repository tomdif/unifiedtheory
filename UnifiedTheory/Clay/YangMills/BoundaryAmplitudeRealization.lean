/- Explicit L2 realization of the finite reflected form. The boundary measure
here is Z^{-1} w dμB; the amplitudes retain their half-partition factor. This
weighted realization proves null-vector identities without assuming dynamics. -/
import UnifiedTheory.Clay.YangMills.BoundaryReflectionGluing
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundaryAmplitudeRealization
noncomputable section
open MeasureTheory BoundaryReflectionGluing
open scoped ENNReal

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

theorem amplitude_continuous (A : B × X → ℝ) (hA : Continuous A)
    (f : B × X → ℂ) (hf : Continuous f) : Continuous (amplitude μX A f) := by
  have hc : Continuous (fun z : B × X => (Real.exp (-A z) : ℂ) * f z) := by fun_prop
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  apply continuous_of_dominated (bound := fun _ => M)
  · intro b
    exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall (fun x => hM _ ⟨(b, x), rfl⟩)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x => hc.comp (continuous_id.prodMk continuous_const))

def boundaryMeasure (w : B → ℝ) (A : B × X → ℝ) : Measure B :=
  (partition μB μX w A)⁻¹ • μB.withDensity (fun b => ENNReal.ofReal (w b))

theorem boundaryMeasure_finite (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A) : IsFiniteMeasure (boundaryMeasure μB μX w A) := by
  have hi := hcw.integrable_of_hasCompactSupport (μ := μB) (HasCompactSupport.of_compactSpace _)
  letI : IsFiniteMeasure (μB.withDensity (fun b => ENNReal.ofReal (w b))) :=
    isFiniteMeasure_withDensity (by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun b => (hw b).le))]
      exact ENNReal.ofReal_ne_top)
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr
    (partition_positive μB μX w hcw hw A hA).ne')

theorem raw_pairing_identity (w : B → ℝ) (hcw : Continuous w)
    (A : B × X → ℝ) (hA : Continuous A)
    (f g : B × X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z, (weight w A z : ℂ) *
      (star (halfObservable f (reflection z)) * halfObservable g z) ∂μB.prod (μX.prod μX)) =
      ∫ b, (w b : ℂ) * (star (amplitude μX A f b) * amplitude μX A g b) ∂μB := by
  have hc : Continuous (fun z : B × (X × X) => (weight w A z : ℂ) *
      (star (halfObservable f (reflection z)) * halfObservable g z)) := by
    unfold halfObservable reflection weight
    fun_prop
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro b
  let ψ : X → ℂ := fun x => (Real.exp (-A (b,x)) : ℂ) * f (b,x)
  let ξ : X → ℂ := fun x => (Real.exp (-A (b,x)) : ℂ) * g (b,x)
  have he (z : X × X) : (weight w A (b,z) : ℂ) *
      (star (halfObservable f (reflection (b,z))) * halfObservable g (b,z)) =
      (w b : ℂ) * (star (ψ z.1) * ξ z.2) := by
    dsimp only [ψ, ξ, weight, halfObservable, reflection, Prod.swap]
    simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_prod_mul (fun x => star (ψ x)) ξ]
  simp only [Complex.star_def, integral_conj, amplitude, ψ, ξ]

theorem pairing_identity (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
    (A : B × X → ℝ) (hA : Continuous A)
    (f g : B × X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ z, star (halfObservable f (reflection z)) * halfObservable g z ∂law μB μX w A) =
      ∫ b, star (amplitude μX A f b) * amplitude μX A g b ∂boundaryMeasure μB μX w A := by
  unfold law boundaryMeasure
  rw [integral_smul_measure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      (weight_continuous w hcw A hA).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hcw.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (weight_positive w hw A _).le,
    ENNReal.toReal_ofReal (hw _).le]
  congr 1
  exact raw_pairing_identity μB μX w hcw A hA f g hf hg

variable (w : B → ℝ) (hcw : Continuous w) (hw : ∀ b, 0 < w b)
  (A : B × X → ℝ) (hA : Continuous A)

include hcw hw hA in
def amplitudeL2 (f : C(B × X, ℂ)) : Lp ℂ 2 (boundaryMeasure μB μX w A) := by
  letI := boundaryMeasure_finite μB μX w hcw hw A hA
  exact ContinuousMap.toLp 2 (boundaryMeasure μB μX w A) ℂ
    ⟨amplitude μX A f, amplitude_continuous μX A hA f f.continuous⟩

include hcw hw hA in
theorem amplitudeL2_inner (f g : C(B × X, ℂ)) :
    inner ℂ (amplitudeL2 μB μX w hcw hw A hA f) (amplitudeL2 μB μX w hcw hw A hA g) =
      ∫ z, star (halfObservable f (reflection z)) * halfObservable g z ∂law μB μX w A := by
  letI := boundaryMeasure_finite μB μX w hcw hw A hA
  rw [amplitudeL2, amplitudeL2, ContinuousMap.inner_toLp,
    pairing_identity μB μX w hcw hw A hA f g f.continuous g.continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

include hcw hw hA in
theorem reflected_null_iff (f : C(B × X, ℂ)) :
    (∫ z, star (halfObservable f (reflection z)) * halfObservable f z ∂law μB μX w A) = 0 ↔
      amplitudeL2 μB μX w hcw hw A hA f = 0 := by
  rw [← amplitudeL2_inner μB μX w hcw hw A hA]
  exact inner_self_eq_zero

end
end UnifiedTheory.Clay.YangMills.BoundaryAmplitudeRealization
