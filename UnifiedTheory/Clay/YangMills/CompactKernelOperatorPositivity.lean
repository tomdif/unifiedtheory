/- A constructed continuous Hilbert feature turns the actual L² kernel
quadratic form into an inner product of Bochner integrals. Density then proves
positivity for every L² vector. The feature identity is an explicit geometric
input, not a supplied positivity assumption on the integral operator. -/
import UnifiedTheory.Clay.YangMills.CompactKernelOperator
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactKernelOperatorPositivity
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
/-- Moving a Bochner integral through the conjugate-linear argument of the inner product. -/
theorem integral_inner_left {F : X → H} (hF : Integrable F μ) (v : H) :
    (∫ x, inner ℂ (F x) v ∂μ) = inner ℂ (∫ x, F x ∂μ) v := by
  simp_rw [← inner_conj_symm (F _) v]
  rw [integral_conj, integral_inner hF]
  exact inner_conj_symm _ _

/-- A genuine continuous Hilbert feature gives the actual kernel quadratic form. -/
theorem continuous_quadratic (K : C(X × X, ℝ)) (Φ : X → H) (hΦ : Continuous Φ)
    (hGram : ∀ x y, inner ℂ (Φ x) (Φ y) = (K (x, y) : ℂ)) (f : C(X, ℂ)) :
    inner ℂ (ContinuousMap.toLp 2 μ ℂ f)
      (CompactKernelOperator.operator μ K (ContinuousMap.toLp 2 μ ℂ f)) =
      inner ℂ (∫ x, f x • Φ x ∂μ) (∫ x, f x • Φ x ∂μ) := by
  have hi : Integrable (fun x => f x • Φ x) μ :=
    (f.continuous.smul hΦ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change inner ℂ (ContinuousMap.toLp 2 μ ℂ f)
    (ContinuousMap.toLp 2 μ ℂ
      (CompactKernelOperator.smoothing μ K (ContinuousMap.toLp 2 μ ℂ f))) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp, ← integral_inner_left μ hi]
  simp_rw [← integral_inner hi, inner_smul_left, inner_smul_right, hGram,
    CompactKernelOperator.smoothing_continuous_input, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  ring

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace H] in
/-- A real-valued Hilbert Gram kernel is symmetric. -/
theorem gram_symm (K : C(X × X, ℝ)) (Φ : X → H)
    (hGram : ∀ x y, inner ℂ (Φ x) (Φ y) = (K (x, y) : ℂ)) (x y : X) :
    K (x, y) = K (y, x) := by
  apply Complex.ofReal_injective
  rw [← hGram, ← inner_conj_symm, hGram]
  simp

variable [SecondCountableTopology X] [NormalSpace X] [μ.WeaklyRegular]

/-- Positivity extends to every actual L² vector by density, not an assumed operator axiom. -/
theorem operator_positive (K : C(X × X, ℝ)) (Φ : X → H) (hΦ : Continuous Φ)
    (hGram : ∀ x y, inner ℂ (Φ x) (Φ y) = (K (x, y) : ℂ)) :
    (CompactKernelOperator.operator μ K).IsPositive := by
  have hs := CompactKernelOperator.operator_symmetric μ K (gram_symm K Φ hGram)
  refine ⟨hs, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (CompactKernelOperator.operator μ K f) f).re
  have hsf : inner ℂ (CompactKernelOperator.operator μ K f) f =
      inner ℂ f (CompactKernelOperator.operator μ K f) := hs f f
  rw [hsf]
  apply (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction_on
    (p := fun f => 0 ≤ (inner ℂ f (CompactKernelOperator.operator μ K f)).re)
  · apply isClosed_le continuous_const
    exact Complex.continuous_re.comp
      (continuous_id.inner (CompactKernelOperator.operator μ K).continuous)
  · intro g
    rw [continuous_quadratic μ K Φ hΦ hGram]
    exact inner_self_nonneg (𝕜 := ℂ) (x := ∫ x, g x • Φ x ∂μ)

end
end UnifiedTheory.Clay.YangMills.CompactKernelOperatorPositivity
