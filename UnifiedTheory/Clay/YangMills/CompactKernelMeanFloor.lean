/- A continuous positive kernel with constant Haar row integral has a
positive remainder after its constant mode is removed. The mean is an actual
Bochner integral in the constructed Hilbert completion. No reflection
positivity of a lattice law or ground-state marginal is assumed here. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabPositivity
import UnifiedTheory.Clay.YangMills.KernelHilbertRealization
import UnifiedTheory.Clay.YangMills.CompactKernelOperatorPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactKernelMeanFloor
noncomputable section
open MeasureTheory PositiveKernelForm KernelHilbertCompletion

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] (K : PositiveKernel X)

def meanFeature : Hilbert K := ∫ x, canonical K x ∂μ

def centeredFeature (x : X) : Hilbert K := canonical K x - meanFeature μ K

theorem canonical_integrable (hc : Continuous K.value) : Integrable (canonical K) μ :=
  (WilsonSlabPositivity.continuous_canonical K hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem canonical_mean_inner (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) (x : X) :
    inner ℂ (canonical K x) (meanFeature μ K) = (c : ℂ) := by
  rw [meanFeature, ← integral_inner (canonical_integrable μ K hc)]
  simpa only [canonical_inner] using hr x

theorem mean_canonical_inner (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) (x : X) :
    inner ℂ (meanFeature μ K) (canonical K x) = (c : ℂ) := by
  rw [← inner_conj_symm, canonical_mean_inner μ K hc c hr]
  exact Complex.conj_ofReal c

theorem mean_inner (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) :
    inner ℂ (meanFeature μ K) (meanFeature μ K) = (c : ℂ) := by
  conv_lhs => lhs; rw [meanFeature]
  rw [← CompactKernelOperatorPositivity.integral_inner_left μ
    (canonical_integrable μ K hc)]
  simp only [canonical_mean_inner μ K hc c hr, integral_const, probReal_univ, one_smul]

theorem mean_nonneg (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) : 0 ≤ c := by
  have h := inner_self_nonneg (𝕜 := ℂ) (x := meanFeature μ K)
  simpa only [mean_inner μ K hc c hr, Complex.ofReal_re] using h

theorem centered_inner (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) (x y : X) :
    inner ℂ (centeredFeature μ K x) (centeredFeature μ K y) =
      K.value (x, y) - (c : ℂ) := by
  simp only [centeredFeature, inner_sub_left, inner_sub_right, canonical_inner,
    canonical_mean_inner μ K hc c hr, mean_canonical_inner μ K hc c hr,
    mean_inner μ K hc c hr]
  ring

def centeredKernel : PositiveKernel X :=
  KernelHilbertRealization.vectorKernel (centeredFeature μ K)

theorem centeredKernel_value (hc : Continuous K.value) (c : ℝ)
    (hr : ∀ x, (∫ y, K.value (x, y) ∂μ) = (c : ℂ)) (x y : X) :
    (centeredKernel μ K).value (x, y) = K.value (x, y) - (c : ℂ) :=
  centered_inner μ K hc c hr x y

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem centeredKernel_continuous (hc : Continuous K.value) :
    Continuous (centeredKernel μ K).value := by
  have hf : Continuous (centeredFeature μ K) :=
    (WilsonSlabPositivity.continuous_canonical K hc).sub continuous_const
  exact (hf.comp continuous_fst).inner (hf.comp continuous_snd)

end
end UnifiedTheory.Clay.YangMills.CompactKernelMeanFloor
