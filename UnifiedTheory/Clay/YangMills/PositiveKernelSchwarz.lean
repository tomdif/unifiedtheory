/- Mixed integral Cauchy--Schwarz for a genuine continuous positive kernel.
The two sources are independent; no positivity of either source is assumed. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.PositiveKernelSchwarz
noncomputable section
open MeasureTheory PositiveKernelForm PositiveKernelInsertion KernelHilbertCompletion

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def mixed (K : PositiveKernel X) (f g : X → ℂ) : ℂ :=
  ∫ z : X × X, star (f z.1) * K.value z * g z.2 ∂μ.prod μ

theorem mixed_eq_inner (K : PositiveKernel X) (hK : Continuous K.value)
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    mixed μ K f g = inner ℂ (∫ x, f x • canonical K x ∂μ)
      (∫ x, g x • canonical K x ∂μ) := by
  have hi (h : X → ℂ) (hh : Continuous h) :
      Integrable (fun x => h x • canonical K x) μ :=
    (hh.smul (WilsonSlabPositivity.continuous_canonical K hK)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm : Integrable (fun z : X × X => star (f z.1) * K.value z * g z.2)
      (μ.prod μ) :=
    ((((continuous_star.comp hf).comp continuous_fst).mul hK).mul
      (hg.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [mixed, integral_prod _ hm,
    ← CompactKernelOperatorPositivity.integral_inner_left μ (hi f hf)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_inner (hi g hg)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [inner_smul_left, inner_smul_right, canonical_inner]
  simp only [Complex.star_def]
  ring

theorem schwarz (K : PositiveKernel X) (hK : Continuous K.value)
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ‖mixed μ K f g‖^2 ≤ (form μ K f).re * (form μ K g).re := by
  rw [mixed_eq_inner μ K hK f g hf hg, form_eq_inner μ K hK f hf,
    form_eq_inner μ K hK g hg]
  let u := ∫ x, f x • canonical K x ∂μ
  let v := ∫ x, g x • canonical K x ∂μ
  change ‖inner ℂ u v‖^2 ≤ RCLike.re (inner ℂ u u) * RCLike.re (inner ℂ v v)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) u v) 2

end
end UnifiedTheory.Clay.YangMills.PositiveKernelSchwarz
