/- The exact optimal coefficient for the physical center-odd row inequality.
The contrast itself attains the coefficient. Its complement is an actual
harmonic overlap of the original full transition rows. -/
import UnifiedTheory.Clay.YangMills.CompactPairedDensity
import UnifiedTheory.Clay.YangMills.WilsonCenterContrast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonContrastMoment
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist WilsonCenterContrast
open WilsonGroundLocalComparison WilsonPhysicalScore WilsonPhysicalVariance

variable (n : ℕ) [NeZero n]

def moment (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) : C(Slice n, ℝ) :=
  ⟨fun u => ∫ v, transition n β hβ u v * (contrast n i β hβ u v)^2
      ∂WilsonSlabOperator.measure n,
    GibbsMarginalTower.fiber_integral_continuous (WilsonSlabOperator.measure n) _
      ((WilsonHeatBathComparison.transitionMap n β hβ).continuous.mul
        ((contrast_continuous n i β hβ).pow 2))⟩

theorem moment_nonneg (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    0 ≤ moment n i β hβ u := integral_nonneg
  (fun v => mul_nonneg (transition_pos n β hβ u v).le (sq_nonneg _))

theorem moment_mixture (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    moment n i β hβ u = ∫ v,
      ((transition n β hβ u v + transition n β hβ (twist n i u) v)/2) *
        (contrast n i β hβ u v)^2 ∂WilsonSlabOperator.measure n := by
  exact (CompactPairedDensity.mixture_even (WilsonSlabOperator.measure n)
    (transition n β hβ u) (transition n β hβ (twist n i u))
    (fun v => (contrast n i β hβ u v)^2) (transition_continuous n β hβ u)
    (transition_continuous n β hβ _) ((source n i β hβ u).continuous.pow 2)
    (even_integral n i β hβ u _ (fun v => by rw [contrast_odd_right, neg_sq]))).symm

theorem moment_gauge (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (h : SliceGauge n Q) : moment n i β hβ (gaugeSlice h u) = moment n i β hβ u := by
  change (∫ v, _ ∂WilsonSlabOperator.measure n) = ∫ v, _ ∂WilsonSlabOperator.measure n
  apply integral_congr_ae
  filter_upwards with v
  rw [WilsonPhysicalResponse.full_transition_gauge_left, contrast_gauge_left]

theorem moment_even (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    moment n i β hβ (twist n i u) = moment n i β hβ u := by
  change (∫ v, _ ∂WilsonSlabOperator.measure n) = ∫ v, _ ∂WilsonSlabOperator.measure n
  simp_rw [contrast_odd_left, neg_sq]
  exact even_integral n i β hβ u _ (fun v => by rw [contrast_odd_right, neg_sq])

theorem source_square_step (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    step n β hβ ((source n i β hβ u)^2) u = moment n i β hβ u := by
  rw [step_full n β hβ _ (fun h v => by
    simp only [ContinuousMap.pow_apply, source, ContinuousMap.coe_mk, contrast_gauge_right])]
  rfl

/-- The contrast source has its first and second row moments exactly equal. -/
theorem source_step (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    step n β hβ (source n i β hβ u) u = moment n i β hβ u := by
  have hh := CompactPairedDensity.contrast_pairing (WilsonSlabOperator.measure n)
    (transition n β hβ u) (transition n β hβ (twist n i u)) (contrast n i β hβ u)
    (transition_continuous n β hβ u) (transition_continuous n β hβ _)
    (source n i β hβ u).continuous (transition_pos n β hβ u)
    (transition_pos n β hβ (twist n i u))
    (odd_integral n i β hβ u _ (contrast_odd_right n i β hβ u))
  rw [step_full n β hβ _ (fun h v => contrast_gauge_right n i β hβ u v h), moment_mixture]
  change (∫ v, transition n β hβ u v * contrast n i β hβ u v
    ∂WilsonSlabOperator.measure n) = _
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with v
  change _ * contrast n i β hβ u v * contrast n i β hβ u v = _
  ring

/-- The actual second contrast moment controls every physical odd source, with no likelihood cap. -/
theorem odd_square (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hf : ∀ u, f (twist n i u) = -f u)
    (u : Slice n) :
    (step n β hβ f u)^2 ≤ moment n i β hβ u * step n β hβ (f^2) u := by
  have hh := CompactPairedDensity.odd_response (WilsonSlabOperator.measure n)
    (transition n β hβ u) (transition n β hβ (twist n i u)) f
    (transition_continuous n β hβ u) (transition_continuous n β hβ _) f.continuous
    (transition_pos n β hβ u) (transition_pos n β hβ (twist n i u))
    (odd_integral n i β hβ u f hf)
    (even_integral n i β hβ u (fun v => (f v)^2) (fun v => by dsimp only; rw [hf, neg_sq]))
  have hs := step_full n β hβ (f^2)
    (fun h v => by simp only [ContinuousMap.pow_apply, hinv]) u
  simp only [ContinuousMap.pow_apply] at hs
  change _ ≤ (∫ v, ((transition n β hβ u v + transition n β hβ (twist n i u) v)/2) *
    (contrast n i β hβ u v)^2 ∂WilsonSlabOperator.measure n) * _ at hh
  rw [← moment_mixture, ← step_full n β hβ f hinv u, ← hs] at hh
  exact hh

/-- Optimality is within the actual continuous physical odd source class at the specified input. -/
theorem row_bound_iff (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (C : ℝ) (hC : 0 ≤ C) :
    moment n i β hβ u ≤ C ↔ ∀ f : C(Slice n, ℝ),
      (∀ h v, f (gaugeSlice h v) = f v) → (∀ v, f (twist n i v) = -f v) →
      (step n β hβ f u)^2 ≤ C * step n β hβ (f^2) u := by
  constructor
  · intro hm f hinv hf
    exact (odd_square n i β hβ f hinv hf u).trans
      (mul_le_mul_of_nonneg_right hm (WilsonGroundRowAveraging.step_nonneg n β hβ (f^2)
        (fun v => by simpa only [ContinuousMap.pow_apply] using sq_nonneg (f v)) u))
  · intro h
    have hh := h (source n i β hβ u) (fun k v => contrast_gauge_right n i β hβ u v k)
      (contrast_odd_right n i β hβ u)
    rw [source_step, source_square_step] at hh
    by_cases hz : moment n i β hβ u = 0
    · simpa only [hz] using hC
    · have hp := lt_of_le_of_ne (moment_nonneg n i β hβ u) (Ne.symm hz)
      nlinarith only [hh, hp]

theorem moment_le_profile (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    moment n i β hβ u ≤ WilsonSeamRateProfile.profile n i β u := by
  apply (row_bound_iff n i β hβ u _ (WilsonSeamRateProfile.profile_nonneg n i β u)).mpr
  intro f hinv hf
  exact WilsonSeamRateProfile.odd_square n i β hβ f hinv hf u

theorem moment_lt_one (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    moment n i β hβ u < 1 :=
  (moment_le_profile n i β hβ u).trans_lt (WilsonSeamRateProfile.profile_lt_one n i β u)

/-- The complement is the harmonic overlap of the two actual physical rows. -/
theorem overlap_identity (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - moment n i β hβ u = ∫ v,
      2 * transition n β hβ u v * transition n β hβ (twist n i u) v /
        (transition n β hβ u v + transition n β hβ (twist n i u) v)
      ∂WilsonSlabOperator.measure n := by
  rw [moment_mixture]
  exact CompactPairedDensity.overlap_identity (WilsonSlabOperator.measure n)
    (transition n β hβ u) (transition n β hβ (twist n i u))
    (transition_continuous n β hβ u) (transition_continuous n β hβ _)
    (transition_pos n β hβ u) (transition_pos n β hβ (twist n i u))
    (transition_mass n β hβ u) (transition_mass n β hβ (twist n i u))

/-- A positive symmetric kernel formed from the actual full Wilson kernel. -/
def harmonicKernel (i : Fin 3) (β : ℝ) : C(Slice n × Slice n, ℝ) :=
  ⟨fun z => 2 * kernelMap n β z * kernelMap n β (twist n i z.1,z.2) /
      (kernelMap n β z + kernelMap n β (twist n i z.1,z.2)), by
    have hc := (kernelMap n β).continuous
    have ht := hc.comp (((twist_continuous n i).comp continuous_fst).prodMk continuous_snd)
    exact ((continuous_const.mul hc).mul ht).div (hc.add ht) (fun z =>
      (add_pos
        (kernel_positive WilsonSingleLinkStaples.character
          WilsonSingleLinkStaples.character_continuous β 2 z.1 z.2)
        (kernel_positive WilsonSingleLinkStaples.character
          WilsonSingleLinkStaples.character_continuous β 2 (twist n i z.1) z.2)).ne')⟩

theorem harmonicKernel_pos (i : Fin 3) (β : ℝ) (u v : Slice n) :
    0 < harmonicKernel n i β (u,v) := by
  have hp := kernel_positive WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2 u v
  have hq := kernel_positive WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2 (twist n i u) v
  change 0 < 2 * kernelMap n β (u,v) * kernelMap n β (twist n i u,v) /
    (kernelMap n β (u,v) + kernelMap n β (twist n i u,v))
  exact div_pos (mul_pos (mul_pos (by norm_num) hp) hq) (add_pos hp hq)

theorem harmonicKernel_symmetric (i : Fin 3) (β : ℝ) (u v : Slice n) :
    harmonicKernel n i β (u,v) = harmonicKernel n i β (v,u) := by
  simp only [harmonicKernel, ContinuousMap.coe_mk]
  rw [← full_kernel_cross n i β u v, kernelMap_symm n β u v,
    kernelMap_symm n β u (twist n i v)]

/-- The overlap is the original-ground row integral of the explicit harmonic kernel. -/
theorem overlap_kernel (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    1 - moment n i β hβ u = ∫ v, harmonicKernel n i β (u,v) * ground n β hβ v /
      (‖transfer n β‖ * ground n β hβ u) ∂WilsonSlabOperator.measure n := by
  rw [overlap_identity]
  apply integral_congr_ae
  filter_upwards with v
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have hk : 0 < kernelMap n β (u,v) + kernelMap n β (twist n i u,v) :=
    add_pos (kernel_positive WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2 u v)
      (kernel_positive WilsonSingleLinkStaples.character
        WilsonSingleLinkStaples.character_continuous β 2 (twist n i u) v)
  simp only [transition, GroundStateDirichlet.transition, ground_twist,
    harmonicKernel, ContinuousMap.coe_mk]
  field_simp [hlam.ne', (ground_pos n β hβ u).ne', (ground_pos n β hβ v).ne', hk.ne']

end
end UnifiedTheory.Clay.YangMills.WilsonContrastMoment
