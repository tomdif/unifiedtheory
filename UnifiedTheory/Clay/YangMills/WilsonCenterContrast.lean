/- The actual full-transition center contrast. Both ground factors cancel
from the ratio, while all temporal Haar integration remains in the kernel.
For each input it is a continuous physical center-odd test source. -/
import UnifiedTheory.Clay.YangMills.WilsonSeamRateFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterContrast
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonGroundLocalComparison WilsonPhysicalScore WilsonPhysicalResponse
open WilsonSingleLinkStaples (character character_continuous character_classFunction)

variable (n : ℕ) [NeZero n]

theorem full_kernel_twist (i : Fin 3) (β : ℝ) (u v : Slice n) :
    kernelMap n β (twist n i u,twist n i v) = kernelMap n β (u,v) := by
  change (∫ h, Real.exp (-slabAction character β 2 (twist n i u) (twist n i v) h)
    ∂temporalHaar) = ∫ h, Real.exp (-slabAction character β 2 u v h) ∂temporalHaar
  apply integral_congr_ae
  filter_upwards with h
  simp only [slabAction, potential_twist, temporalAction_eq character character_classFunction,
    ← twist_gauge, kinetic_twist]

theorem full_kernel_cross (i : Fin 3) (β : ℝ) (u v : Slice n) :
    kernelMap n β (u,twist n i v) = kernelMap n β (twist n i u,v) := by
  simpa only [twist_involution] using full_kernel_twist n i β (twist n i u) v

theorem full_transition_twist (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    transition n β hβ (twist n i u) (twist n i v) = transition n β hβ u v := by
  simp only [transition, GroundStateDirichlet.transition, full_kernel_twist, ground_twist]

theorem full_transition_cross (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    transition n β hβ u (twist n i v) = transition n β hβ (twist n i u) v := by
  simpa only [twist_involution] using full_transition_twist n i β hβ (twist n i u) v

def contrast (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) : ℝ :=
  (transition n β hβ u v - transition n β hβ (twist n i u) v) /
    (transition n β hβ u v + transition n β hβ (twist n i u) v)

theorem contrast_continuous (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun z : Slice n × Slice n => contrast n i β hβ z.1 z.2) := by
  have hc := (WilsonHeatBathComparison.transitionMap n β hβ).continuous
  have ht := hc.comp (((twist_continuous n i).comp continuous_fst).prodMk continuous_snd)
  exact (hc.sub ht).div (hc.add ht)
    (fun z => (add_pos (transition_pos n β hβ z.1 z.2)
      (transition_pos n β hβ (twist n i z.1) z.2)).ne')

def source (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) : C(Slice n, ℝ) :=
  ⟨contrast n i β hβ u, (contrast_continuous n i β hβ).comp
    (f := fun v : Slice n => (u,v)) (continuous_const.prodMk continuous_id)⟩

theorem contrast_gauge_left (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n)
    (h : SliceGauge n Q) : contrast n i β hβ (gaugeSlice h u) v = contrast n i β hβ u v := by
  simp only [contrast, twist_gauge, full_transition_gauge_left]

theorem contrast_gauge_right (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n)
    (h : SliceGauge n Q) : contrast n i β hβ u (gaugeSlice h v) = contrast n i β hβ u v := by
  simp only [contrast, transition_gauge_right]

theorem contrast_odd_left (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    contrast n i β hβ (twist n i u) v = -contrast n i β hβ u v := by
  simp only [contrast, twist_involution]
  rw [add_comm (transition n β hβ (twist n i u) v)]
  ring

theorem contrast_odd_right (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    contrast n i β hβ u (twist n i v) = -contrast n i β hβ u v := by
  simp only [contrast, full_transition_cross, twist_involution]
  rw [add_comm (transition n β hβ (twist n i u) v)]
  ring

theorem contrast_abs_lt_one (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    |contrast n i β hβ u v| < 1 := by
  have hp := transition_pos n β hβ u v
  have hq := transition_pos n β hβ (twist n i u) v
  rw [contrast, abs_div, abs_of_pos (add_pos hp hq)]
  apply (div_lt_one (add_pos hp hq)).mpr
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The contrast is determined by the full Wilson kernel, with no ground amplitude in its ratio. -/
theorem contrast_kernel (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    contrast n i β hβ u v = (kernelMap n β (u,v) - kernelMap n β (twist n i u,v)) /
      (kernelMap n β (u,v) + kernelMap n β (twist n i u,v)) := by
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have hk : 0 < kernelMap n β (u,v) + kernelMap n β (twist n i u,v) :=
    add_pos (kernel_positive character character_continuous β 2 u v)
      (kernel_positive character character_continuous β 2 (twist n i u) v)
  unfold contrast transition GroundStateDirichlet.transition
  rw [ground_twist]
  field_simp [hlam.ne', (ground_pos n β hβ u).ne', (ground_pos n β hβ v).ne', hk.ne']

theorem contrast_symmetric (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    contrast n i β hβ u v = contrast n i β hβ v u := by
  rw [contrast_kernel, contrast_kernel, ← full_kernel_cross n i β u v,
    kernelMap_symm n β u v, kernelMap_symm n β u (twist n i v)]

theorem twisted_integral (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (F : Slice n → ℝ) :
    (∫ v, transition n β hβ (twist n i u) v * F v ∂WilsonSlabOperator.measure n) =
      ∫ v, transition n β hβ u v * F (twist n i v) ∂WilsonSlabOperator.measure n := by
  have hh := WilsonRawSymmetry.integral_pull n (symmetry n i)
    (fun v => transition n β hβ (twist n i u) v * F v)
  change (∫ v, transition n β hβ (twist n i u) (twist n i v) * F (twist n i v)
    ∂WilsonSlabOperator.measure n) = _ at hh
  simpa only [full_transition_twist] using hh.symm

theorem odd_integral (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (F : Slice n → ℝ) (hF : ∀ v, F (twist n i v) = -F v) :
    (∫ v, transition n β hβ (twist n i u) v * F v ∂WilsonSlabOperator.measure n) =
      -(∫ v, transition n β hβ u v * F v ∂WilsonSlabOperator.measure n) := by
  rw [twisted_integral]
  simp only [hF, mul_neg, integral_neg]

theorem even_integral (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n)
    (F : Slice n → ℝ) (hF : ∀ v, F (twist n i v) = F v) :
    (∫ v, transition n β hβ (twist n i u) v * F v ∂WilsonSlabOperator.measure n) =
      ∫ v, transition n β hβ u v * F v ∂WilsonSlabOperator.measure n := by
  rw [twisted_integral]
  simp only [hF]

end
end UnifiedTheory.Clay.YangMills.WilsonCenterContrast
