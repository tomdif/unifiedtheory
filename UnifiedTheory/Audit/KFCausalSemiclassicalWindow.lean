/- Shrinking normalized windows can be chosen with vanishing canonical
test error along a subsequence of any hbar sequence tending to zero.
Translation continuity supplies the scale choice, rather than an assumed
window characteristic limit. -/
import UnifiedTheory.Audit.KFCausalLocalizedWindow
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalSemiclassicalWindow
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalLocalizedWindow
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation

def radius (k : ℕ) : ℝ := 1/((k:ℝ)+1)

theorem radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

variable (n : ℕ)

def unitWindow (k : ℕ) : BlockHilbert n := window n (radius k)

theorem unitWindow_norm (k : ℕ) : ‖unitWindow n k‖ = 1 := window_norm n (radius k) (radius_pos k)

theorem translation_subsequence (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, ∀ v : Block n, ‖v‖ ≤ (k:ℝ)+1 →
      ‖translation volume (h (φ k) • v) (unitWindow n k)-unitWindow n k‖ < radius k := by
  apply extraction_forall_of_eventually (P := fun k j =>
    ∀ v : Block n, ‖v‖ ≤ (k:ℝ)+1 →
      ‖translation volume (h j • v) (unitWindow n k)-unitWindow n k‖ < radius k)
  intro k
  obtain ⟨δ,hδ,hD⟩ := Metric.continuous_iff.mp (translation_continuous volume (unitWindow n k))
    0 (radius k) (radius_pos k)
  have hs : Tendsto (fun j => |h j| *((k:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul_const ((k:ℝ)+1)
  filter_upwards [hs.eventually (gt_mem_nhds hδ)] with j hj
  intro v hv
  have hn : ‖h j • v‖ < δ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hv (abs_nonneg _)).trans_lt hj
  have hd := hD (h j • v) (by simpa only [dist_zero_right] using hn)
  simpa only [translation_zero,dist_eq_norm] using hd

theorem operator_limit (h : ℕ → ℝ) (φ : ℕ → ℕ)
    (ht : ∀ k : ℕ, ∀ v : Block n, ‖v‖ ≤ (k:ℝ)+1 →
      ‖translation volume (h (φ k) • v) (unitWindow n k)-unitWindow n k‖ < radius k)
    (z : Frequency (X := Block n)) :
    Tendsto (fun k => ‖operator volume (h (φ k)) z (unitWindow n k)-unitWindow n k‖)
      atTop (𝓝 0) := by
  have hb : ∀ᶠ k : ℕ in atTop,
      ‖operator volume (h (φ k)) z (unitWindow n k)-unitWindow n k‖ ≤ radius k+‖z.1‖*radius k := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop ‖z.2‖)] with k hk
    have htrans := ht k z.2 (by linarith)
    have hmod := window_modulation_bound n (radius k) (radius_pos k) z.1
    exact (phaseTranslation_difference volume z.1 z.1.continuous.measurable
      (h (φ k) • z.2) (unitWindow n k)).trans (add_le_add htrans.le hmod)
  have hr : Tendsto radius atTop (𝓝 (0:ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k => radius k+‖z.1‖*radius k) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using hr.add (hr.const_mul ‖z.1‖)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hb hl

theorem characteristic_limit (h : ℕ → ℝ) (φ : ℕ → ℕ)
    (ht : ∀ k : ℕ, ∀ v : Block n, ‖v‖ ≤ (k:ℝ)+1 →
      ‖translation volume (h (φ k) • v) (unitWindow n k)-unitWindow n k‖ < radius k)
    (z : Frequency (X := Block n)) :
    Tendsto (fun k => characteristic volume (h (φ k)) (unitWindow n k) z) atTop (𝓝 1) := by
  have hb (k : ℕ) : ‖characteristic volume (h (φ k)) (unitWindow n k) z-1‖ ≤
      ‖operator volume (h (φ k)) z (unitWindow n k)-unitWindow n k‖ := by
    have he : inner ℂ (unitWindow n k) (unitWindow n k) = 1 := by
      rw [inner_self_eq_norm_sq_to_K,unitWindow_norm]
      norm_num
    unfold characteristic
    rw [← he,← inner_sub_right]
    simpa only [unitWindow_norm,one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) (unitWindow n k)
        (operator volume (h (φ k)) z (unitWindow n k)-unitWindow n k)
  have hd := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hb (operator_limit n h φ ht z))
  simpa only [sub_add_cancel,zero_add] using hd.add_const (1:ℂ)

#print axioms radius_pos
#print axioms unitWindow_norm
#print axioms translation_subsequence
#print axioms operator_limit
#print axioms characteristic_limit

end
end UnifiedTheory.Audit.KFCausalSemiclassicalWindow
