/- A vanishing hard-defect threshold with quantitatively vanishing
arbitrary-pattern activity. This is a finite-regulator statement. -/
import UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonClusterActivity
noncomputable section
open WilsonGroundSlabEnergy WilsonClusterSourceDecay

def threshold (β : ℝ) : ℝ := 192 * envelope β

theorem threshold_pos (β : ℝ) (hβ : 0 < β) : 0 < threshold β := by
  have he : 0 < envelope β := by
    unfold envelope
    exact add_pos_of_pos_of_nonneg (by positivity)
      (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
  exact mul_pos (by norm_num) he

theorem threshold_margin (β : ℝ) (hβ : 0 < β) : 96 * envelope β ≤ threshold β := by
  have he := WilsonClusterNorm.envelope_nonneg β hβ
  unfold threshold
  linarith

theorem threshold_tendsto : Filter.Tendsto threshold Filter.atTop (nhds 0) := by
  simpa only [mul_zero] using envelope_tendsto.const_mul (192 : ℝ)

theorem rate_threshold (β : ℝ) : rate β (threshold β) = Real.exp (-24 * β * envelope β) := by
  unfold rate threshold
  congr 1
  ring

theorem exponent_threshold (β : ℝ) (hβ : 0 < β) :
    -24 * β * envelope β = -37632 / β - 224 * Real.log (2 * β + 5) := by
  unfold envelope
  field_simp
  ring

/-- A simple explicit envelope; the exact rate decays much faster. -/
theorem rate_bound (β : ℝ) (hβ : 0 < β) : rate β (threshold β) ≤ (2 * β + 5)⁻¹ := by
  rw [rate_threshold, exponent_threshold β hβ]
  have hl : 0 ≤ Real.log (2 * β + 5) := Real.log_nonneg (by linarith)
  calc
    _ ≤ Real.exp (-Real.log (2 * β + 5)) := Real.exp_le_exp.mpr (by
      have hd : 0 ≤ 37632 / β := by positivity
      rw [neg_div]
      linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by linarith)]

theorem rate_tendsto :
    Filter.Tendsto (fun β => rate β (threshold β)) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun β : ℝ => 2 * β + 5) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop (max 0 b)] with β hβ
    have hb := (le_max_right (0 : ℝ) b).trans hβ
    have hz := (le_max_left (0 : ℝ) b).trans hβ
    linarith
  apply squeeze_zero' _ _ (tendsto_inv_atTop_zero.comp ht)
  · exact Filter.Eventually.of_forall (fun β => (rate_pos β (threshold β)).le)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
    exact rate_bound β hβ

end
end UnifiedTheory.Clay.YangMills.WilsonClusterActivity
