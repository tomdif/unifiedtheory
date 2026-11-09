/- Explicit weak-coupling constants for rooted connected-cluster tails.
The supported threshold tends to zero, and a fixed spatial entropy constant
is absorbed with no volume-dependent coupling threshold. -/
import UnifiedTheory.Clay.YangMills.WilsonConnectedSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonConnectedWeakCoupling
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonHighFieldDecay WilsonPhysicalVariance
open SpatialPlaquetteCutGeometry WilsonClusterSourceDecay WilsonConnectedActivity
open WilsonClusterActivity

theorem rate_half (β : ℝ) (hβ : 256 ≤ β) : 256 * rate β (threshold β) ≤ 1 / 2 := by
  have hb : 0 < β := by linarith
  apply (mul_le_mul_of_nonneg_left (rate_bound β hb) (by norm_num : (0 : ℝ) ≤ 256)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith : 0 < 2 * β + 5)).mpr
  linarith

theorem budget_half (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 256 * ρ ≤ 1 / 2) (m : ℕ) :
    budget ρ m ≤ 2 * ρ * (1 / 2 : ℝ)^(m - 1) := by
  have hq : 0 ≤ 256 * ρ := by positivity
  have hd : 0 < 1 - 256 * ρ := by linarith
  have hp := pow_le_pow_left₀ hq hsmall (m - 1)
  unfold budget
  calc
    _ ≤ (ρ * (256 * ρ)^(m - 1)) / (1 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hρ (pow_nonneg hq _)) (by norm_num) (by linarith)
    _ = 2 * ρ * (256 * ρ)^(m - 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem budget_bound (β : ℝ) (hβ : 256 ≤ β) (m : ℕ) :
    budget (rate β (threshold β)) m ≤
      (2 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) := by
  have hb : 0 < β := by linarith
  apply (budget_half _ (rate_pos β _).le (rate_half β hβ) m).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rate_bound β hb) (by norm_num : (0 : ℝ) ≤ 2))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (m - 1))
  simpa only [div_eq_mul_inv] using h

variable (n : ℕ) [NeZero n]

theorem source_tail (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 256 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (WilsonConnectedSource.event n p m (threshold β)).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β (by linarith)) ≤
      2 * loss (2 * (2 * n)) β (by linarith) f +
        (4 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
          mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  have h := WilsonConnectedSource.source_tail n p m hm β hb (threshold β)
    (threshold_margin β hb) (threshold_pos β hb) (by linarith [rate_half β hβ]) f
  have hc := mul_le_mul_of_nonneg_right (budget_bound β hβ m)
    (mass_nonneg (2 * (2 * n)) β hb.le f)
  have he : 2 * (2 / (2 * β + 5)) = 4 / (2 * β + 5) := by ring
  rw [← he]
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonConnectedWeakCoupling
