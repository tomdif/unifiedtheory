/- Rooted cluster entropy with a marked endpoint. The extra cluster-size
factor is absorbed by doubling the activity, independently of volume. -/
import UnifiedTheory.Clay.YangMills.WilsonConnectedWeakCoupling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonMarkedClusterActivity
noncomputable section
open WilsonPlaquetteGraph WilsonConnectedActivity WilsonClusterSourceDecay WilsonClusterActivity

theorem size_activity (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (k : ℝ) * ρ ^ k ≤ (2 * ρ) ^ k := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hk (pow_nonneg hρ k)

variable (N : ℕ) [NeZero N]

/-- Every rooted pattern is charged once for each possible marked endpoint it contains. -/
theorem activity_bound (p : Plaquettes N) (m L : ℕ) (hm : 0 < m)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 512 * ρ < 1) :
    (∑ i : Index N p m L, ((marked N p m L i).card : ℝ) *
      ρ ^ (marked N p m L i).card) ≤ budget (2 * ρ) m := by
  apply (Finset.sum_le_sum (fun i _ => size_activity (marked N p m L i).card ρ hρ)).trans
  exact WilsonConnectedActivity.activity_bound N p m L hm (2 * ρ) (by positivity)
    (by nlinarith)

omit N [NeZero N] in
theorem rate_half (β : ℝ) (hβ : 512 ≤ β) :
    256 * (2 * rate β (threshold β)) ≤ 1 / 2 := by
  have hb : 0 < β := by linarith
  have h := mul_le_mul_of_nonneg_left (rate_bound β hb) (by norm_num : (0 : ℝ) ≤ 512)
  have hd : 512 / (2 * β + 5) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * β + 5)).mpr
    linarith
  rw [div_eq_mul_inv] at hd
  nlinarith

omit N [NeZero N] in
theorem budget_bound (β : ℝ) (hβ : 512 ≤ β) (m : ℕ) :
    budget (2 * rate β (threshold β)) m ≤
      (4 / (2 * β + 5)) * (1 / 2 : ℝ) ^ (m - 1) := by
  have hb : 0 < β := by linarith
  apply (WilsonConnectedWeakCoupling.budget_half _
    (mul_nonneg (by norm_num) (rate_pos β _).le) (rate_half β hβ) m).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rate_bound β hb) (by norm_num : (0 : ℝ) ≤ 4))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (m - 1))
  convert h using 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonMarkedClusterActivity
