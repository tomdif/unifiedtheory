/- The algebraic core of Lemma V (README, "Large-t endpoint"): for the von Mises–Fisher law `e^{κ cos θ}` on S³
and `W = e^{(κ/2)(1 − cos θ)}`, one has `LW / W = (κ/2) g(cos θ)` with `g(c) = (κ/2) c² + 3c − κ/2`. Outside the
cap `{1 − cos θ ≤ 6/κ}`, i.e. for `c ∈ [−1, 1 − 6/κ]`, `g(c) ≤ −3`, so `LW ≤ −(3κ/2) W`. The proof uses the
factorization `g(c) + 3 = (κ/2)(c + 1)(c − (1 − 6/κ))`. The calculus identity for `LW / W` and the
Bakry–Barthe–Cattiaux–Guillin theorem are not formalized here. -/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov

/-- The Lyapunov ratio polynomial. -/
noncomputable def g (κ c : ℝ) : ℝ := κ / 2 * c ^ 2 + 3 * c - κ / 2

theorem g_add_three (κ c : ℝ) (hκ : κ ≠ 0) :
    g κ c + 3 = κ / 2 * (c + 1) * (c - (1 - 6 / κ)) := by
  unfold g; field_simp; ring

theorem g_neg_one (κ : ℝ) : g κ (-1) = -3 := by unfold g; ring

theorem g_cap_edge (κ : ℝ) (hκ : κ ≠ 0) : g κ (1 - 6 / κ) = -3 := by
  have := g_add_three κ (1 - 6 / κ) hκ; simp at this; linarith

/-- **Lyapunov drift outside the cap.** For `κ > 0` and `−1 ≤ c ≤ 1 − 6/κ`, `g(c) ≤ −3`. -/
theorem g_le_neg_three (κ c : ℝ) (hκ : 0 < κ) (h1 : -1 ≤ c) (h2 : c ≤ 1 - 6 / κ) : g κ c ≤ -3 := by
  have h := g_add_three κ c hκ.ne'
  have : κ / 2 * (c + 1) * (c - (1 - 6 / κ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (by linarith)) (by linarith)
  linarith

/-- The drift rate: outside the cap, `(κ/2) g(c) ≤ −(3κ/2)`. -/
theorem drift (κ c : ℝ) (hκ : 0 < κ) (h1 : -1 ≤ c) (h2 : c ≤ 1 - 6 / κ) :
    κ / 2 * g κ c ≤ -(3 * κ / 2) := by
  have := g_le_neg_three κ c hκ h1 h2; nlinarith

/-- The constant of Lemma V: `(2/(3κ))(1 + 6e³) < 82/κ`, i.e. `2(1 + 6e³) < 246`. (The value is ≈ 81.01/κ, so
81 would be false.) -/
theorem lemmaV_constant : 2 * (1 + 6 * Real.exp 3) < 246 := by
  have he : Real.exp 3 < 20.2 := by
    have h := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have hp : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 :=
      pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
    rw [h3]; linarith [show (2.7182818286 : ℝ) ^ 3 < 20.2 by norm_num]
  linarith

end UnifiedTheory.Clay.YangMills.Twisted.TwistedVMFLyapunov
