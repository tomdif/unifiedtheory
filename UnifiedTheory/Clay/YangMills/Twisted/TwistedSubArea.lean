/- The flux induction tolerates constants that grow, as long as they grow slower than the area.

`TwistedFluxInduction.area_law_iterate` assumed one constant `M` at every scale. In log form, with `u_k = -log y_k`
and `m_k = log M_k` (`M_k = 4 n_k² K₁² K₂` at scale `L_k = 2^k L₀`), one isotropic doubling gives
`u_{k+1} ≥ 4 u_k - m_k`.

* `log_iterate`: `u_k ≥ 4^k (u_0 - Σ_{j<k} m_j / 4^{j+1})`.
* `subarea_sum`: if `m_j ≤ A + B q^j` with `0 ≤ q < 4`, then `Σ_{j<k} m_j / 4^{j+1} ≤ A/3 + B/(4 - q)`.
* `area_law_growing`: so `u_0 > A/3 + B/(4 - q)` gives `u_k ≥ 4^k δ` with `δ > 0`, i.e. `y_k ≤ e^{-δ (L_k/L₀)²}`.

With `q = 2^α`, the constants may grow like `log M(L) ≤ A + B (L/L₀)^α` for any `α < 2`: sub-area growth, not
boundedness, is what `K̄` and the transverse factor `n` must satisfy. Area-type growth (`α = 2`) is the borderline and
fails. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea

theorem log_iterate (u m : ℕ → ℝ) (h : ∀ k, 4 * u k - m k ≤ u (k + 1)) (k : ℕ) :
    (4 : ℝ) ^ k * (u 0 - ∑ j ∈ Finset.range k, m j / 4 ^ (j + 1)) ≤ u k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h4 : (0 : ℝ) < 4 ^ (k + 1) := by positivity
    calc (4 : ℝ) ^ (k + 1) * (u 0 - ∑ j ∈ Finset.range (k + 1), m j / 4 ^ (j + 1))
        = 4 * ((4 : ℝ) ^ k * (u 0 - ∑ j ∈ Finset.range k, m j / 4 ^ (j + 1))) - m k := by
          rw [Finset.sum_range_succ]; field_simp; ring
      _ ≤ 4 * u k - m k := by linarith
      _ ≤ u (k + 1) := h k

theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (k : ℕ) : ∑ j ∈ Finset.range k, r ^ j ≤ 1 / (1 - r) := by
  have hr : (0 : ℝ) < 1 - r := by linarith
  rw [geom_sum_eq (by linarith : r ≠ 1), le_div_iff₀ hr]
  have : (r ^ k - 1) / (r - 1) * (1 - r) = 1 - r ^ k := by
    field_simp [(by linarith : r - 1 ≠ 0)]; ring
  rw [this]; linarith [pow_nonneg h0 k]

theorem subarea_sum (m : ℕ → ℝ) {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq0 : 0 ≤ q) (hq : q < 4)
    (hm : ∀ j, m j ≤ A + B * q ^ j) (k : ℕ) :
    ∑ j ∈ Finset.range k, m j / 4 ^ (j + 1) ≤ A / 3 + B / (4 - q) := by
  have hsplit : ∀ j, m j / 4 ^ (j + 1) ≤ A / 4 * (1 / 4) ^ j + B / 4 * (q / 4) ^ j := by
    intro j
    have h4 : (0 : ℝ) < 4 ^ (j + 1) := by positivity
    rw [div_le_iff₀ h4]
    have e : (A / 4 * (1 / 4) ^ j + B / 4 * (q / 4) ^ j) * 4 ^ (j + 1) = A + B * q ^ j := by
      rw [div_pow, div_pow, pow_succ]; field_simp; simp
    rw [e]; exact hm j
  have g1 := geom_le (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) k
  have g2 := geom_le (by positivity : (0 : ℝ) ≤ q / 4) (by linarith) k
  calc ∑ j ∈ Finset.range k, m j / 4 ^ (j + 1)
      ≤ ∑ j ∈ Finset.range k, (A / 4 * (1 / 4) ^ j + B / 4 * (q / 4) ^ j) := Finset.sum_le_sum fun j _ => hsplit j
    _ = A / 4 * ∑ j ∈ Finset.range k, (1 / 4 : ℝ) ^ j + B / 4 * ∑ j ∈ Finset.range k, (q / 4) ^ j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A / 4 * (1 / (1 - 1 / 4)) + B / 4 * (1 / (1 - q / 4)) := by
        gcongr
    _ = A / 3 + B / (4 - q) := by
        have : (4 : ℝ) - q ≠ 0 := by linarith
        field_simp; ring

theorem area_law_growing (u m : ℕ → ℝ) {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq0 : 0 ≤ q) (hq : q < 4)
    (hm : ∀ j, m j ≤ A + B * q ^ j) (h : ∀ k, 4 * u k - m k ≤ u (k + 1)) (k : ℕ) :
    (4 : ℝ) ^ k * (u 0 - (A / 3 + B / (4 - q))) ≤ u k := by
  have h1 := log_iterate u m h k
  have h2 := subarea_sum m hA hB hq0 hq hm k
  have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea
