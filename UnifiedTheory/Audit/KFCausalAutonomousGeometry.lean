/-
  Supporting inequalities for autonomous geometry selection.
  Graph-cycle counting, finite spectral recurrence, and the random-regular
  asymptotics remain explicit analytic suppliers in the accompanying note.
-/
import UnifiedTheory.Audit.KFCausalCoarseGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalAutonomousGeometry
noncomputable section
open scoped BigOperators
open Filter Topology

/-- Energy conservation fixes the only possible constant six-site resonance. -/
theorem six_site_resonance (v rho : ℝ) :
    12 * v / 7 = 144 * rho ↔ v = 84 * rho := by constructor <;> intro h <;> linarith

/-- Weighted Cauchy-Schwarz, without taking square roots of weights. -/
theorem weighted_row_bound {J : Type*} [Fintype J]
    (w x : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∑ j, w j * x j) ^ 2 ≤ (∑ j, w j) * ∑ j, w j * x j ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (f := w) (g := fun j => w j * x j ^ 2)
  · exact fun j _ => hw j
  · exact fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  · intro j _
    ring

/-- A nonnegative rectangular matrix has squared Euclidean operator norm at
most its maximum row sum times its maximum column sum. This proves the real
version; applying it to magnitudes also bounds complex vectors analytically. -/
theorem weighted_schur_bound {I J : Type*} [Fintype I] [Fintype J]
    (w : I → J → ℝ) (x : J → ℝ) (row col : ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : 0 ≤ row)
    (hr : ∀ i, ∑ j, w i j ≤ row) (hc : ∀ j, ∑ i, w i j ≤ col) :
    (∑ i, (∑ j, w i j * x j) ^ 2) ≤ row * col * ∑ j, x j ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, w i j) * ∑ j, w i j * x j ^ 2 :=
      Finset.sum_le_sum (fun i _ => weighted_row_bound (w i) x (hw i))
    _ ≤ ∑ i, row * ∑ j, w i j * x j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hr i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (hw i j) (sq_nonneg _)))
    _ = row * ∑ j, (∑ i, w i j) * x j ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ row * ∑ j, col * x j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hrow
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The compressed eigenvalue equation and the Schur bound supply hblock. -/
theorem ground_event_bound (p D e r : ℝ) (hD : 0 < D) (hr : 0 ≤ r)
    (he : e < D) (hblock : (D - e) ^ 2 * p ≤ D * r * (1 - p)) :
    p ≤ D * r / ((D - e) ^ 2 + D * r) := by
  have hden : 0 < (D - e) ^ 2 + D * r := by
    have hs : 0 < (D - e) ^ 2 := sq_pos_of_pos (sub_pos.mpr he)
    nlinarith [mul_nonneg hD.le hr]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/-- An extensive target diagonal and bounded repair weight force a 1/D bound. -/
theorem inverse_volume_bound (p D e r : ℝ) (hp : 0 ≤ p)
    (hD : 0 < D) (hr : 0 ≤ r) (he : e ≤ D / 2)
    (hblock : (D - e) ^ 2 * p ≤ D * r * (1 - p)) : p ≤ 4 * r / D := by
  have hs : D ^ 2 / 4 ≤ (D - e) ^ 2 := by nlinarith [sq_nonneg (D / 2 - e)]
  have h1 := mul_le_mul_of_nonneg_right hs hp
  have h2 : D * r * (1 - p) ≤ D * r := by nlinarith [mul_nonneg (mul_nonneg hD.le hr) hp]
  have h3 : D * (p * D) ≤ D * (4 * r) := by nlinarith
  exact (le_div_iff₀ hD).mpr (le_of_mul_le_mul_left h3 hD)

theorem vanishing_from_inverse_volume (p D : ℕ → ℝ) (r : ℝ)
    (hp : ∀ n, 0 ≤ p n) (hb : ∀ n, p n ≤ 4 * r / D n)
    (hD : Tendsto D atTop atTop) : Tendsto p atTop (𝓝 0) :=
  squeeze_zero hp hb (hD.const_div_atTop (4 * r))

/-- Finite spectral recurrence is an explicit supplier, not assumed attraction. -/
theorem recurrent_limit_eq_initial (f : ℝ → ℝ) (times : ℕ → ℝ) (limit : ℝ)
    (ht : Tendsto times atTop atTop)
    (hr : Tendsto (fun n => f (times n)) atTop (𝓝 (f 0)))
    (hl : Tendsto f atTop (𝓝 limit)) : limit = f 0 :=
  tendsto_nhds_unique (hl.comp ht) hr

/-- Four changed endpoints, radius-three degree bound, four path positions,
and the factor two from the actual ordered exchange normalization. -/
theorem cubic_repair_constant :
    (2 : ℕ) * 4 * (4 * (1 + 6 + 6 * 5 + 6 * 5 ^ 2)) * (6 * 5 ^ 2) = 897600 := by
  norm_num

#print axioms six_site_resonance
#print axioms weighted_row_bound
#print axioms weighted_schur_bound
#print axioms ground_event_bound
#print axioms inverse_volume_bound
#print axioms vanishing_from_inverse_volume
#print axioms recurrent_limit_eq_initial
#print axioms cubic_repair_constant

end
end UnifiedTheory.Audit.KFCausalAutonomousGeometry
