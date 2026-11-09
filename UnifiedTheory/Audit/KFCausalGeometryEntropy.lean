/-
  Finite weight/rank bounds and entropy dominance for the v2 phase audit.
  The quantum spectral suppliers and random-regular graph theorems are
  analytic/literature inputs, not axioms asserting a physical continuum.
-/
import UnifiedTheory.Audit.KFCausalBalancedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGeometryEntropy
noncomputable section
open scoped BigOperators
open Filter Topology

/-- The scalar ratio step behind a finite spectral trace bound. -/
theorem weight_ratio_bound (A Z m D lo hi : ℝ)
    (hm : 0 ≤ m) (hD : 0 < D) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hA : A ≤ m * hi) (hZ : D * lo ≤ Z) :
    A / Z ≤ (m * hi) / (D * lo) := by
  have hden : 0 < D * lo := mul_pos hD hlo
  apply (div_le_iff₀ (lt_of_lt_of_le hden hZ)).mpr
  calc
    A ≤ m * hi := hA
    _ = (m * hi / (D * lo)) * (D * lo) := (div_mul_cancel₀ _ hden.ne').symm
    _ ≤ (m * hi / (D * lo)) * Z :=
      mul_le_mul_of_nonneg_left hZ (div_nonneg (mul_nonneg hm hhi) hden.le)

/-- Works in a basis adapted to an event projector, without commutation of
that projector with the Hamiltonian. Spectral calculus supplies lo and hi. -/
theorem finite_event_weight_bound {X : Type*} [Fintype X] [Nonempty X]
    (w : X → ℝ) (s : Finset X) (lo hi : ℝ) (hlo : 0 < lo)
    (hlow : ∀ x, lo ≤ w x) (hhigh : ∀ x, w x ≤ hi) :
    (∑ x ∈ s, w x) / (∑ x, w x) ≤
      ((s.card : ℝ) * hi) / ((Fintype.card X : ℝ) * lo) := by
  have hhi : 0 ≤ hi := le_trans hlo.le (le_trans (hlow (Classical.choice inferInstance))
    (hhigh (Classical.choice inferInstance)))
  apply weight_ratio_bound _ _ _ _ _ _ (by positivity) (by positivity) hlo hhi
  · simpa using Finset.sum_le_sum (s := s) (fun x _ => hhigh x)
  · simpa using Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlow x)

theorem exponential_rank_factor (m D B : ℝ) (hD : D ≠ 0) :
    (m * Real.exp B) / (D * Real.exp (-B)) =
      (m / D) * Real.exp (2 * B) := by
  rw [Real.exp_neg, show 2 * B = B + B by ring, Real.exp_add]
  field_simp

/-- Entropy deficit competes with the spectral width; all quantities are finite. -/
theorem entropy_exponent_bound (p ratio B deficit remainder : ℝ)
    (hp : p ≤ ratio * Real.exp (2 * B))
    (hratio : ratio ≤ Real.exp (-deficit + remainder)) :
    p ≤ Real.exp (-deficit + remainder + 2 * B) := by
  calc
    p ≤ ratio * Real.exp (2 * B) := hp
    _ ≤ Real.exp (-deficit + remainder) * Real.exp (2 * B) :=
      mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- Once the logarithmic term wins, suppression is at least exponential. -/
theorem entropy_log_threshold (a b n : ℝ) (hn : 0 ≤ n)
    (hlarge : b + 1 ≤ a * Real.log n) :
    Real.exp (-a * n * Real.log n + b * n) ≤ Real.exp (-n) := by
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlarge hn]

/-- An explicitly supplied diverging suppression bound forces vanishing mass. -/
theorem vanishing_from_entropy_bound (p deficit : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hb : ∀ n, p n ≤ Real.exp (-deficit n))
    (hdeficit : Tendsto deficit atTop atTop) : Tendsto p atTop (𝓝 0) := by
  have he : Tendsto (fun n => Real.exp (-deficit n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdeficit)
  exact squeeze_zero hp hb he

/-- The sharper probability bound also uses the complementary event weight. -/
theorem sharp_event_weight_bound (a b upper lower : ℝ)
    (ha : 0 ≤ a) (hau : a ≤ upper) (hl : 0 < lower) (hlb : lower ≤ b) :
    a / (a + b) ≤ upper / (upper + lower) := by
  have hu : 0 ≤ upper := le_trans ha hau
  apply (div_le_div_iff₀ (by linarith : 0 < a + b)
    (by linarith : 0 < upper + lower)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hau hl.le,
    mul_le_mul_of_nonneg_left hlb hu]

/-- Maintaining positive event probability requires a compensating spectral budget. -/
theorem necessary_spectral_budget (p deficit budget : ℝ) (hp : 0 < p)
    (hbound : p ≤ Real.exp (budget - deficit)) : deficit + Real.log p ≤ budget := by
  have h := (Real.log_le_iff_le_exp hp).mpr hbound
  linarith

#print axioms weight_ratio_bound
#print axioms finite_event_weight_bound
#print axioms exponential_rank_factor
#print axioms entropy_exponent_bound
#print axioms entropy_log_threshold
#print axioms vanishing_from_entropy_bound
#print axioms sharp_event_weight_bound
#print axioms necessary_spectral_budget

end
end UnifiedTheory.Audit.KFCausalGeometryEntropy
