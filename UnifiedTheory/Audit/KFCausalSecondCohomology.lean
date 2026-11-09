/-
  Second cubical descent and the explicit finite Ward correction.
  Algebraic identities and quantitative implication lemmas are formalized.
  Its overlap residual bound is a separate analytic argument;
  an exact finite divergence solution alone does not prove locality.
-/
import UnifiedTheory.Audit.KFCausalLocalCohomology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSecondCohomology
noncomputable section
open Matrix
open scoped BigOperators

section DoubleComplex
variable {X₂ X₃ X₄ Y₀ Y₁ Y₂ : Type*}
variable [Fintype X₂] [Fintype X₃] [Fintype X₄]
variable [Fintype Y₀] [Fintype Y₁] [Fintype Y₂]

omit [Fintype X₂] [Fintype Y₀] [Fintype Y₁] in
/-- No remainder is omitted: J = d_x d_y L + d_x Q + K. -/
theorem second_descent_identity (D₃ : Matrix X₂ X₃ ℝ) (D₄ : Matrix X₃ X₄ ℝ)
    (E₂ : Matrix Y₂ Y₁ ℝ) (J K : Matrix X₂ Y₁ ℝ)
    (T W Q : Matrix X₃ Y₁ ℝ) (V : Matrix X₄ Y₁ ℝ) (L : Matrix X₃ Y₂ ℝ)
    (hD : D₃ * D₄ = 0) (hJ : J = D₃ * T + K)
    (hW : W = T - D₄ * V) (hQ : Q = W - L * E₂) :
    J = D₃ * (L * E₂) + D₃ * Q + K := by
  rw [hJ, hQ, hW]
  simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hD, Matrix.zero_mul]
  abel

omit [Fintype X₂] [Fintype Y₂] [Fintype X₃] [Fintype Y₀] in
/-- The remaining y-boundary is the retained S plus the top diagonal. -/
theorem remaining_cycle_identity (D₄ : Matrix X₃ X₄ ℝ) (E₁ : Matrix Y₁ Y₀ ℝ)
    (T W : Matrix X₃ Y₁ ℝ) (V : Matrix X₄ Y₁ ℝ)
    (U M : Matrix X₄ Y₀ ℝ) (S : Matrix X₃ Y₀ ℝ)
    (hW : W = T - D₄ * V) (hS : S = T * E₁ - D₄ * U)
    (hV : V * E₁ = U - M) : W * E₁ = S + D₄ * M := by
  rw [hW, Matrix.sub_mul, Matrix.mul_assoc, hV, Matrix.mul_sub, hS]
  abel

omit [Fintype X₂] [Fintype Y₂] [Fintype X₃] in
/-- The spatial variation of the top diagonal is fixed by the retained S. -/
theorem top_diagonal_gradient (D₄ : Matrix X₃ X₄ ℝ) (E₁ : Matrix Y₁ Y₀ ℝ)
    (T : Matrix X₃ Y₁ ℝ) (U : Matrix X₄ Y₀ ℝ) (S : Matrix X₃ Y₀ ℝ)
    (oneY : Matrix Y₀ Unit ℝ) (hE : E₁ * oneY = 0)
    (hS : S = T * E₁ - D₄ * U) : D₄ * (U * oneY) = -(S * oneY) := by
  rw [hS, Matrix.sub_mul, Matrix.mul_assoc T E₁, hE, Matrix.mul_zero,
    zero_sub, neg_neg, Matrix.mul_assoc]

end DoubleComplex

section Bianchi
/-- The discrete product rule on one oriented three-cell. The shifted
curvatures are necessary; the last term is the Bianchi defect. -/
theorem cap_product_rule (t t₀ t₁ t₂ F₀ F₁ F₂ G₀ G₁ G₂ : ℝ) :
    (t - t₀) * F₀ - (t - t₁) * F₁ + (t - t₂) * F₂ =
      (t * G₀ - t₀ * F₀) - (t * G₁ - t₁ * F₁) +
      (t * G₂ - t₂ * F₂) + t * ((F₀ - G₀) - (F₁ - G₁) + (F₂ - G₂)) := by
  ring

theorem bianchi_cap_divergence (t t₀ t₁ t₂ F₀ F₁ F₂ G₀ G₁ G₂ : ℝ)
    (hF : (F₀ - G₀) - (F₁ - G₁) + (F₂ - G₂) = 0) :
    (t - t₀) * F₀ - (t - t₁) * F₁ + (t - t₂) * F₂ =
      (t * G₀ - t₀ * F₀) - (t * G₁ - t₁ * F₁) + (t * G₂ - t₂ * F₂) := by
  rw [cap_product_rule, hF, mul_zero, add_zero]

end Bianchi

section FiniteCompletion
variable {V E : Type*} [Fintype V] [Fintype E]

/-- An actual right inverse on zero-total sources completes the finite Ward equation. -/
theorem finite_ward_completion [DecidableEq V] (D : Matrix V E ℝ) (H : Matrix E V ℝ)
    (P : Matrix V V ℝ) (a : Matrix V Unit ℝ) (h : Matrix E Unit ℝ)
    (hDH : D * H = 1 - P) (hzero : P * (a - D * h) = 0) :
    D * (h + H * (a - D * h)) = a := by
  classical
  rw [Matrix.mul_add, ← Matrix.mul_assoc D H, hDH, Matrix.sub_mul,
    Matrix.one_mul, hzero, sub_zero]
  abel

/-- Exact scalar correction removes the radial average-density Ward defect. -/
theorem corrected_radial_ward (radial density average change : ℝ)
    (hRad : radial + density = average) (hChange : change = -average) :
    radial + change = -density := by
  linarith

end FiniteCompletion

section LocalityImplications

/-- A distant representative and small spatial variation bound the same
field derivative at every location. This is the top-diagonal rigidity step. -/
theorem far_representative_bound (gx gz ε δ : ℝ)
    (hfar : |gz| ≤ ε) (hvariation : |gx - gz| ≤ δ) : |gx| ≤ ε + δ := by
  calc
    |gx| = |(gx - gz) + gz| := by congr 1; ring
    _ ≤ |gx - gz| + |gz| := abs_add_le _ _
    _ ≤ ε + δ := by linarith

/-- A finite summation right inverse amplifies a uniform residual bound by
its explicitly supplied absolute row sum, including for field derivatives. -/
theorem finite_primitive_bound {I : Type*} (s : Finset I) (H r : I → ℝ)
    (ε K : ℝ) (he : 0 ≤ ε) (hr : ∀ i ∈ s, |r i| ≤ ε)
    (hH : ∑ i ∈ s, |H i| ≤ K) : |∑ i ∈ s, H i * r i| ≤ K * ε := by
  calc
    _ ≤ ∑ i ∈ s, |H i * r i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |H i| * ε := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr i hi) (abs_nonneg _)
    _ = (∑ i ∈ s, |H i|) * ε := by rw [Finset.sum_mul]
    _ ≤ K * ε := mul_le_mul_of_nonneg_right hH he

/-- Polynomial volume factors can be absorbed into a weaker exponential.
This does not supply the input residual estimate. -/
theorem polynomial_exponential_bound (x : ℝ) (hx : 0 ≤ x) (p : ℕ) :
    x ^ p * Real.exp (-x) ≤ (2 : ℝ) ^ p * p.factorial * Real.exp (-x / 2) := by
  have hf : (0 : ℝ) < p.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (x / 2) (by linarith : 0 ≤ x / 2) p
  have hpow : x ^ p ≤ (2 : ℝ) ^ p * p.factorial * Real.exp (x / 2) := by
    have hh := (div_le_iff₀ hf).mp h
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2 ^ p)
    have heq : (2 : ℝ) ^ p * (x / 2) ^ p = x ^ p := by
      rw [← mul_pow]
      congr 1
      ring
    rw [heq] at hh'
    simpa only [mul_assoc, mul_comm (Real.exp (x / 2)) (p.factorial : ℝ)] using hh'
  have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-x)).le
  calc
    _ ≤ ((2 : ℝ) ^ p * p.factorial * Real.exp (x / 2)) * Real.exp (-x) := hh
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- A volume-exponential bound controls spatial separation up to the torus diameter. -/
theorem volume_to_distance_bound (r L α C : ℝ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hr : r ≤ 2 * L) : C * Real.exp (-α * L) ≤ C * Real.exp (-α * r / 2) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith

end LocalityImplications

#print axioms second_descent_identity
#print axioms remaining_cycle_identity
#print axioms top_diagonal_gradient
#print axioms cap_product_rule
#print axioms bianchi_cap_divergence
#print axioms finite_ward_completion
#print axioms corrected_radial_ward
#print axioms far_representative_bound
#print axioms finite_primitive_bound
#print axioms polynomial_exponential_bound
#print axioms volume_to_distance_bound

end
end UnifiedTheory.Audit.KFCausalSecondCohomology
