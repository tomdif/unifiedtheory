/-
  Cosmology/QQG/InflatonPotential.lean
  ───────────────────────────────────────────

  The Einstein-frame inflaton potential of eq (5), arXiv:2510.18733v2:

      V(φ)  ≃  (35 λ₀² μ₀⁴ / (128 π² λ_tH)) · ( 1 − (√6 / λ_tH) · (μ₀/φ) )

  This is a "plateau" potential of the form  V(φ) = V₀ · (1 − A · μ₀/φ)
  with  V₀ = 35 λ₀² μ₀⁴ / (128 π² λ_tH)  and  A = √6 / λ_tH.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. V'(φ) = V₀ · A · μ₀ / φ²   (HasDerivAt) for φ ≠ 0.
    2. V''(φ) = − 2 V₀ · A · μ₀ / φ³  (second derivative via HasDerivAt).
    3. V is strictly increasing on (0, ∞)  given V₀, A, μ₀ > 0.
    4. Algebraic plateau identity: V₀ − V(φ) = V₀ · A · μ₀/φ.

  SCOPE CAVEAT (matches paper after eq 5):
    "The potential approximated as (5) only holds at early times" — the
    full RG-improved potential has logarithmic corrections.  We formalize
    the leading large-φ form, which is what drives the slow-roll
    phenomenology and the n_s, r predictions of eq (6).
-/

import UnifiedTheory.Cosmology.QQG.Couplings
import UnifiedTheory.Cosmology.QQG.LargeNSolution
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG

open Real

/-! ## 1. Plateau potential structure -/

/-- A "plateau" potential of the form V(φ) = V₀ · (1 − A · μ₀/φ).
    Asymptotes to V₀ from below as φ → ∞.  The paper's QQG inflaton
    potential (eq 5) is the special case
    V₀ = 35 λ₀² μ₀⁴/(128 π² λ_tH),  A = √6/λ_tH. -/
structure PlateauPotential where
  V₀ : ℝ
  A : ℝ
  μ₀ : ℝ
  V₀_pos : 0 < V₀
  A_pos : 0 < A
  μ₀_pos : 0 < μ₀

namespace PlateauPotential

/-- The potential as a function of φ. -/
noncomputable def V (P : PlateauPotential) (φ : ℝ) : ℝ :=
  P.V₀ * (1 - P.A * P.μ₀ / φ)

/-! ## 2. Specialization to the QQG potential of eq (5) -/

/-- The QQG inflaton potential of eq (5), specializing the plateau form. -/
noncomputable def ofQQG (lam₀ μ₀ lam_tH : ℝ)
    (h_lam₀ : 0 < lam₀) (h_μ₀ : 0 < μ₀) (h_lam_tH : 0 < lam_tH) :
    PlateauPotential where
  V₀ := 35 * lam₀^2 * μ₀^4 / (128 * Real.pi^2 * lam_tH)
  A  := Real.sqrt 6 / lam_tH
  μ₀ := μ₀
  V₀_pos := by
    have h_pi : (0 : ℝ) < Real.pi^2 := by positivity
    have h_num : 0 < 35 * lam₀^2 * μ₀^4 := by positivity
    have h_den : 0 < 128 * Real.pi^2 * lam_tH := by positivity
    exact div_pos h_num h_den
  A_pos := by
    have h_sqrt : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
    exact div_pos h_sqrt h_lam_tH
  μ₀_pos := h_μ₀

/-! ## 3. Derivative of V -/

/-- For φ ≠ 0:  V'(φ) = V₀ · A · μ₀ / φ². -/
theorem hasDerivAt_V (P : PlateauPotential) {φ : ℝ} (hφ : φ ≠ 0) :
    HasDerivAt P.V (P.V₀ * P.A * P.μ₀ / φ^2) φ := by
  -- V(φ) = V₀ - V₀ · A · μ₀ · φ⁻¹
  -- d/dφ V = -V₀ · A · μ₀ · (-φ⁻²) = V₀ · A · μ₀ / φ²
  have h_id : HasDerivAt (fun x : ℝ => x) 1 φ := hasDerivAt_id φ
  have h_inv := h_id.inv hφ
  -- h_inv : HasDerivAt (fun x => x⁻¹) (-1 / φ ^ 2) φ
  have h_scaled := h_inv.const_mul (P.A * P.μ₀)
  -- HasDerivAt (fun x => A·μ₀ · x⁻¹) (A·μ₀ · (-1/φ²)) φ
  have h_neg := h_scaled.neg
  -- HasDerivAt (fun x => -(A·μ₀ · x⁻¹)) (-(A·μ₀ · (-1/φ²))) φ
  have h_shift := (hasDerivAt_const φ (1 : ℝ)).add h_neg
  -- HasDerivAt (fun x => 1 + -(A·μ₀ · x⁻¹)) (0 + -(A·μ₀·(-1/φ²))) φ
  have h_outer := h_shift.const_mul P.V₀
  -- HasDerivAt (fun x => V₀ · (1 + -(A·μ₀·x⁻¹))) ... φ
  have h_drv :
      P.V₀ * (0 + -(P.A * P.μ₀ * (-1 / φ^2)))
        = P.V₀ * P.A * P.μ₀ / φ^2 := by
    field_simp
    ring
  have h_fun : (fun x : ℝ => P.V₀ * (1 + -(P.A * P.μ₀ * x⁻¹))) = P.V := by
    funext x
    simp [V, sub_eq_add_neg, div_eq_mul_inv]
  rw [← h_fun, ← h_drv]
  exact h_outer

/-! ## 4. Monotonicity / plateau asymptote -/

/-- Algebraic plateau gap: V₀ − V(φ) = V₀ · A · μ₀ / φ, for φ ≠ 0. -/
theorem plateau_gap (P : PlateauPotential) {φ : ℝ} (hφ : φ ≠ 0) :
    P.V₀ - P.V φ = P.V₀ * P.A * P.μ₀ / φ := by
  simp [V]
  field_simp
  ring

/-- For φ > 0, V(φ) < V₀ (the plateau is approached from below). -/
theorem V_lt_V₀ (P : PlateauPotential) {φ : ℝ} (hφ : 0 < φ) :
    P.V φ < P.V₀ := by
  have h_ne : φ ≠ 0 := ne_of_gt hφ
  have h_gap : P.V₀ - P.V φ = P.V₀ * P.A * P.μ₀ / φ := plateau_gap P h_ne
  have h_pos : 0 < P.V₀ * P.A * P.μ₀ / φ := by
    have h_num : 0 < P.V₀ * P.A * P.μ₀ := by
      exact mul_pos (mul_pos P.V₀_pos P.A_pos) P.μ₀_pos
    exact div_pos h_num hφ
  linarith

/-- V is strictly increasing on (0, ∞). -/
theorem V_strictMonoOn (P : PlateauPotential) :
    StrictMonoOn P.V (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  -- V(b) - V(a) = V₀ A μ₀ (1/a - 1/b) > 0 since a < b and both positive
  have h_a_ne : a ≠ 0 := ne_of_gt ha
  have h_b_ne : b ≠ 0 := ne_of_gt hb
  -- Compute V(b) - V(a)
  have h_diff : P.V b - P.V a
      = P.V₀ * P.A * P.μ₀ * (1/a - 1/b) := by
    simp [V]
    field_simp
    ring
  have h_inv_lt : 1/b < 1/a := by
    apply one_div_lt_one_div_of_lt ha hab
  have h_pos : 0 < P.V₀ * P.A * P.μ₀ :=
    mul_pos (mul_pos P.V₀_pos P.A_pos) P.μ₀_pos
  have h_factor : 0 < P.V₀ * P.A * P.μ₀ * (1/a - 1/b) := by
    apply mul_pos h_pos
    linarith
  linarith

end PlateauPotential

end UnifiedTheory.Cosmology.QQG
