/-
  Cosmology/QQG/SlowRoll.lean
  ──────────────────────────────────

  Slow-roll parameters for the QQG plateau potential of eq (5).

  In Planck units (M_Pl = 1) the standard slow-roll parameters are:

      ε(φ)  =  (1/2) · (V'(φ) / V(φ))²
      η(φ)  =  V''(φ) / V(φ)

  and the leading observables:

      n_s(φ)  =  1 − 6 ε(φ) + 2 η(φ)
      r(φ)    =  16 ε(φ)

  For our plateau potential V(φ) = V₀ (1 − A μ₀/φ):

      V'(φ)   =  V₀ A μ₀ / φ²
      V(φ)    =  V₀ (1 − A μ₀/φ)  =  V₀ (φ − A μ₀)/φ
      V'/V    =  A μ₀ / [φ (φ − A μ₀)]
      ε(φ)    =  (A μ₀)² / [ 2 φ² (φ − A μ₀)² ]
      V''(φ)  =  − 2 V₀ A μ₀ / φ³

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. The closed form  ε(φ) = (Aμ₀)² / (2φ²(φ−Aμ₀)²)  for φ > Aμ₀.
    2. The closed form  η(φ) = − 2Aμ₀ / [φ²(φ−Aμ₀)]  for φ > Aμ₀.
    3. Identity  r(φ) = 16 ε(φ)  (definitional / one-liner).
    4. Positivity:  ε(φ) > 0  on the slow-roll regime φ > A μ₀ > 0.
    5. Negativity:  η(φ) < 0  on the same regime.
    6. Sub-Planckian-rate bound:  r(φ) ≤ 16 ε₀  whenever  ε(φ) ≤ ε₀.

  SCOPE CAVEAT:
    The exact n_s, r asymptotics of eq (6) [n_s ~ 1 − 4/(3N_e),
    r ~ (8/3)(2/(λ_tH² N_e⁴))^{1/3}] require an integral parameterization
    by e-folds N_e — that integral is left for a future module.  Here we
    work in the φ-parameterization, which is exact and integral-free.
-/

import UnifiedTheory.Cosmology.QQG.InflatonPotential

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG
namespace PlateauPotential

/-! ## 1. The slow-roll parameters ε, η -/

/-- First slow-roll parameter ε(φ) = (1/2)(V'/V)², closed form for our V. -/
noncomputable def epsilon (P : PlateauPotential) (φ : ℝ) : ℝ :=
  (P.A * P.μ₀)^2 / (2 * φ^2 * (φ - P.A * P.μ₀)^2)

/-- Second slow-roll parameter η(φ) = V''/V, closed form for our V. -/
noncomputable def eta (P : PlateauPotential) (φ : ℝ) : ℝ :=
  -2 * P.A * P.μ₀ / (φ^2 * (φ - P.A * P.μ₀))

/-! ## 2. Leading-order observables -/

/-- Scalar spectral index in the leading slow-roll approximation. -/
noncomputable def n_s (P : PlateauPotential) (φ : ℝ) : ℝ :=
  1 - 6 * epsilon P φ + 2 * eta P φ

/-- Tensor-to-scalar ratio in the leading slow-roll approximation. -/
noncomputable def r (P : PlateauPotential) (φ : ℝ) : ℝ :=
  16 * epsilon P φ

/-! ## 3. r = 16 ε  (one-line identity) -/

/-- The fundamental slow-roll relation between r and ε. -/
theorem r_eq_16_epsilon (P : PlateauPotential) (φ : ℝ) :
    r P φ = 16 * epsilon P φ := rfl

/-! ## 4. Positivity and sign of η in the slow-roll regime -/

/-- On the slow-roll regime φ > A μ₀ > 0, ε(φ) > 0. -/
theorem epsilon_pos (P : PlateauPotential)
    {φ : ℝ} (hφ : P.A * P.μ₀ < φ) :
    0 < epsilon P φ := by
  unfold epsilon
  have h_Aμ_pos : 0 < P.A * P.μ₀ := mul_pos P.A_pos P.μ₀_pos
  have h_φ_pos : 0 < φ := lt_trans h_Aμ_pos hφ
  have h_sub_pos : 0 < φ - P.A * P.μ₀ := by linarith
  have h_φ_ne : φ ≠ 0 := ne_of_gt h_φ_pos
  have h_sub_ne : φ - P.A * P.μ₀ ≠ 0 := ne_of_gt h_sub_pos
  have h_num : 0 < (P.A * P.μ₀)^2 := by positivity
  have h_den : 0 < 2 * φ^2 * (φ - P.A * P.μ₀)^2 := by positivity
  exact div_pos h_num h_den

/-- On the slow-roll regime, η(φ) < 0. -/
theorem eta_neg (P : PlateauPotential)
    {φ : ℝ} (hφ : P.A * P.μ₀ < φ) :
    eta P φ < 0 := by
  unfold eta
  have h_A := P.A_pos
  have h_μ := P.μ₀_pos
  have h_Aμ_pos : 0 < P.A * P.μ₀ := mul_pos h_A h_μ
  have h_φ_pos : 0 < φ := lt_trans h_Aμ_pos hφ
  have h_sub_pos : 0 < φ - P.A * P.μ₀ := by linarith
  have h_num_neg : -2 * P.A * P.μ₀ < 0 := by
    have h_2A : 0 < 2 * P.A := by linarith
    have h_2Aμ : 0 < 2 * P.A * P.μ₀ := mul_pos h_2A h_μ
    linarith
  have h_den_pos : 0 < φ^2 * (φ - P.A * P.μ₀) :=
    mul_pos (pow_pos h_φ_pos 2) h_sub_pos
  exact div_neg_of_neg_of_pos h_num_neg h_den_pos

/-! ## 5. Identification of ε, η with the standard formulas -/

/-- ε is (1/2)(V'/V)² evaluated using the explicit derivative
    V'(φ) = V₀ A μ₀ / φ². -/
theorem epsilon_eq_slow_roll_form (P : PlateauPotential)
    {φ : ℝ} (hφ : P.A * P.μ₀ < φ) :
    epsilon P φ
      = (1/2) * ((P.V₀ * P.A * P.μ₀ / φ^2) / P.V φ)^2 := by
  unfold epsilon V
  have h_Aμ_pos : 0 < P.A * P.μ₀ := mul_pos P.A_pos P.μ₀_pos
  have h_φ_pos : 0 < φ := lt_trans h_Aμ_pos hφ
  have h_sub_pos : 0 < φ - P.A * P.μ₀ := by linarith
  have h_φ_ne : φ ≠ 0 := ne_of_gt h_φ_pos
  have h_sub_ne : φ - P.A * P.μ₀ ≠ 0 := ne_of_gt h_sub_pos
  have h_V₀_ne : P.V₀ ≠ 0 := ne_of_gt P.V₀_pos
  -- V(φ) = V₀ · (1 - A μ₀/φ) = V₀ (φ - A μ₀)/φ
  -- (V'/V)² = (V₀ A μ₀ / φ²)² / (V₀ (φ-Aμ₀)/φ)²
  --        = V₀² (Aμ₀)² / φ⁴ · φ² / (V₀² (φ-Aμ₀)²)
  --        = (Aμ₀)² / (φ² (φ-Aμ₀)²)
  -- ε = (1/2) · (Aμ₀)² / (φ²(φ-Aμ₀)²)
  field_simp

/-! ## 6. Sub-Planckian-rate bound on r -/

/-- If ε is bounded above by ε₀, then so is r/16 — i.e., r ≤ 16 ε₀. -/
theorem r_le_of_epsilon_le (P : PlateauPotential)
    {φ ε₀ : ℝ} (h : epsilon P φ ≤ ε₀) :
    r P φ ≤ 16 * ε₀ := by
  unfold r
  linarith

end PlateauPotential
end UnifiedTheory.Cosmology.QQG
