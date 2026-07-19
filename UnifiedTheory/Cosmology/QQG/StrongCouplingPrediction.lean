/-
  Cosmology/QQG/StrongCouplingPrediction.lean
  ───────────────────────────────────────────────────

  The "sharp" empirical handle from the paper: in order to avoid the
  strong-coupling regime (λ_tH ≳ 1), the tensor-to-scalar ratio must
  satisfy r ≥ 0.01.

  Eq (6) of arXiv:2510.18733v2 gives r in the e-fold parameterization:

      r  ~  (8/3) · ( 2 / (λ_tH² N_e⁴) )^{1/3} .

  Treating this expression as a *definition* of `r_predicted`, we prove
  the sharp algebraic equivalence:

      r_predicted(λ_tH, N_e)  ≥  r_th
        ⟺  λ_tH² · N_e⁴  ≤  2 · (8 / (3 r_th))³ .

  Specialised to r_th = 1/100 (the paper's "≥ 0.01" claim):

      r_predicted(λ_tH, N_e)  ≥  1/100
        ⟺  λ_tH² · N_e⁴  ≤  2 · (800/3)³  ≈  3.79 × 10⁷ .

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `r_predicted_cubed = (r_predicted)³`.
    2. The sharp iff bound for general r_th > 0.
    3. The specialised "r ≥ 0.01 prediction" lemma.

  SCOPE CAVEAT:
    Eq (6) is itself derived in the leading slow-roll + large-N regime.
    The lemma here is about the *formal prediction* of that formula, not
    a direct derivation from V(φ) in the φ-parameterization — that would
    require the e-fold integral parameterization left to future work.
-/

import UnifiedTheory.Cosmology.QQG.LargeNSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG

open Real

/-! ## 1. The predicted tensor-to-scalar ratio (eq 6) -/

/-- `r_predicted(λ_tH, N_e) := (8/3) · (2 / (λ_tH² N_e⁴))^{1/3}`. -/
noncomputable def r_predicted (lam_tH N_e : ℝ) : ℝ :=
  (8/3) * (2 / (lam_tH^2 * N_e^4)) ^ ((1:ℝ)/3)

/-- The cube of `r_predicted`, an integer-exponent expression. -/
noncomputable def r_predicted_cubed (lam_tH N_e : ℝ) : ℝ :=
  (8/3)^3 * (2 / (lam_tH^2 * N_e^4))

/-! ## 2. Cube relation between the rpow form and the rational form -/

/-- `(r_predicted)³ = r_predicted_cubed`, when λ_tH, N_e are positive. -/
theorem r_predicted_pow_three
    {lam_tH N_e : ℝ} (h_lam : 0 < lam_tH) (h_N : 0 < N_e) :
    (r_predicted lam_tH N_e) ^ 3 = r_predicted_cubed lam_tH N_e := by
  unfold r_predicted r_predicted_cubed
  have h_arg_pos : 0 < 2 / (lam_tH^2 * N_e^4) := by positivity
  have h_arg_nn : 0 ≤ 2 / (lam_tH^2 * N_e^4) := le_of_lt h_arg_pos
  -- expand: ((8/3) * x^(1/3))^3 = (8/3)^3 * x
  rw [mul_pow]
  -- show (x^(1/3))^3 = x
  have h_cube : ((2 / (lam_tH^2 * N_e^4)) ^ ((1:ℝ)/3)) ^ 3
      = 2 / (lam_tH^2 * N_e^4) := by
    have h_inv : ((1:ℝ)/3) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [h_inv]
    exact Real.rpow_inv_natCast_pow h_arg_nn (by norm_num : (3 : ℕ) ≠ 0)
  rw [h_cube]

/-! ## 3. Positivity of r_predicted -/

/-- `r_predicted > 0` for positive λ_tH, N_e. -/
theorem r_predicted_pos
    {lam_tH N_e : ℝ} (h_lam : 0 < lam_tH) (h_N : 0 < N_e) :
    0 < r_predicted lam_tH N_e := by
  unfold r_predicted
  have h_arg_pos : 0 < 2 / (lam_tH^2 * N_e^4) := by positivity
  have h_rpow_pos : 0 < (2 / (lam_tH^2 * N_e^4)) ^ ((1:ℝ)/3) :=
    Real.rpow_pos_of_pos h_arg_pos _
  have h_const : (0 : ℝ) < 8/3 := by norm_num
  exact mul_pos h_const h_rpow_pos

/-! ## 4. Sharp bound: r_predicted ≥ r_th  iff  λ_tH² N_e⁴ ≤ 2 (8/(3 r_th))³ -/

/-- **Sharp form of the strong-coupling prediction.**  For positive
    parameters, `r_th ≤ r_predicted(λ_tH, N_e)` is equivalent to the
    algebraic upper bound `λ_tH² · N_e⁴ ≤ 2 · (8/(3 r_th))³`. -/
theorem r_predicted_ge_iff
    {lam_tH N_e r_th : ℝ}
    (h_lam : 0 < lam_tH) (h_N : 0 < N_e) (h_r : 0 < r_th) :
    r_th ≤ r_predicted lam_tH N_e
      ↔ lam_tH^2 * N_e^4 ≤ 2 * (8 / (3 * r_th)) ^ 3 := by
  have h_pos : 0 < r_predicted lam_tH N_e := r_predicted_pos h_lam h_N
  have h_r3_pos : (0 : ℝ) < r_th^3 := by positivity
  -- Use the cube relation
  have h_cube_eq : (r_predicted lam_tH N_e)^3 = r_predicted_cubed lam_tH N_e :=
    r_predicted_pow_three h_lam h_N
  -- Step 1: r_th ≤ r_pred  ⟺  r_th^3 ≤ r_pred^3  (both positive)
  have h_step1 : r_th ≤ r_predicted lam_tH N_e
      ↔ r_th^3 ≤ (r_predicted lam_tH N_e)^3 := by
    constructor
    · intro h
      have h1 : 0 ≤ r_th := le_of_lt h_r
      exact pow_le_pow_left₀ h1 h 3
    · intro h
      by_contra h_neg
      push_neg at h_neg
      have h2 : 0 ≤ r_predicted lam_tH N_e := le_of_lt h_pos
      have h3 : (r_predicted lam_tH N_e)^3 < r_th^3 :=
        pow_lt_pow_left₀ h_neg h2 (by norm_num)
      linarith
  -- Step 2: r_pred^3 = (8/3)^3 · 2 / (λ_tH² N_e⁴)
  rw [h_step1, h_cube_eq]
  unfold r_predicted_cubed
  -- Goal: r_th^3 ≤ (8/3)^3 * (2 / (lam_tH^2 * N_e^4))
  --       ⟺ lam_tH^2 * N_e^4 ≤ 2 * (8/(3 r_th))^3
  have h_denom_pos : 0 < lam_tH^2 * N_e^4 := by positivity
  have h_rth3_eq : (8 / (3 * r_th)) ^ 3 = (8/3)^3 / r_th^3 := by
    field_simp
  rw [h_rth3_eq]
  constructor
  · intro h
    -- r_th^3 ≤ (8/3)^3 · 2/(lam² N⁴)
    -- ⟹ r_th^3 · (lam² N⁴) ≤ (8/3)^3 · 2
    -- ⟹ lam² N⁴ ≤ (8/3)^3 · 2 / r_th^3 = 2 · (8/3)^3 / r_th^3
    have h1 : r_th^3 * (lam_tH^2 * N_e^4) ≤ (8/3)^3 * 2 := by
      have := mul_le_mul_of_nonneg_right h (le_of_lt h_denom_pos)
      calc r_th^3 * (lam_tH^2 * N_e^4)
          ≤ ((8/3)^3 * (2 / (lam_tH^2 * N_e^4))) * (lam_tH^2 * N_e^4) := this
        _ = (8/3)^3 * 2 := by field_simp
    have h2 : lam_tH^2 * N_e^4 ≤ ((8/3)^3 * 2) / r_th^3 :=
      (le_div_iff₀ h_r3_pos).mpr (by linarith)
    have h3 : ((8/3)^3 * 2) / r_th^3 = 2 * ((8/3)^3 / r_th^3) := by ring
    linarith [h3 ▸ h2]
  · intro h
    -- lam² N⁴ ≤ 2 · (8/3)^3 / r_th^3
    -- ⟹ r_th^3 · (lam² N⁴) ≤ 2 · (8/3)^3
    -- ⟹ r_th^3 ≤ (8/3)^3 · 2 / (lam² N⁴)
    have h1 : r_th^3 * (lam_tH^2 * N_e^4) ≤ r_th^3 * (2 * ((8/3)^3 / r_th^3)) :=
      mul_le_mul_of_nonneg_left h (le_of_lt h_r3_pos)
    have h2 : r_th^3 * (2 * ((8/3)^3 / r_th^3)) = 2 * (8/3)^3 := by
      field_simp
    have h3 : r_th^3 * (lam_tH^2 * N_e^4) ≤ 2 * (8/3)^3 := by linarith
    have h4 : r_th^3 ≤ 2 * (8/3)^3 / (lam_tH^2 * N_e^4) :=
      (le_div_iff₀ h_denom_pos).mpr (by linarith)
    have h5 : 2 * (8/3)^3 / (lam_tH^2 * N_e^4)
        = (8/3)^3 * (2 / (lam_tH^2 * N_e^4)) := by ring
    linarith [h5 ▸ h4]

/-! ## 5. The paper's "r ≥ 0.01" prediction -/

/-- **The QQG r-bound prediction.**  Specialising to the paper's threshold
    r_th = 1/100, the bound becomes  λ_tH² · N_e⁴ ≤ 2 · (800/3)³. -/
theorem r_predicted_ge_001_iff
    {lam_tH N_e : ℝ} (h_lam : 0 < lam_tH) (h_N : 0 < N_e) :
    (1 : ℝ)/100 ≤ r_predicted lam_tH N_e
      ↔ lam_tH^2 * N_e^4 ≤ 2 * (800/3) ^ 3 := by
  have h : 8 / (3 * ((1:ℝ)/100)) = 800/3 := by norm_num
  rw [r_predicted_ge_iff h_lam h_N (by norm_num : (0:ℝ) < 1/100), h]

end UnifiedTheory.Cosmology.QQG
