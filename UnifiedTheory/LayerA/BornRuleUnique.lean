/-
  LayerA/BornRuleUnique.lean — The Born rule is the UNIQUE SO(2)-invariant quadratic form

  Critique #9: "The Born rule is not fully derived."

  RESPONSE: We prove that Q² + P² is the UNIQUE rotation-invariant
  quadratic form on ℝ². This is the algebraic content of the Born rule.

  A general quadratic form on ℝ² is f(Q, P) = a·Q² + b·Q·P + c·P².
  Under SO(2) rotation by angle θ:
    Q' = Q·cos θ - P·sin θ
    P' = Q·sin θ + P·cos θ
  Requiring f(Q', P') = f(Q, P) for ALL θ forces a = c and b = 0.
  So f = a·(Q² + P²).

  The Born rule |ψ|² = Q² + P² is therefore the UNIQUE (up to scale)
  rotation-invariant quadratic observable.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.BornRuleUnique

/-! ## 1. Quadratic forms on ℝ² -/

/-- A **quadratic form** on ℝ² specified by three coefficients:
    f(Q, P) = a·Q² + b·Q·P + c·P². -/
structure QuadForm where
  a : ℝ  -- coefficient of Q²
  b : ℝ  -- coefficient of Q·P (cross-term)
  c : ℝ  -- coefficient of P²

/-- Evaluate the quadratic form at (Q, P). -/
def QuadForm.eval (f : QuadForm) (Q P : ℝ) : ℝ :=
  f.a * Q ^ 2 + f.b * Q * P + f.c * P ^ 2

/-- The **norm-squared form** Q² + P² (the Born rule). -/
def normSqForm : QuadForm where
  a := 1
  b := 0
  c := 1

/-- The norm-squared form evaluates to Q² + P². -/
theorem normSq_eval (Q P : ℝ) :
    normSqForm.eval Q P = Q ^ 2 + P ^ 2 := by
  unfold normSqForm QuadForm.eval; ring

/-! ## 2. SO(2) rotation of a quadratic form -/

/-- Evaluate f at the SO(2)-rotated point (Q', P'). -/
noncomputable def QuadForm.evalRotated (f : QuadForm) (θ Q P : ℝ) : ℝ :=
  f.eval (Q * Real.cos θ - P * Real.sin θ) (Q * Real.sin θ + P * Real.cos θ)

/-- A quadratic form is **SO(2)-invariant** if f(R_θ(Q,P)) = f(Q,P)
    for all θ, Q, P. -/
def QuadForm.IsSO2Invariant (f : QuadForm) : Prop :=
  ∀ θ Q P : ℝ, f.evalRotated θ Q P = f.eval Q P

/-! ## 3. The key computation: expanding f(R_θ(Q,P))

    f(Q', P') = a·(Q cosθ - P sinθ)² + b·(Q cosθ - P sinθ)(Q sinθ + P cosθ)
              + c·(Q sinθ + P cosθ)²

    Expanding:
    = a·(Q² cos²θ - 2QP cosθ sinθ + P² sin²θ)
    + b·(Q² cosθ sinθ + QP cos²θ - QP sin²θ - P² sinθ cosθ)
    + c·(Q² sin²θ + 2QP sinθ cosθ + P² cos²θ)

    Collecting by monomials Q², QP, P²:
    Q² coefficient: a·cos²θ + b·cosθ sinθ + c·sin²θ
    QP coefficient: -2a·cosθ sinθ + b·(cos²θ - sin²θ) + 2c·sinθ cosθ
    P² coefficient: a·sin²θ - b·sinθ cosθ + c·cos²θ

    For invariance, these must equal a, b, c respectively for all θ.
-/

/-- The Q² coefficient after rotation. -/
noncomputable def rotatedCoeffQ2 (f : QuadForm) (θ : ℝ) : ℝ :=
  f.a * Real.cos θ ^ 2 + f.b * Real.cos θ * Real.sin θ + f.c * Real.sin θ ^ 2

/-- The QP coefficient after rotation. -/
noncomputable def rotatedCoeffQP (f : QuadForm) (θ : ℝ) : ℝ :=
  -2 * f.a * Real.cos θ * Real.sin θ + f.b * (Real.cos θ ^ 2 - Real.sin θ ^ 2) +
  2 * f.c * Real.sin θ * Real.cos θ

/-- The P² coefficient after rotation. -/
noncomputable def rotatedCoeffP2 (f : QuadForm) (θ : ℝ) : ℝ :=
  f.a * Real.sin θ ^ 2 - f.b * Real.sin θ * Real.cos θ + f.c * Real.cos θ ^ 2

/-- The rotated evaluation equals the sum of rotated coefficients × monomials. -/
theorem evalRotated_expand (f : QuadForm) (θ Q P : ℝ) :
    f.evalRotated θ Q P =
    rotatedCoeffQ2 f θ * Q ^ 2 + rotatedCoeffQP f θ * Q * P +
    rotatedCoeffP2 f θ * P ^ 2 := by
  unfold QuadForm.evalRotated QuadForm.eval rotatedCoeffQ2 rotatedCoeffQP rotatedCoeffP2
  ring

/-! ## 4. Invariance forces a = c and b = 0 -/

-- Setting θ = π/2 forces a = c.
-- At θ = π/2: cos = 0, sin = 1.
-- Q² coefficient: a·0 + b·0 + c·1 = c. Must equal a. So a = c.
-- QP coefficient: 0 + b·(0-1) + 0 = -b. Must equal b. So b = -b, i.e., b = 0.
-- P² coefficient: a·1 - b·0 + c·0 = a. Must equal c. So a = c (consistent).

/-- At θ = π/2, cos θ = 0 and sin θ = 1. -/
theorem cos_pi_div_two : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two

theorem sin_pi_div_two : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two

/-- **SO(2) invariance at θ = π/2 forces a = c.** -/
theorem invariance_forces_a_eq_c (f : QuadForm) (hinv : f.IsSO2Invariant) :
    f.a = f.c := by
  -- Evaluate at θ = π/2, Q = 1, P = 0
  have h := hinv (Real.pi / 2) 1 0
  simp only [QuadForm.evalRotated, QuadForm.eval] at h
  simp only [cos_pi_div_two, sin_pi_div_two] at h
  linarith

/-- **SO(2) invariance at θ = π/2 forces b = 0.** -/
theorem invariance_forces_b_eq_zero (f : QuadForm) (hinv : f.IsSO2Invariant) :
    f.b = 0 := by
  -- Evaluate at θ = π/2, Q = 1, P = 1
  have h1 := hinv (Real.pi / 2) 1 1
  simp only [QuadForm.evalRotated, QuadForm.eval] at h1
  simp only [cos_pi_div_two, sin_pi_div_two] at h1
  -- Also evaluate at Q = 1, P = 0 and Q = 0, P = 1 for the constraint
  have h2 := hinv (Real.pi / 2) 1 0
  simp only [QuadForm.evalRotated, QuadForm.eval] at h2
  simp only [cos_pi_div_two, sin_pi_div_two] at h2
  -- h2 gives: f.c = f.a, so f.a = f.c
  -- h1 gives: f.c - f.b + f.a = f.a + f.b + f.c
  -- Simplifying: -f.b = f.b, so f.b = 0
  linarith

/-! ## 5. The uniqueness theorem -/

/-- **MAIN THEOREM: Every SO(2)-invariant quadratic form is proportional
    to Q² + P².**

    If f(Q, P) = a·Q² + b·Q·P + c·P² is invariant under all SO(2)
    rotations, then b = 0 and a = c, so f = a·(Q² + P²). -/
theorem so2_invariant_quadratic_unique (f : QuadForm) (hinv : f.IsSO2Invariant) :
    f.b = 0 ∧ f.a = f.c := by
  exact ⟨invariance_forces_b_eq_zero f hinv, invariance_forces_a_eq_c f hinv⟩

/-- **Corollary: an SO(2)-invariant quadratic form evaluates as a·(Q² + P²).** -/
theorem so2_invariant_eval (f : QuadForm) (hinv : f.IsSO2Invariant) (Q P : ℝ) :
    f.eval Q P = f.a * (Q ^ 2 + P ^ 2) := by
  have ⟨hb, hac⟩ := so2_invariant_quadratic_unique f hinv
  unfold QuadForm.eval
  rw [hb, hac]; ring

/-- **The Born rule: the unique normalized SO(2)-invariant quadratic form.** -/
theorem born_rule_from_invariance (f : QuadForm) (hinv : f.IsSO2Invariant)
    (hnorm : f.a = 1) (Q P : ℝ) :
    f.eval Q P = Q ^ 2 + P ^ 2 := by
  rw [so2_invariant_eval f hinv Q P, hnorm, one_mul]

/-! ## 6. Converse: Q² + P² IS SO(2)-invariant -/

/-- **The norm-squared form is SO(2)-invariant.** -/
theorem normSq_is_SO2_invariant : normSqForm.IsSO2Invariant := by
  intro θ Q P
  unfold QuadForm.evalRotated normSqForm QuadForm.eval
  have hsc := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg Q, sq_nonneg P, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

/-! ## 7. Higher-order check: quartic forms

    For completeness, we note that the same argument applies to quartic forms.
    A general quartic on ℝ² has 5 coefficients. SO(2) invariance reduces
    this to the unique form (Q² + P²)². We prove the key identity. -/

/-- (Q² + P²)² is SO(2)-invariant — immediate from norm-squared invariance. -/
theorem quartic_invariant (θ Q P : ℝ) :
    ((Q * Real.cos θ - P * Real.sin θ) ^ 2 +
     (Q * Real.sin θ + P * Real.cos θ) ^ 2) ^ 2 =
    (Q ^ 2 + P ^ 2) ^ 2 := by
  have hsc := Real.sin_sq_add_cos_sq θ
  congr 1
  nlinarith [sq_nonneg Q, sq_nonneg P, sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

/-! ## 8. Connection to probability: normalization -/

/-- **If the quadratic form must be non-negative and integrate to 1
    over the unit circle (Q² + P² = 1), then f.a > 0.**

    The non-negativity condition: f(Q, P) ≥ 0 for all Q, P.
    Since f = a·(Q² + P²) and Q² + P² ≥ 0, we need a ≥ 0.
    Since f ≠ 0 (it's a probability measure), a > 0. -/
theorem nonneg_invariant_form_positive_coeff (f : QuadForm)
    (hinv : f.IsSO2Invariant)
    (hnn : ∀ Q P : ℝ, 0 ≤ f.eval Q P)
    (hne : f.a ≠ 0) :
    0 < f.a := by
  by_contra h
  push_neg at h
  have hle : f.a < 0 := lt_of_le_of_ne h hne
  -- f.eval 1 0 = f.a · (1 + 0) = f.a < 0, contradicting non-negativity
  have := hnn 1 0
  rw [so2_invariant_eval f hinv] at this
  linarith

/-! ## 9. Master theorem -/

/-- **BORN RULE UNIQUENESS THEOREM.**

    (1) Every SO(2)-invariant quadratic form is proportional to Q² + P²
    (2) Q² + P² is SO(2)-invariant (converse)
    (3) The proportionality constant is positive for non-negative forms
    (4) With normalization a = 1, the form IS the Born rule |ψ|² = Q² + P²

    This is the algebraic content of the Born rule. The physical content
    (why we need SO(2) invariance) comes from the isotropy of the
    Poisson sprinkling, proved in RotationInvariance.lean. -/
theorem born_rule_uniqueness :
    -- (1) Uniqueness: invariance forces the form
    (∀ f : QuadForm, f.IsSO2Invariant → f.b = 0 ∧ f.a = f.c)
    -- (2) Existence: Q² + P² is invariant
    ∧ normSqForm.IsSO2Invariant
    -- (3) The Born rule is the normalized invariant form
    ∧ (∀ Q P : ℝ, normSqForm.eval Q P = Q ^ 2 + P ^ 2) := by
  exact ⟨fun f h => so2_invariant_quadratic_unique f h,
         normSq_is_SO2_invariant,
         normSq_eval⟩

end UnifiedTheory.LayerA.BornRuleUnique
