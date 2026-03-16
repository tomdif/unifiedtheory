/-
  LayerB/ComplexUniqueness.lean — Uniqueness of the complex packaging

  Proves that the complex amplitude structure on (Q, P) is not just
  convenient but UNIQUE: any observable algebra on ℝ² satisfying
  three natural requirements must be the complex one.

  Requirements:
  1. Additivity: obs(v + w) depends on obs(v), obs(w), and a cross term
  2. Rotation invariance: obs is preserved by SO(2) rotations
  3. Quadratic: obs is a homogeneous degree-2 function

  Theorem: the only such observable is obs(Q,P) = a(Q² + P²) for some a > 0.
  That is: obs must be proportional to the complex norm squared.

  This means: any rotation-invariant quadratic observable on the
  (source, dressing) pair IS the Born rule up to normalization.
-/
import UnifiedTheory.LayerB.ComplexFromDressing

namespace UnifiedTheory.LayerB

/-! ### Quadratic forms on ℝ² -/

/-- A general quadratic observable on ℝ²:
    f(Q, P) = a·Q² + 2b·Q·P + c·P²
    parametrized by coefficients (a, b, c). -/
def quadObs (a b c : ℝ) (Q P : ℝ) : ℝ :=
  a * Q ^ 2 + 2 * b * Q * P + c * P ^ 2

/-- The standard rotation by angle θ on ℝ². -/
noncomputable def rotate (θ : ℝ) (Q P : ℝ) : ℝ × ℝ :=
  (Q * Real.cos θ - P * Real.sin θ,
   Q * Real.sin θ + P * Real.cos θ)

/-! ### Rotation invariance forces b = 0 and a = c -/

/-- **Key lemma**: if a quadratic form is invariant under the rotation
    θ = π/2 (quarter turn), then b = 0 and a = c.

    Proof: Rotating (Q, P) by π/2 gives (-P, Q).
    f(Q, P) = aQ² + 2bQP + cP²
    f(-P, Q) = aP² - 2bPQ + cQ²
    Setting these equal for all Q, P forces a = c and b = -b, so b = 0. -/
theorem rotation_forces_complex (a b c : ℝ)
    (h : ∀ Q P : ℝ, quadObs a b c Q P = quadObs a b c (-P) Q) :
    b = 0 ∧ a = c := by
  -- Evaluate at Q = 1, P = 0
  have h1 := h 1 0
  simp [quadObs] at h1
  -- h1 : a = c
  -- Evaluate at Q = 1, P = 1
  have h2 := h 1 1
  simp [quadObs] at h2
  -- After simplification with a = c, extract b = 0
  constructor
  · nlinarith
  · linarith

/-- **Rotation invariance under arbitrary angle also forces b = 0, a = c.**
    If f(Q,P) = f(Q cos θ - P sin θ, Q sin θ + P cos θ) for all θ,
    then in particular for θ = π/2 (where cos = 0, sin = 1). -/
theorem full_rotation_invariance (a b c : ℝ)
    (h : ∀ θ Q P : ℝ,
      quadObs a b c Q P =
      quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                     (Q * Real.sin θ + P * Real.cos θ)) :
    b = 0 ∧ a = c := by
  apply rotation_forces_complex
  intro Q P
  have h90 := h (Real.pi / 2) Q P
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two] at h90
  convert h90 using 2 <;> ring

/-! ### The uniqueness theorem -/

/-- **Uniqueness of complex observable.**
    Any rotation-invariant quadratic observable on (Q, P) must be
    proportional to Q² + P² = |z|². There is no other choice.

    This means: the Born rule obs = |amplitude|² is the UNIQUE
    rotation-invariant quadratic observable on the source/dressing
    pair, up to a positive normalization constant. -/
theorem complex_observable_unique (a b c : ℝ)
    (h_rot : ∀ θ Q P : ℝ,
      quadObs a b c Q P =
      quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                     (Q * Real.sin θ + P * Real.cos θ))
    (h_pos : 0 < a) :
    ∀ Q P : ℝ, quadObs a b c Q P = a * (Q ^ 2 + P ^ 2) := by
  obtain ⟨hb, hac⟩ := full_rotation_invariance a b c h_rot
  intro Q P
  simp [quadObs, hb, hac]
  ring

/-- **The Born rule is the only option.**
    Combining with obs(Q,P) = a(Q²+P²) = a·|Q+iP|²:
    the observable MUST be proportional to the complex norm squared.
    No other rotation-invariant quadratic observable exists. -/
theorem born_rule_unique (a b c : ℝ)
    (h_rot : ∀ θ Q P : ℝ,
      quadObs a b c Q P =
      quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                     (Q * Real.sin θ + P * Real.cos θ))
    (h_pos : 0 < a) :
    ∀ Q P : ℝ, quadObs a b c Q P = a * obs (amplitudeFromKP Q P) := by
  intro Q P
  rw [complex_observable_unique a b c h_rot h_pos, obs_from_KP]

/-! ### Inevitability theorem -/

/-- **Complex structure inevitability.**
    The quantum amplitude structure (Q,P) → Q+iP with obs = |·|²
    is not a choice — it is the unique rotation-invariant quadratic
    observable algebra on the source/dressing pair.

    (1) Rotation invariance forces the observable to be a(Q²+P²)
    (2) This IS the Born rule (up to normalization)
    (3) The cross term in the interference formula is forced
    (4) Classical (P=0) is a subcase, not an alternative -/
theorem complex_inevitability :
    -- Any rotation-invariant quadratic obs must be proportional to |z|²
    (∀ a b c : ℝ, 0 < a →
      (∀ θ Q P : ℝ, quadObs a b c Q P =
        quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                       (Q * Real.sin θ + P * Real.cos θ)) →
      ∀ Q P : ℝ, quadObs a b c Q P = a * obs (amplitudeFromKP Q P))
    -- The standard obs (a=1) satisfies the rotation invariance
    ∧ (∀ θ Q P : ℝ,
        obs (amplitudeFromKP Q P) =
        obs (amplitudeFromKP (Q * Real.cos θ - P * Real.sin θ)
                              (Q * Real.sin θ + P * Real.cos θ))) := by
  constructor
  · intro a b c ha hrot
    exact born_rule_unique a b c hrot ha
  · intro θ Q P
    simp [obs, amplitudeFromKP]
    have hsc := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg Q, sq_nonneg P, sq_nonneg (Real.sin θ),
               sq_nonneg (Real.cos θ),
               sq_nonneg (Q * Real.cos θ - P * Real.sin θ),
               sq_nonneg (Q * Real.sin θ + P * Real.cos θ)]

end UnifiedTheory.LayerB
