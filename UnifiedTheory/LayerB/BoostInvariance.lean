/-
  LayerB/BoostInvariance.lean — The Berry-Keating Hamiltonian from boost invariance

  THE OBSERVATION:
  The K/P space carries two natural symmetry groups:
  - SO(2) rotations: (K,P) → (Kcosθ - Psinθ, Ksinθ + Pcosθ)
  - SO(1,1) boosts: (K,P) → (e^t K, e^{-t} P)

  Each has a unique invariant quadratic form:
  - Rotation-invariant: K² + P² = |z|² (the Born rule, proven)
  - Boost-invariant: K·P (the Berry-Keating Hamiltonian)

  These are the compact and noncompact invariants of SL(2,ℝ) acting
  on the 2D amplitude space. The Born rule comes from the compact part.
  The Berry-Keating Hamiltonian comes from the noncompact part.

  THE CONNECTION TO THE RIEMANN HYPOTHESIS:
  Berry and Keating conjectured that the nontrivial zeros of ζ(s) are
  eigenvalues of a self-adjoint operator with semiclassical limit H = xp.
  In the K/P framework: x ↔ K (source), p ↔ P (dressing), so H = K·P.
  The Berry-Keating Hamiltonian IS the K/P product, uniquely selected
  by boost invariance — the same way the Born rule is uniquely selected
  by rotation invariance.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace UnifiedTheory.LayerB.BoostInvariance

/-! ## The general quadratic form on the K/P plane -/

/-- A general quadratic form on ℝ²: Q(K,P) = a·K² + b·K·P + c·P². -/
def quadForm (a b c K P : ℝ) : ℝ := a * K ^ 2 + b * K * P + c * P ^ 2

/-! ## Rotation invariance → Born rule (recap) -/

/-- **Rotation invariance forces b = 0, a = c.**
    Under (K,P) → (K cosθ - P sinθ, K sinθ + P cosθ),
    Q is invariant for all θ iff b = 0 and a = c.
    The unique rotation-invariant quadratic is a(K² + P²). -/
theorem rotation_invariant_iff (a b c : ℝ) :
    (∀ K P θ : ℝ,
      quadForm a b c K P =
      quadForm a b c (K * Real.cos θ - P * Real.sin θ)
                      (K * Real.sin θ + P * Real.cos θ))
    ↔ (b = 0 ∧ a = c) := by
  constructor
  · intro h
    constructor
    · -- Set K=1, P=0, θ=π/4: Q(cos(π/4), sin(π/4)) = Q(1, 0)
      -- a·cos²+b·cos·sin+c·sin² = a, so b·cos·sin + (c-a)·sin² = 0
      -- At θ = π/2: Q(0, 1) = Q(1, 0), so c = a
      have h1 := h 1 0 (Real.pi / 2)
      simp [quadForm, Real.cos_pi_div_two, Real.sin_pi_div_two] at h1
      have h2 := h 0 1 (Real.pi / 2)
      simp [quadForm, Real.cos_pi_div_two, Real.sin_pi_div_two] at h2
      -- From h1: a = c, from h2: c = a (redundant)
      -- Need b = 0: use θ = π/4
      have h3 := h 1 0 (Real.pi / 4)
      simp [quadForm] at h3
      -- h3: a = a·cos²(π/4) + b·cos(π/4)·sin(π/4) + c·sin²(π/4)
      -- = (a+c)/2 + b/2 (since cos²+sin²=1 and cos·sin = sin(π/2)/2 = 1/2... hmm)
      -- Actually let me use K=1, P=1, θ=π/2 instead
      have h4 := h 1 1 (Real.pi / 2)
      simp [quadForm, Real.cos_pi_div_two, Real.sin_pi_div_two] at h4
      -- h4: a + b + c = a - b + c, so 2b = 0
      linarith
    · have h1 := h 1 0 (Real.pi / 2)
      simp [quadForm, Real.cos_pi_div_two, Real.sin_pi_div_two] at h1
      linarith
  · rintro ⟨hb, hac⟩
    intro K P θ
    subst hb; subst hac
    simp only [quadForm, zero_mul, add_zero]
    -- a*(K² + P²) = a*((Kcosθ-Psinθ)² + (Ksinθ+Pcosθ)²)
    -- because (Kcosθ-Psinθ)² + (Ksinθ+Pcosθ)² = K²(cos²+sin²) + P²(sin²+cos²) = K²+P²
    suffices h : a * ((K * Real.cos θ - P * Real.sin θ) ^ 2 +
      (K * Real.sin θ + P * Real.cos θ) ^ 2) = a * (K ^ 2 + P ^ 2) by linarith
    congr 1
    have hsc := Real.sin_sq_add_cos_sq θ
    have : (K * Real.cos θ - P * Real.sin θ) ^ 2 +
      (K * Real.sin θ + P * Real.cos θ) ^ 2 =
      K ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
      P ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [this, show Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 from by linarith,
      show Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 from by linarith]
    ring


/-! ## Boost invariance → Berry-Keating Hamiltonian -/

/-- A **boost** on the K/P plane: (K,P) → (e^t · K, e^{-t} · P).
    This is the noncompact (hyperbolic) analog of rotation. -/
noncomputable def boost (t K P : ℝ) : ℝ × ℝ :=
  (Real.exp t * K, Real.exp (-t) * P)

/-- **Boost invariance forces a = 0, c = 0.**
    Under (K,P) → (e^t K, e^{-t} P),
    Q is invariant for all t iff a = 0 and c = 0.
    The unique boost-invariant quadratic is b·K·P. -/
theorem boost_invariant_iff (a b c : ℝ) :
    (∀ K P t : ℝ,
      quadForm a b c K P =
      quadForm a b c (Real.exp t * K) (Real.exp (-t) * P))
    ↔ (a = 0 ∧ c = 0) := by
  constructor
  · intro h
    constructor
    · -- Set K=1, P=0: Q(1,0) = a. Q(e^t, 0) = a·e^{2t}. So a = a·e^{2t} for all t.
      -- This forces a = 0.
      have h1 := h 1 0 1
      simp [quadForm] at h1
      -- h1: a = a * exp(1)^2 + ... = a * exp(2)
      -- So a * (1 - exp(2)) = 0. Since exp(2) ≠ 1, a = 0.
      have hexp2 : Real.exp (1 : ℝ) ^ 2 > 1 := by
        have h1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
        nlinarith [sq_nonneg (Real.exp 1 - 1)]
      nlinarith
    · -- Set K=0, P=1: Q(0,1) = c. Q(0, e^{-t}) = c·e^{-2t}. Forces c = 0.
      have h1 := h 0 1 1
      simp [quadForm] at h1
      have hexp2 : Real.exp (-(1 : ℝ)) ^ 2 < 1 := by
        have hpos := Real.exp_pos (-(1:ℝ))
        have hlt : Real.exp (-(1:ℝ)) < 1 := by
          have h0 : Real.exp (0:ℝ) = 1 := Real.exp_zero
          linarith [Real.exp_strictMono (show (-(1:ℝ)) < 0 by norm_num)]
        nlinarith [sq_nonneg (1 - Real.exp (-(1:ℝ)))]
      nlinarith
  · rintro ⟨ha, hc⟩
    intro K P t
    subst ha; subst hc
    unfold quadForm
    have hexp : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    -- The goal after unfolding has exp(t)*K and exp(-t)*P terms
    -- Use: exp(t)*exp(-t) = 1
    have key : ∀ (a b : ℝ), Real.exp t * a * (Real.exp (-t) * b) = a * b := by
      intro a b
      have : Real.exp t * a * (Real.exp (-t) * b) = a * b * (Real.exp t * Real.exp (-t)) := by ring
      rw [this, hexp, mul_one]
    simp only [zero_mul, zero_add, add_zero]
    rw [show b * (Real.exp t * K) * (Real.exp (-t) * P) =
      b * (Real.exp t * K * (Real.exp (-t) * P)) from by ring, key K P]; ring

/-! ## The two invariants of SL(2,ℝ) -/

/-- **THE BORN RULE AND THE BERRY-KEATING HAMILTONIAN ARE CANONICAL DUALS.**

    On the 2D amplitude space (K, P):
    - The unique rotation-invariant quadratic is K² + P² = |z|²
      (the Born-rule observable, proven in BornRuleUniqueness.lean)
    - The unique boost-invariant quadratic is K·P
      (the Berry-Keating Hamiltonian)

    These are the Casimir invariants of the compact (SO(2)) and
    noncompact (SO(1,1)) subgroups of SL(2,ℝ) acting on the K/P plane.

    Both are derived from the same K/P space, which itself is derived
    from the source functional primitive.

    CONNECTION TO THE RIEMANN HYPOTHESIS:
    Berry and Keating conjectured that the Riemann zeros are eigenvalues
    of a self-adjoint quantization of H = xp. In the K/P framework:
    x = K (source functional value), p = P (dressing/momentum), and
    H = K·P is uniquely selected by boost invariance — just as the
    Born rule K² + P² is uniquely selected by rotation invariance. -/
theorem born_and_berry_keating :
    -- (1) Rotation invariance → K² + P² (Born rule)
    (∀ a b c : ℝ,
      (∀ K P θ : ℝ, quadForm a b c K P =
        quadForm a b c (K * Real.cos θ - P * Real.sin θ)
                        (K * Real.sin θ + P * Real.cos θ)) →
      b = 0 ∧ a = c)
    -- (2) Boost invariance → K·P (Berry-Keating)
    ∧ (∀ a b c : ℝ,
      (∀ K P t : ℝ, quadForm a b c K P =
        quadForm a b c (Real.exp t * K) (Real.exp (-t) * P)) →
      a = 0 ∧ c = 0) := by
  exact ⟨fun a b c h => (rotation_invariant_iff a b c).mp h,
         fun a b c h => (boost_invariant_iff a b c).mp h⟩

end UnifiedTheory.LayerB.BoostInvariance
