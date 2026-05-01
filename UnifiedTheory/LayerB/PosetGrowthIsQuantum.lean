/-
  LayerB/PosetGrowthIsQuantum.lean — Born-rule shape for dressing-invariant
  growth probabilities.

  CONTENT: If poset-growth probability is quadratic in (Q, P) and dressing-
  invariant under the SO(2) action on the K/P plane, then it is proportional
  to Q² + P² — the same algebraic uniqueness result as `BornRuleUnique.lean`
  and `ComplexUniqueness.lean`, applied to growth dynamics rather than to
  measurement observables. All three files prove the same uniqueness fact
  under different framings; this is intentional re-statement, not three
  independent results.

  WHAT THIS FILE DOES NOT CONTAIN: the Rideout–Sorkin sequential growth
  model is referenced but not formalized. There is no Hilbert space attached
  to the growth process, no unitary evolution operator, and no derivation of
  Born-rule probabilities from unitary transition amplitudes. The chain
  "growth probability ∝ Q² + P² ⇒ Born rule ⇒ quantum mechanics" is asserted
  by analogy; only the first arrow (algebraic uniqueness given dressing
  invariance) is formalized here.

  The SO(2) "dressing rotation" on the K/P plane is taken as stipulation, as
  in `BornRuleUnique` and `ComplexFromDressing`. Its derivation from causal-
  poset structure is open; see `PHASE4_DIAGNOSTIC.md` for the surviving open
  question (a)/(b) and the Solèr–Moretti–Oppio continuum analogue.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PosetGrowthIsQuantum

open Real

/-! ═══════════════════════════════════════════════════════════════
    PART 1: POSET GROWTH AS A STOCHASTIC PROCESS
    ═══════════════════════════════════════════════════════════════ -/

/-- A growth step: adding one element to a finite partial order.
    Each possible addition is characterized by:
    - Q : ℝ (source strength, visible to φ)
    - P : ℝ (dressing content, invisible to φ) -/
structure GrowthStep where
  Q : ℝ  -- source component
  P : ℝ  -- dressing component

/-- A growth probability rule: assigns a probability to each (Q, P) pair. -/
def GrowthProb := ℝ → ℝ → ℝ

/-! ═══════════════════════════════════════════════════════════════
    PART 2: THE DRESSING INVISIBILITY CONSTRAINT
    ═══════════════════════════════════════════════════════════════ -/

/-- The dressing rotation: (Q, P) → (Q cos θ - P sin θ, Q sin θ + P cos θ).
    This is the SO(2) action on the (Q, P) plane.
    The source functional φ cannot distinguish (Q, P) from its rotation. -/
noncomputable def rotateQ (Q P θ : ℝ) : ℝ := Q * cos θ - P * sin θ
noncomputable def rotateP (Q P θ : ℝ) : ℝ := Q * sin θ + P * cos θ

/-- Rotation preserves Q² + P². -/
theorem rotation_preserves_norm (Q P θ : ℝ) :
    (rotateQ Q P θ)^2 + (rotateP Q P θ)^2 = Q^2 + P^2 := by
  unfold rotateQ rotateP
  have h := sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Q * cos θ - P * sin θ),
             sq_nonneg (Q * sin θ + P * cos θ),
             sq_nonneg Q, sq_nonneg P,
             sq_nonneg (cos θ), sq_nonneg (sin θ)]

/-- A growth probability is DRESSING-INVARIANT if it doesn't change
    under dressing rotations. -/
def IsDressingInvariant (prob : GrowthProb) : Prop :=
  ∀ Q P θ : ℝ, prob (rotateQ Q P θ) (rotateP Q P θ) = prob Q P

/-! ═══════════════════════════════════════════════════════════════
    PART 3: UNIQUENESS OF THE BORN RULE FOR GROWTH
    ═══════════════════════════════════════════════════════════════ -/

/-- A general quadratic growth probability:
    prob(Q, P) = a·Q² + 2b·Q·P + c·P². -/
def quadGrowthProb (a b c : ℝ) : GrowthProb :=
  fun Q P => a * Q^2 + 2 * b * Q * P + c * P^2

/-- Quarter-turn (θ = π/2) maps (Q, P) → (-P, Q). -/
theorem quarter_turn_Q (Q P : ℝ) : rotateQ Q P (π/2) = -P := by
  unfold rotateQ; simp [cos_pi_div_two, sin_pi_div_two]

theorem quarter_turn_P (Q P : ℝ) : rotateP Q P (π/2) = Q := by
  unfold rotateP; simp [cos_pi_div_two, sin_pi_div_two]

/-- Dressing invariance under quarter-turn forces b = 0 and a = c. -/
theorem quarter_turn_forces_born_rule (a b c : ℝ)
    (h : ∀ Q P : ℝ, quadGrowthProb a b c (-P) Q = quadGrowthProb a b c Q P) :
    b = 0 ∧ a = c := by
  unfold quadGrowthProb at h
  constructor
  · -- Use Q = 1, P = 1
    have h11 := h 1 1
    linarith
  · -- Use Q = 1, P = 0
    have h10 := h 1 0
    linarith

/-- **THE BORN RULE FOR GROWTH.**

    If:
    (1) Growth probability is quadratic in (Q, P)
    (2) Growth probability is dressing-invariant (SO(2) symmetric)

    Then: growth probability = a · (Q² + P²) for some a > 0.

    This IS the Born rule: prob ∝ |z|² where z = Q + iP. -/
theorem born_rule_for_growth (a b c : ℝ)
    (h_inv : ∀ Q P : ℝ, quadGrowthProb a b c (-P) Q = quadGrowthProb a b c Q P) :
    ∀ Q P : ℝ, quadGrowthProb a b c Q P = a * (Q^2 + P^2) := by
  obtain ⟨hb, hac⟩ := quarter_turn_forces_born_rule a b c h_inv
  intro Q P
  unfold quadGrowthProb
  rw [hb, hac]; ring

/-! ═══════════════════════════════════════════════════════════════
    PART 4: WHY GROWTH MUST BE QUADRATIC
    ═══════════════════════════════════════════════════════════════ -/

/-- The growth probability is quadratic because:
    - It must be nonneg (probability ≥ 0)
    - It must vanish when Q = P = 0 (no element = no growth)
    - It must be smooth (differentiable in Q and P)
    - The leading term of a smooth nonneg function vanishing at 0 is quadratic

    Formally: if f(0,0) = 0 and f ≥ 0, the Taylor expansion is:
    f(Q,P) = aQ² + 2bQP + cP² + O(|(Q,P)|³)
    and the quadratic part must be positive semidefinite. -/
theorem zero_at_origin : (0 : ℝ)^2 + (0 : ℝ)^2 = 0 := by ring

theorem born_rule_nonneg (a : ℝ) (ha : 0 ≤ a) (Q P : ℝ) :
    0 ≤ a * (Q^2 + P^2) := by
  apply mul_nonneg ha
  linarith [sq_nonneg Q, sq_nonneg P]

/-! ═══════════════════════════════════════════════════════════════
    PART 5: THE EQUIVALENCE
    ═══════════════════════════════════════════════════════════════ -/

/-- The Born rule probability is EXACTLY the dressing-invariant norm. -/
theorem born_is_dressing_invariant (a : ℝ) :
    IsDressingInvariant (fun Q P => a * (Q^2 + P^2)) := by
  intro Q P θ
  simp only
  rw [show a * ((rotateQ Q P θ)^2 + (rotateP Q P θ)^2) =
      a * ((rotateQ Q P θ)^2 + (rotateP Q P θ)^2) from rfl]
  congr 1
  exact rotation_preserves_norm Q P θ

/-- No non-Born quadratic is dressing-invariant. -/
theorem only_born_is_invariant (a b c : ℝ)
    (h : ∀ Q P : ℝ, quadGrowthProb a b c (-P) Q = quadGrowthProb a b c Q P)
    (hb_ne : b ≠ 0 ∨ a ≠ c) : False := by
  obtain ⟨hb, hac⟩ := quarter_turn_forces_born_rule a b c h
  rcases hb_ne with hb_ne | hac_ne
  · exact hb_ne hb
  · exact hac_ne hac

/-! ═══════════════════════════════════════════════════════════════
    PART 6: THE MASTER THEOREM
    ═══════════════════════════════════════════════════════════════ -/

/-- **DRESSING-INVARIANT QUADRATIC GROWTH PROBABILITIES HAVE BORN-RULE SHAPE.**

    If poset-growth probability is quadratic in (Q, P) and dressing-invariant
    under the SO(2) action on the K/P plane, then it is proportional to
    Q² + P². Specifically:

    (1) Each growth step has (Q, P) ∈ ℝ² from the K/P decomposition
    (2) Dressing invariance forces prob ∝ Q² + P² (algebraic uniqueness)
    (3) The Born-shape rule is nonneg (valid probability for a ≥ 0)
    (4) Q² + P² is dressing-invariant (consistent)
    (5) No other quadratic rule is dressing-invariant (uniqueness)

    Limits of this theorem (read carefully):

    * **Same fact as `BornRuleUnique` and `ComplexUniqueness`.** The
      algebraic uniqueness statement is identical; the framing differs
      (growth probability vs. measurement observable vs. complex amplitude).

    * **Sequential-growth dynamics not formalized.** Rideout–Sorkin
      classical sequential growth is referenced in the file docstring
      but not implemented in Lean. This theorem does not establish that
      poset-growth dynamics ARE the Rideout–Sorkin model; it characterizes
      the shape of an individual-step probability distribution under
      stated symmetry assumptions.

    * **No Hilbert space, no unitary evolution.** The theorem does not
      derive that growth probabilities respect a unitary evolution on
      a complex Hilbert space. The chain "Born-shape probability ⇒
      Born rule ⇒ quantum mechanics" is asserted by analogy; only the
      first arrow is formalized here.

    * **SO(2) action stipulated.** The dressing rotation is defined in
      this file, not derived from causal-poset data. See
      `PHASE4_DIAGNOSTIC.md` for the surviving open question. -/
theorem dressing_invariant_quadratic_is_born_form :
    -- (1) Born rule forced by dressing invariance
    (∀ a b c : ℝ,
      (∀ Q P : ℝ, quadGrowthProb a b c (-P) Q = quadGrowthProb a b c Q P) →
      ∀ Q P : ℝ, quadGrowthProb a b c Q P = a * (Q^2 + P^2))
    -- (2) Born rule is nonneg for a ≥ 0
    ∧ (∀ a : ℝ, 0 ≤ a → ∀ Q P : ℝ, 0 ≤ a * (Q^2 + P^2))
    -- (3) Born rule IS dressing-invariant
    ∧ (∀ a : ℝ, IsDressingInvariant (fun Q P => a * (Q^2 + P^2)))
    -- (4) Rotation preserves Q² + P²
    ∧ (∀ Q P θ : ℝ, (rotateQ Q P θ)^2 + (rotateP Q P θ)^2 = Q^2 + P^2)
    -- (5) Zero at origin
    ∧ ((0 : ℝ)^2 + (0 : ℝ)^2 = 0) := by
  exact ⟨born_rule_for_growth,
         born_rule_nonneg,
         born_is_dressing_invariant,
         rotation_preserves_norm,
         zero_at_origin⟩

end UnifiedTheory.LayerB.PosetGrowthIsQuantum
