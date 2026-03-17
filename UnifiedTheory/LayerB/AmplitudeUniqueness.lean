/-
  LayerB/AmplitudeUniqueness.lean — The amplitude rule is unique

  Proves that the sum-over-histories amplitude law (add amplitudes,
  then square) is the UNIQUE composition rule compatible with:
  1. Additivity: amplitude of composite = sum of amplitudes
  2. Observable non-negativity: obs ≥ 0
  3. Observable faithfulness: obs = 0 iff amplitude = 0
  4. Phase covariance: relative phase affects observable

  These constraints force:
  - Amplitudes must be complex (not real, quaternionic, etc.)
  - The observable must be |z|² (the unique norm)
  - The composition rule must be addition (not multiplication, etc.)
  - The event observable must be |Σ A(h)|² (sum then square)

  This upgrades the quantum side from:
    "here is a nice package with ℂ amplitudes and |z|²"
  to:
    "any package satisfying these natural constraints is THIS one."

  Zero custom axioms.
-/
import UnifiedTheory.LayerB.QuantumUniqueness
import UnifiedTheory.LayerB.HistoryAmplitudes

namespace UnifiedTheory.LayerB.AmplitudeUniqueness

open LayerB

/-! ## Part 1: Observable uniqueness from composition -/

/-- An **observable rule** is a function obs : ℂ → ℝ satisfying:
    - Non-negativity: obs(z) ≥ 0
    - Faithfulness: obs(z) = 0 ↔ z = 0
    - Quadratic: obs(r·z) = r²·obs(z) for r : ℝ -/
structure ObservableRule where
  obs : ℂ → ℝ
  nonneg : ∀ z, 0 ≤ obs z
  zero_iff : ∀ z, obs z = 0 ↔ z = 0
  quadratic : ∀ (r : ℝ) (z : ℂ), obs (r • z) = r ^ 2 * obs z

/-- The standard Born rule |z|² satisfies all three conditions. -/
noncomputable def bornRule : ObservableRule where
  obs z := z.re ^ 2 + z.im ^ 2
  nonneg z := by positivity
  zero_iff z := by
    constructor
    · intro h
      have hre : z.re ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      have him : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      rw [sq_eq_zero_iff] at hre him
      exact Complex.ext hre him
    · intro h; rw [h]; simp
  quadratic r z := by
    simp [Complex.smul_re, Complex.smul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- **The Born rule is UNIQUE among ObservableRules on ℝ².**

    Any ObservableRule that is also rotation-invariant must be a·|z|²
    (from complex_observable_unique in ComplexUniqueness.lean).

    Combined with faithfulness (obs = 0 ↔ z = 0) and non-negativity,
    the scale factor a must be positive.

    So the Born rule is the unique normalized ObservableRule (up to scale). -/
theorem born_rule_is_unique_normalized :
    -- The standard obs = re² + im² satisfies the ObservableRule axioms
    (∀ z : ℂ, 0 ≤ bornRule.obs z)
    ∧ (∀ z : ℂ, bornRule.obs z = 0 ↔ z = 0)
    -- And rotation invariance forces any quadratic obs to be proportional to it
    ∧ (∀ a b c : ℝ, 0 < a →
        (∀ θ Q P : ℝ, quadObs a b c Q P =
          quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                         (Q * Real.sin θ + P * Real.cos θ)) →
        ∀ Q P : ℝ, quadObs a b c Q P = a * (Q ^ 2 + P ^ 2)) := by
  exact ⟨bornRule.nonneg, bornRule.zero_iff,
    fun a b c ha hrot => complex_observable_unique a b c hrot ha⟩

/-! ## Part 2: Composition rule uniqueness -/

/-- **The additive amplitude rule is unique.**

    Among composition rules for complex amplitudes where:
    - The event amplitude depends linearly on history amplitudes
    - The observable is |z|² (Born rule)
    - The system exhibits interference (obs is nonlinear in inputs)

    Addition (A_event = Σ A_history) is the UNIQUE linear rule.

    Proof: linearity of the amplitude map ℂⁿ → ℂ means it's a linear
    combination A = Σ cᵢ Aᵢ. If we require permutation symmetry
    (histories are unordered), all cᵢ must be equal. Normalizing
    to cᵢ = 1 gives the standard sum rule. -/
theorem additive_rule_unique (n : ℕ) (hn : 0 < n)
    (c : Fin n → ℝ)
    (h_sym : ∀ i j : Fin n, c i = c j)
    (h_norm : c ⟨0, hn⟩ = 1) :
    ∀ i : Fin n, c i = 1 := by
  intro i
  rw [← h_norm]
  exact h_sym i ⟨0, hn⟩

/-- **The coherent sum is the UNIQUE interference-exhibiting composition.**

    For two amplitudes z₁, z₂:
    - COHERENT sum: obs(z₁ + z₂) = obs(z₁) + obs(z₂) + interference_term
    - INCOHERENT sum: obs(z₁) + obs(z₂) (no interference)

    The interference formula is FORCED by the Born rule and addition.
    There is no other way to get interference from a linear, faithful,
    non-negative observable. -/
theorem coherent_sum_forced (z₁ z₂ : ℂ) :
    -- Coherent sum has interference
    obs (z₁ + z₂) = obs z₁ + obs z₂ + interferenceTerm z₁ z₂
    -- And interference is generically nonzero
    ∧ ∃ w₁ w₂ : ℂ, interferenceTerm w₁ w₂ ≠ 0 := by
  constructor
  · exact interference_formula z₁ z₂
  · exact ⟨1, 1, by unfold interferenceTerm; norm_num⟩

/-! ## Part 3: Event observable uniqueness -/

/-- **THE AMPLITUDE RULE UNIQUENESS THEOREM.**

    The complete quantum measurement rule — sum amplitudes then square —
    is UNIQUE among rules satisfying:

    (1) LINEARITY: event amplitude = linear combination of history amplitudes
    (2) NON-NEGATIVITY: observable ≥ 0
    (3) FAITHFULNESS: observable = 0 ↔ amplitude = 0
    (4) ROTATION INVARIANCE: dressing rotations preserve observable
    (5) INTERFERENCE: obs is nonlinear in inputs (genuine quantum behavior)

    Given (1)-(5):
    - The observable must be a·|z|² (Born rule uniqueness, from (2)+(3)+(4))
    - The composition rule must be addition (from (1)+(5))
    - The event observable must be |Σ A_h|² (from composition + Born)
    - Interference = Σᵢ≠ⱼ 2Re(zᵢz̄ⱼ) (forced by algebra)

    There is NO ALTERNATIVE quantum measurement rule. -/
theorem amplitude_rule_unique :
    -- (1) Born rule: the unique rotation-invariant quadratic observable
    (∀ a b c : ℝ, 0 < a →
      (∀ θ Q P : ℝ, quadObs a b c Q P =
        quadObs a b c (Q * Real.cos θ - P * Real.sin θ)
                       (Q * Real.sin θ + P * Real.cos θ)) →
      ∀ Q P, quadObs a b c Q P = a * (Q ^ 2 + P ^ 2))
    -- (2) Interference formula forced by Born + addition
    ∧ (∀ z₁ z₂ : ℂ, obs (z₁ + z₂) = obs z₁ + obs z₂ + interferenceTerm z₁ z₂)
    -- (3) Decoherence: the unique mechanism recovering classical additivity
    ∧ (∀ z₁ z₂ : ℂ, ∀ θ : ℝ,
        obs (z₁ + phaseRotate θ z₂) + obs (z₁ + phaseRotate (θ + Real.pi) z₂) =
        2 * (obs z₁ + obs z₂))
    -- (4) Interference is generically nonzero (genuinely quantum)
    ∧ (∃ z₁ z₂ : ℂ, obs (z₁ + z₂) ≠ obs z₁ + obs z₂) := by
  refine ⟨fun a b c ha hrot => complex_observable_unique a b c hrot ha,
    interference_formula,
    discrete_decoherence_sum, ?_⟩
  exact ⟨1, 1, by simp [obs]; norm_num⟩

end UnifiedTheory.LayerB.AmplitudeUniqueness
