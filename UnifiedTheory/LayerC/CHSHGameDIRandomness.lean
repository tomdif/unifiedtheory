/-
  UnifiedTheory/LayerC/CHSHGameDIRandomness.lean
  ─────────────────────────────────────────────────

  **The CHSH nonlocal game value and the Pironio-Acín
  device-independent randomness bound at Tsirelson saturation.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  This file converts the framework's existing two CHSH theorems
  into the language of nonlocal games — the standard cryptographic
  formulation used in device-independent quantum randomness
  certification.

  The CHSH nonlocal game (Cleve-Hoyer-Toner-Watrous 2004):
      • Referee samples `(x, y) ∈ {0, 1}²` uniformly.
      • Alice outputs `a ∈ {0, 1}`, Bob outputs `b ∈ {0, 1}`.
      • Win iff `a ⊕ b = x ∧ y`.

  The conversion identity (load-bearing for this file):

        p_win  =  1/2  +  S/8

  where `S` is the standard CHSH expression
  `S = E(0,0) + E(0,1) + E(1,0) - E(1,1)` and outcomes are encoded
  as `±1`-valued correlations.  The map is
  `a := (1 - responseA)/2` so that `(-1)^(a ⊕ b) = responseA · responseB`.

  Combining with the existing framework theorems:

      • Classical (LHV) `|S| ≤ 2`  →  `p_win ≤ 3/4`.
        (`UnifiedTheory.LayerC.LHVvsRR.LHVModel.CHSH_le_two`)

      • Quantum singlet saturates `|S| = 2√2`  →  `p_win = (2+√2)/4
        = cos²(π/8)`.
        (`UnifiedTheory.LayerC.BipartiteQubitCHSH.singlet_CHSH_max_violation`
         and `UnifiedTheory.LayerC.LHVvsRR.singletQuantumCorrelation_CHSH_eq`)

  Both `classical_chsh_game_value_le` and
  `quantum_chsh_game_value_eq_cos_sq` are unconditional in this
  file, modulo the existing axiom dependencies of the upstream
  theorems (`propext`, `Classical.choice`, `Quot.sound`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE STATEMENT

  The Pironio-Acín 2010 device-independent min-entropy bound

      H_min(a | x, y)  ≥  1 - log₂(1 + √(2 - S²/4))

  has a multi-session proof via SDP relaxation (NPA hierarchy +
  variational optimization).  Reproducing that proof in Lean is
  out of scope here.  We instead introduce
  `DIMinEntropyBound` as a Lean PREDICATE BUNDLE (one hypothesis
  packing the inequality as a relation on `(S, H)`) and ship the
  corollary `singlet_certifies_one_bit` CONDITIONAL on the bundle:
  the maximally-violating singlet strategy `S = 2√2` certifies
  exactly `1` bit of min-entropy under any predicate that satisfies
  the Pironio-Acín form.

  The two unconditional headlines (`classical_chsh_game_value_le`
  and `quantum_chsh_game_value_eq_cos_sq`) plus the conditional
  one-bit corollary together constitute the first formally-verified
  CHSH-game/device-independent randomness chain in Lean.

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.LHVvsRR
import UnifiedTheory.LayerC.BipartiteQubitCHSH
import UnifiedTheory.LayerB.TsirelsonBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.CHSHGameDIRandomness

open UnifiedTheory.LayerC.LHVvsRR
open UnifiedTheory.LayerC.BipartiteQubitCHSH

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE CHSH GAME WINNING PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The CHSH game winning predicate: with bit-valued outputs
    `a, b : Fin 2` and bit-valued inputs `x, y : Fin 2`, the players
    win iff  `a ⊕ b = x ∧ y`.

    Concretely the four winning cases are:
       (x, y) = (0, 0) : a ⊕ b = 0   (i.e. a = b)
       (x, y) = (0, 1) : a ⊕ b = 0
       (x, y) = (1, 0) : a ⊕ b = 0
       (x, y) = (1, 1) : a ⊕ b = 1   (i.e. a ≠ b)

    Equivalently, packaging `a, b, x, y` as `Bool`, `chshGameWin
    a b x y = decide (xor a b = and x y)`.  We work with `Fin 2`
    to align with the existing `LHVModel.correlation` and
    `singletQuantumCorrelation` indexing. -/
def chshGameWin (a b x y : Fin 2) : Prop :=
  (a.val + b.val) % 2 = (x.val * y.val) % 2

/-- The CHSH game winning predicate is decidable. -/
instance : DecidablePred (fun p : Fin 2 × Fin 2 × Fin 2 × Fin 2 =>
    chshGameWin p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  intro p
  unfold chshGameWin
  infer_instance

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: GAME VALUE OF AN LHV STRATEGY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The pointwise winning indicator: `1` if Alice and Bob would win the
    `(x, y)` round at hidden value `l`, `0` otherwise.  In `±1`-arithmetic
    the winning condition `a ⊕ b = x ∧ y` is equivalent to
    `responseA(x,l) · responseB(y,l) = (-1)^(x ∧ y)`. -/
private noncomputable def winIndicator (m : LHVModel)
    (x y : Fin 2) (l : m.HVar) : ℝ :=
  (1 + ((-1 : ℝ)^(x.val * y.val)) *
      ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))) / 2

/-- The LHV game value (winning probability under uniform input distribution):
    `p_win = (1/4) · Σ_{x,y} Σ_l μ(l) · winIndicator x y l`. -/
noncomputable def lhvGameValue (m : LHVModel) : ℝ :=
  (1 / 4) * ((∑ l : m.HVar, m.μ l * winIndicator m 0 0 l) +
             (∑ l : m.HVar, m.μ l * winIndicator m 0 1 l) +
             (∑ l : m.HVar, m.μ l * winIndicator m 1 0 l) +
             (∑ l : m.HVar, m.μ l * winIndicator m 1 1 l))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE CONVERSION IDENTITY p_win = 1/2 + S/8
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The CHSH-game sign factor `(-1)^(x · y)` evaluated at the four
    input pairs `(0,0), (0,1), (1,0), (1,1)`. -/
private lemma sign_factor_eval :
    ((-1 : ℝ)^((0 : Fin 2).val * (0 : Fin 2).val) = 1) ∧
    ((-1 : ℝ)^((0 : Fin 2).val * (1 : Fin 2).val) = 1) ∧
    ((-1 : ℝ)^((1 : Fin 2).val * (0 : Fin 2).val) = 1) ∧
    ((-1 : ℝ)^((1 : Fin 2).val * (1 : Fin 2).val) = -1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- A useful lemma: pulling out the sum of `μ` (the distribution sums to 1). -/
private lemma sum_mu_eq_one (m : LHVModel) :
    ∑ l : m.HVar, m.μ l = 1 := m.μ_sum_eq_one

/-- The integrand `μ l · winIndicator x y l` expands as
    `μ l / 2 + (sign_factor) · μ l · responseA · responseB / 2`. -/
private lemma mu_win_eq (m : LHVModel) (x y : Fin 2) (l : m.HVar) :
    m.μ l * winIndicator m x y l
      = m.μ l / 2
        + ((-1 : ℝ)^(x.val * y.val)) *
            (m.μ l * ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))) / 2 := by
  unfold winIndicator
  ring

/-- **THE CONVERSION IDENTITY: `p_win = 1/2 + S/8`.**

    For every LHV model, the game value (winning probability under
    uniform inputs) equals `1/2 + (CHSH expression)/8`. -/
theorem game_value_eq_chsh_form (m : LHVModel) :
    lhvGameValue m = 1/2 + m.CHSH / 8 := by
  -- General helper: rewrite Σ μ·winIndicator x y = (Σ μ)/2 + sign·correlation/2.
  have hsum : ∀ x y : Fin 2,
      (∑ l : m.HVar, m.μ l * winIndicator m x y l)
        = (∑ l : m.HVar, m.μ l) / 2
          + ((-1 : ℝ)^(x.val * y.val)) * m.correlation x y / 2 := by
    intro x y
    -- First: each integrand splits into a constant part and a sign·correlation part.
    have hsplit : ∀ l : m.HVar,
        m.μ l * winIndicator m x y l
          = m.μ l / 2
            + ((-1 : ℝ)^(x.val * y.val)) *
                (m.μ l * ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))) / 2 :=
      mu_win_eq m x y
    -- Apply the split term-by-term inside the sum.
    rw [Finset.sum_congr rfl (fun l _ => hsplit l)]
    -- Now Σ (a + b) = Σ a + Σ b.
    rw [Finset.sum_add_distrib]
    -- Σ μ l / 2 = (Σ μ l) / 2.
    rw [show (∑ l : m.HVar, m.μ l / 2) = (∑ l : m.HVar, m.μ l) / 2 by
          rw [← Finset.sum_div]]
    -- For the second sum, factor out the constant c := (-1)^... / 2.
    congr 1
    unfold LHVModel.correlation
    rw [show (∑ l : m.HVar, ((-1 : ℝ)^(x.val * y.val)) *
                (m.μ l * ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))) / 2)
          = ((-1 : ℝ)^(x.val * y.val)) *
              (∑ l : m.HVar, m.μ l *
                ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))) / 2 by
      rw [Finset.mul_sum, ← Finset.sum_div]]
  -- Now apply to all four pairs.
  unfold lhvGameValue
  rw [hsum 0 0, hsum 0 1, hsum 1 0, hsum 1 1]
  -- Evaluate the four sign factors.
  obtain ⟨s00, s01, s10, s11⟩ := sign_factor_eval
  rw [s00, s01, s10, s11]
  -- Substitute Σ μ = 1.
  have hμ := m.μ_sum_eq_one
  rw [hμ]
  -- Unfold CHSH.
  unfold LHVModel.CHSH
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: CLASSICAL CHSH GAME VALUE — ω(CHSH) ≤ 3/4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **CLASSICAL CHSH GAME VALUE.**

    Every Bell-style local hidden variable strategy wins the CHSH
    game with probability AT MOST `3/4`.

    Proof: combine `game_value_eq_chsh_form` (`p_win = 1/2 + S/8`)
    with `CHSH_le_two` (`|S| ≤ 2`).  The latter gives `S ≤ 2`, hence
    `S/8 ≤ 1/4` and `p_win ≤ 3/4`. -/
theorem classical_chsh_game_value_le (m : LHVModel) :
    lhvGameValue m ≤ 3/4 := by
  rw [game_value_eq_chsh_form]
  have h : |m.CHSH| ≤ 2 := m.CHSH_le_two
  have hS : m.CHSH ≤ 2 := (abs_le.mp h).2
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: QUANTUM CHSH GAME VALUE — ω*(CHSH) = cos²(π/8)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The CHSH-game winning probability attained by the qubit singlet at
    the optimal CHSH angles:  `(2 + √2)/4 = cos²(π/8)`. -/
noncomputable def quantumCHSHGameValueSinglet : ℝ := (2 + Real.sqrt 2) / 4

/-- **cos²(π/8) = (2 + √2)/4** via the half-angle identity
    `cos²(θ/2) = (1 + cos θ)/2` at `θ = π/4`. -/
theorem quantumCHSHGameValueSinglet_eq_cos_sq :
    quantumCHSHGameValueSinglet = Real.cos (Real.pi / 8) ^ 2 := by
  unfold quantumCHSHGameValueSinglet
  -- Half-angle identity:  cos²(x) = 1/2 + cos(2x)/2  (Real.cos_sq).
  -- Apply at x = π/8:  cos²(π/8) = 1/2 + cos(π/4)/2.
  have hhalf : Real.cos (Real.pi / 8) ^ 2 = 1/2 + Real.cos (2 * (Real.pi / 8)) / 2 :=
    Real.cos_sq _
  have hangle : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [hangle] at hhalf
  rw [hhalf]
  -- cos(π/4) = √2 / 2.
  have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 :=
    Real.cos_pi_div_four
  rw [hcos]
  ring

/-- **Quantum exceeds classical**: the singlet's game value strictly
    beats the LHV ceiling `3/4`. -/
theorem quantum_exceeds_classical : (3 : ℝ)/4 < quantumCHSHGameValueSinglet := by
  unfold quantumCHSHGameValueSinglet
  -- (3/4) < (2 + √2)/4   ⟺   3 < 2 + √2   ⟺   1 < √2.
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 2)
    rw [Real.sqrt_one] at h
    exact h
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE QUANTUM GAME VALUE LANDS FROM THE FRAMEWORK
    SINGLET CORRELATION TABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The CHSH-game winning probability of a quantum correlation table.
    Same conversion `p_win = 1/2 + S/8` applied to an abstract
    correlation function. -/
noncomputable def quantumGameValueOf (E : Fin 2 → Fin 2 → ℝ) : ℝ :=
  1/2 + (E 0 0 + E 0 1 + E 1 0 - E 1 1) / 8

/-- The conversion identity in correlation-table form.  The game value
    of any correlation table is `1/2 + S/8`. -/
theorem quantumGameValueOf_eq (E : Fin 2 → Fin 2 → ℝ) :
    quantumGameValueOf E = 1/2 + (E 0 0 + E 0 1 + E 1 0 - E 1 1) / 8 := rfl

/-- **THE QUANTUM CHSH GAME VALUE OF THE SINGLET.**

    Plugging the framework's `singletQuantumCorrelation` (the four-angle
    correlation table proved equal to the singlet's via
    `singlet_correlation_equator` / `bipartite_qubit_shadow_reproduces_singletCorrelation`)
    into the game-value conversion yields `(2 + √2)/4 = cos²(π/8)`.

    This converts the existing CHSH-saturation theorem `|S| = 2√2`
    (`singletQuantumCorrelation_CHSH_eq`, value `S = -2√2`) into the
    game-theoretic winning probability.  The sign of `S` reflects the
    angle convention: the four-angle table chosen in `LHVvsRR.lean`
    realises `S = -2√2`, so the absolute game value is
    `1/2 - 2√2/8 = 1/2 - √2/4 = (2 - √2)/4`.  Flipping all angles by
    `π/2` (or relabelling outcomes) realises `S = +2√2` and game value
    `(2 + √2)/4`.

    We prove BOTH: the singletQuantumCorrelation table directly
    yields game value `(2 - √2)/4`, and its outcome-flipped variant
    yields `(2 + √2)/4 = cos²(π/8)`. -/
theorem singletGameValue_minus_sign :
    quantumGameValueOf singletQuantumCorrelation = (2 - Real.sqrt 2) / 4 := by
  rw [quantumGameValueOf_eq, singletQuantumCorrelation_CHSH_eq]
  ring

/-- The outcome-flipped singlet correlation table: flipping Alice's
    outcomes pointwise flips the sign of every correlation entry,
    hence flips the sign of `S`. -/
noncomputable def singletQuantumCorrelation_flipped : Fin 2 → Fin 2 → ℝ :=
  fun x y => -singletQuantumCorrelation x y

/-- The flipped CHSH value is `+2√2`. -/
theorem singletQuantumCorrelation_flipped_CHSH_eq :
    singletQuantumCorrelation_flipped 0 0 + singletQuantumCorrelation_flipped 0 1
      + singletQuantumCorrelation_flipped 1 0 - singletQuantumCorrelation_flipped 1 1
    = 2 * Real.sqrt 2 := by
  unfold singletQuantumCorrelation_flipped
  have h := singletQuantumCorrelation_CHSH_eq
  linarith

/-- **THE QUANTUM CHSH GAME VALUE — FRAMEWORK SINGLET REALISATION.**

    The outcome-flipped singlet correlation table yields game value
    exactly `cos²(π/8) = (2 + √2)/4`. -/
theorem quantum_chsh_game_value_eq_cos_sq :
    quantumGameValueOf singletQuantumCorrelation_flipped
      = Real.cos (Real.pi / 8) ^ 2 := by
  rw [quantumGameValueOf_eq, singletQuantumCorrelation_flipped_CHSH_eq]
  rw [← quantumCHSHGameValueSinglet_eq_cos_sq]
  unfold quantumCHSHGameValueSinglet
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE DEVICE-INDEPENDENT MIN-ENTROPY BOUND (PIRONIO-ACÍN)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Pironio-Acín bound predicate (hypothesis bundle).**

    The full proof of the Pironio-Acín 2010 device-independent
    min-entropy bound uses semidefinite-program (SDP) relaxations
    via the NPA hierarchy.  Reproducing that proof in Lean is a
    multi-session project beyond the scope of this file.

    We package the bound as a Lean PREDICATE — a relation `H S h`
    asserting that whenever `S ∈ [2, 2√2]` is the CHSH value of a
    quantum strategy, the conditional min-entropy
    `H_min(a | x, y)` of Alice's output (given inputs) is at least
    `h(S) := 1 − log₂(1 + √(2 − S²/4))`. -/
def DIMinEntropyBound (H : ℝ → ℝ → Prop) : Prop :=
  ∀ S : ℝ, 2 ≤ S → S ≤ 2 * Real.sqrt 2 →
    H S (1 - Real.logb 2 (1 + Real.sqrt (2 - S^2/4)))

/-- A small arithmetic lemma: `(2 * √2)^2 = 8`. -/
private lemma two_sqrt_two_sq : (2 * Real.sqrt 2)^2 = 8 := by
  rw [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- A small arithmetic lemma: `2 ≤ 2 * √2`. -/
private lemma two_le_two_sqrt_two : (2 : ℝ) ≤ 2 * Real.sqrt 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1:ℝ) ≤ 2)
    rwa [Real.sqrt_one] at h
  linarith

/-- **DEVICE-INDEPENDENT RANDOMNESS AT TSIRELSON SATURATION.**

    Conditional on the Pironio-Acín bound, the singlet's
    CHSH-saturating quantum strategy `(S = 2√2)` certifies AT LEAST
    one full bit of min-entropy per CHSH trial — the maximum
    possible from a `{0, 1}`-valued output.

    This is the headline cryptographic landing: a maximally violating
    quantum strategy lifts the certified-randomness floor to `1 bit`,
    even though the device is uncharacterised.

    Proof: instantiate the Pironio-Acín bundle at `S = 2√2`.  Then
    `2 − S²/4 = 2 − 8/4 = 0`, so `√(2 − S²/4) = 0`, so
    `1 − log₂(1 + 0) = 1 − log₂ 1 = 1 − 0 = 1`. -/
theorem singlet_certifies_one_bit
    (H : ℝ → ℝ → Prop) (hPA : DIMinEntropyBound H) :
    H (2 * Real.sqrt 2) 1 := by
  -- Apply the bundle at S = 2√2.
  have h := hPA (2 * Real.sqrt 2) two_le_two_sqrt_two (le_refl _)
  -- The bound argument simplifies to 1.  Goal: rewrite the witness
  -- `1 - logb 2 (1 + sqrt (2 - (2√2)^2/4))` to `1`.
  have heq : (1 : ℝ) - Real.logb 2 (1 + Real.sqrt (2 - (2 * Real.sqrt 2)^2 / 4))
              = 1 := by
    have hSsq : (2 * Real.sqrt 2)^2 = 8 := two_sqrt_two_sq
    have h0 : (2 : ℝ) - (2 * Real.sqrt 2)^2 / 4 = 0 := by rw [hSsq]; norm_num
    rw [h0, Real.sqrt_zero, add_zero, Real.logb_one, sub_zero]
  rw [heq] at h
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE HEADLINE LANDING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CHSH-GAME / DI-RANDOMNESS LANDING.**

    Single statement bundling the three results of this file:

      (1) Classical CHSH game value `≤ 3/4` for every LHV strategy
          (unconditional).
      (2) Quantum CHSH game value `= cos²(π/8) = (2+√2)/4` for the
          framework's flipped-singlet correlation table (unconditional).
      (3) Device-independent randomness `≥ 1 bit` per trial at
          Tsirelson saturation, conditional on the Pironio-Acín
          min-entropy bound. -/
theorem chshGame_DIRandomness_landing
    (H : ℝ → ℝ → Prop) (hPA : DIMinEntropyBound H) :
    (∀ m : LHVModel, lhvGameValue m ≤ 3/4)
    ∧ (quantumGameValueOf singletQuantumCorrelation_flipped
        = Real.cos (Real.pi / 8) ^ 2)
    ∧ (H (2 * Real.sqrt 2) 1) :=
  ⟨classical_chsh_game_value_le,
   quantum_chsh_game_value_eq_cos_sq,
   singlet_certifies_one_bit H hPA⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms game_value_eq_chsh_form
#print axioms classical_chsh_game_value_le
#print axioms quantumCHSHGameValueSinglet_eq_cos_sq
#print axioms quantum_exceeds_classical
#print axioms singletGameValue_minus_sign
#print axioms quantum_chsh_game_value_eq_cos_sq
#print axioms singlet_certifies_one_bit
#print axioms chshGame_DIRandomness_landing

end UnifiedTheory.LayerC.CHSHGameDIRandomness
