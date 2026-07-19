/-
  UnifiedTheory/LayerC/LHVvsRR.lean
  ─────────────────────────────────

  **The asymmetric distinction between Local Hidden Variable (LHV)
  models and Raymond-Robichaud local-realistic theories.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  The Raymond-Robichaud paper (and the formalised local-realist
  shadow theorem in `BipartiteNoSignallingAnalyticCoreDischarge`)
  observes that Bell's theorem refutes only the STRONGER form of
  local realism — the one that postulates a single hidden variable
  `λ` from which both Alice's and Bob's outcomes are produced by
  local response functions:

      P(a, b | x, y) = ∑_λ μ(λ) · p_A(a | x, λ) · p_B(b | y, λ).

  Their broader notion (`LocalRealisticTheory` in
  `LayerC/LocalRealisticAxioms.lean`) does NOT demand such a single
  global hidden parameter; it only demands the diagrammatic
  postulates of Section 3 of the paper.

  This file makes the distinction formal in Lean:

    (A) `LHVModel` — Bell's `λ`-factorisable model with a discrete
        hidden-variable space `Λ : Type` (a `Fintype` with a discrete
        probability distribution), Alice's and Bob's deterministic
        response functions, and ±1-valued outcomes.

    (B) `LHVModel.CHSH_le_two` — every LHV model satisfies the
        classical CHSH bound `|S| ≤ 2`.  This is Bell's theorem
        in its purest combinatorial form.  We reuse the algebraic
        CHSH-bound lemma `chsh_factorizable_bound` from
        `LayerB/SeparableCHSH.lean` pointwise at each `λ` and then
        bound the convex combination under the probability sum.

    (C) `singletQuantumCorrelation` — the standard four-angle
        correlation table `E(x, y) := -cos(θ_x - θ_y)` with
        Alice's angles `{0, π/2}` and Bob's angles `{π/4, -π/4}`,
        i.e. the correlation table the QM singlet PRODUCES on
        the bipartite-qubit substrate.

    (D) `singletQuantumCorrelation_CHSH_eq` — direct trig:
        `E(0, π/4) + E(0, -π/4) + E(π/2, π/4) - E(π/2, -π/4) =
         -2√2`.

    (E) `singlet_has_no_LHV_shadow` — NO LHV MODEL CAN REPRODUCE
        THE SINGLET'S CHSH CORRELATIONS.  Bell's theorem on the
        framework's substrate.

    (F) `bipartite_qubit_shadow_has_RR_but_not_LHV` — THE
        ASYMMETRIC HEADLINE.  The bipartite-qubit substrate of
        phase-quotient unitary QM HAS a Raymond-Robichaud
        local-realistic shadow (via
        `bipartiteQubitUnitaryQM_has_localRealisticModel`)
        BUT DOES NOT HAVE a Bell-style LHV shadow (via
        `singlet_has_no_LHV_shadow`).  Bell's theorem refutes
        the stronger LHV form, NOT Raymond-Robichaud's broader
        local realism.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  DESIGN CHOICE: DISCRETE Λ

  We use a `Fintype Λ` plus an explicit discrete probability
  distribution `μ : Λ → ℝ` (`μ_nonneg`, `μ_sum_eq_one`) instead of
  Mathlib's measure-theoretic `MeasureTheory.Measure`.  This is
  standard textbook practice (Bell's original argument uses
  finite Λ in the deterministic-response setting) and avoids
  having to set up integration infrastructure.  The combinatorial
  content of Bell's theorem — `|S(λ)| ≤ 2` pointwise then convex
  combine — is unchanged.

  Zero `sorry`.  Zero custom `axiom`.
-/

import UnifiedTheory.LayerC.BipartiteQubitCHSH
import UnifiedTheory.LayerB.SeparableCHSH
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.LHVvsRR

open UnifiedTheory.LayerB.SeparableCHSH
open UnifiedTheory.LayerC.LocalRealisticAxioms
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE LHV MODEL (BELL'S λ-FACTORISABILITY)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A Local Hidden Variable model** for a bipartite two-setting
    scenario, in Bell's classic deterministic form with a discrete
    hidden-parameter space `Λ`.

    The fields encode:
      * `Λ` — the (finite) hidden-variable space;
      * `μ` — a probability distribution on `Λ` (nonneg + sums to 1);
      * `responseA x λ` — Alice's outcome (`+1` or `-1`) at setting
        `x ∈ Fin 2` and hidden value `λ`;
      * `responseB y λ` — Bob's outcome (`+1` or `-1`) at setting
        `y ∈ Fin 2` and hidden value `λ`.

    The bipartite predicted correlation is
    `correlation x y = ∑_λ μ(λ) · responseA(x, λ) · responseB(y, λ)`,
    Bell's `λ`-factorisability assumption.

    This is STRICTLY STRONGER than Raymond-Robichaud's
    `LocalRealisticTheory` (which posits no single λ): an LHV model
    induces such a global stochastic latent. -/
structure LHVModel where
  /-- The discrete hidden-variable space (named `HVar` because
      `Λ` would mask the standard `λ` binder in Lean syntax). -/
  HVar : Type
  /-- The hidden-variable space is finite. -/
  isFintype : Fintype HVar
  /-- The discrete probability distribution. -/
  μ : HVar → ℝ
  /-- Distribution is nonnegative. -/
  μ_nonneg : ∀ l, 0 ≤ μ l
  /-- Distribution sums to one. -/
  μ_sum_eq_one : (Finset.univ : Finset HVar).sum (fun l => μ l) = 1
  /-- Alice's response function at setting `x` and hidden value `l`. -/
  responseA : Fin 2 → HVar → ℤ
  /-- Bob's response function at setting `y` and hidden value `l`. -/
  responseB : Fin 2 → HVar → ℤ
  /-- Alice's outcomes are ±1. -/
  responseA_pm_one : ∀ x l, responseA x l = 1 ∨ responseA x l = -1
  /-- Bob's outcomes are ±1. -/
  responseB_pm_one : ∀ y l, responseB y l = 1 ∨ responseB y l = -1

-- Activate the LHV model's `Fintype` instance on `HVar`.
attribute [instance] LHVModel.isFintype

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: LHV-PREDICTED CORRELATIONS AND CHSH VALUE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The LHV-predicted correlation at settings `(x, y)`:
    `correlation x y = ∑_l μ(l) · (responseA x l) · (responseB y l)`. -/
noncomputable def LHVModel.correlation (m : LHVModel) (x y : Fin 2) : ℝ :=
  ∑ l : m.HVar, m.μ l * ((m.responseA x l : ℝ) * (m.responseB y l : ℝ))

/-- The CHSH expression for an LHV model:
    `S = E(0,0) + E(0,1) + E(1,0) - E(1,1)`. -/
noncomputable def LHVModel.CHSH (m : LHVModel) : ℝ :=
  m.correlation 0 0 + m.correlation 0 1 + m.correlation 1 0 - m.correlation 1 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BELL'S THEOREM — CLASSICAL CHSH BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The pointwise CHSH expression of an LHV model at hidden value `l`. -/
private noncomputable def LHVModel.pointwiseCHSH (m : LHVModel) (l : m.HVar) : ℝ :=
  (m.responseA 0 l : ℝ) * (m.responseB 0 l : ℝ)
  + (m.responseA 0 l : ℝ) * (m.responseB 1 l : ℝ)
  + (m.responseA 1 l : ℝ) * (m.responseB 0 l : ℝ)
  - (m.responseA 1 l : ℝ) * (m.responseB 1 l : ℝ)

/-- `|responseA x l| ≤ 1` as a real number, since outcomes are `±1`. -/
private lemma abs_responseA_le_one (m : LHVModel) (x : Fin 2) (l : m.HVar) :
    |(m.responseA x l : ℝ)| ≤ 1 := by
  rcases m.responseA_pm_one x l with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- `|responseB y l| ≤ 1` as a real number, since outcomes are `±1`. -/
private lemma abs_responseB_le_one (m : LHVModel) (y : Fin 2) (l : m.HVar) :
    |(m.responseB y l : ℝ)| ≤ 1 := by
  rcases m.responseB_pm_one y l with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- **Pointwise CHSH bound (Bell's combinatorial inequality).**
    At every hidden value `l`, the pointwise CHSH expression has
    `|pointwiseCHSH l| ≤ 2`.  Proved by reusing
    `chsh_factorizable_bound` from `LayerB/SeparableCHSH.lean` with
    `f x := responseA x l` and `g y := responseB y l` (bridged through
    a `Bool` reindexing). -/
private lemma LHVModel.pointwiseCHSH_abs_le_two (m : LHVModel) (l : m.HVar) :
    |m.pointwiseCHSH l| ≤ 2 := by
  -- Define f, g : Bool → ℝ via the Bool-to-Fin-2 correspondence
  -- (false ↦ 0, true ↦ 1).
  let f : Bool → ℝ := fun b =>
    (m.responseA (Bool.casesOn b (0 : Fin 2) (1 : Fin 2)) l : ℝ)
  let g : Bool → ℝ := fun b =>
    (m.responseB (Bool.casesOn b (0 : Fin 2) (1 : Fin 2)) l : ℝ)
  have hf : ∀ x, |f x| ≤ 1 := by
    intro x; cases x with
    | false => exact abs_responseA_le_one m 0 l
    | true => exact abs_responseA_le_one m 1 l
  have hg : ∀ y, |g y| ≤ 1 := by
    intro y; cases y with
    | false => exact abs_responseB_le_one m 0 l
    | true => exact abs_responseB_le_one m 1 l
  have hbound := chsh_factorizable_bound f g hf hg
  -- Unfold chshExpr and identify with pointwiseCHSH
  change |m.pointwiseCHSH l| ≤ 2
  have eq_expr :
      chshExpr (fun x y => f x * g y) = m.pointwiseCHSH l := by
    change f false * g false + f false * g true + f true * g false
           - f true * g true = m.pointwiseCHSH l
    rfl
  rw [eq_expr] at hbound
  exact hbound

/-- The correlation `correlation x y` equals the sum over `l` of
    `μ l` times the bilinear factor.  (Definitional.) -/
private lemma LHVModel.correlation_eq_sum (m : LHVModel) (x y : Fin 2) :
    m.correlation x y
      = ∑ l : m.HVar, m.μ l * ((m.responseA x l : ℝ) * (m.responseB y l : ℝ)) :=
  rfl

/-- The CHSH expression equals the sum over `l` of `μ l · pointwiseCHSH l`. -/
private lemma LHVModel.CHSH_eq_sum (m : LHVModel) :
    m.CHSH = ∑ l : m.HVar, m.μ l * m.pointwiseCHSH l := by
  unfold LHVModel.CHSH
  simp only [LHVModel.correlation_eq_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro l _
  unfold LHVModel.pointwiseCHSH
  ring

/-- **BELL'S THEOREM — CLASSICAL CHSH BOUND for LHV models.**

    Every Bell-style local hidden variable model satisfies `|S| ≤ 2`.

    Proof: by `pointwiseCHSH_abs_le_two`, the integrand has absolute
    value at most 2 at every `l`.  Multiplying by the nonnegative
    probability density `μ` and summing gives
    `|∑ μ(l)·CHSH(l)| ≤ ∑ μ(l)·2 = 2`. -/
theorem LHVModel.CHSH_le_two (m : LHVModel) : |m.CHSH| ≤ 2 := by
  rw [LHVModel.CHSH_eq_sum]
  -- |∑ μ l · S(l)| ≤ ∑ |μ l · S(l)| ≤ ∑ μ l · 2 = 2
  have h1 : |∑ l : m.HVar, m.μ l * m.pointwiseCHSH l|
              ≤ ∑ l : m.HVar, |m.μ l * m.pointwiseCHSH l| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ l ∈ (Finset.univ : Finset m.HVar),
              |m.μ l * m.pointwiseCHSH l| ≤ m.μ l * 2 := by
    intro l _
    rw [abs_mul, abs_of_nonneg (m.μ_nonneg l)]
    exact mul_le_mul_of_nonneg_left (m.pointwiseCHSH_abs_le_two l) (m.μ_nonneg l)
  have h3 : ∑ l : m.HVar, |m.μ l * m.pointwiseCHSH l|
              ≤ ∑ l : m.HVar, m.μ l * 2 :=
    Finset.sum_le_sum h2
  have h4 : ∑ l : m.HVar, m.μ l * 2 = 2 := by
    rw [← Finset.sum_mul, m.μ_sum_eq_one, one_mul]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: HASLHVSHADOW PREDICATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The HasLHVShadow predicate.**  A correlation table
    `predictedCorrelation : Fin 2 → Fin 2 → ℝ` has an LHV shadow
    if there exists an LHV model whose predicted two-party
    correlations match it for every choice of settings.

    Cf. RR's broader `HasLocalRealisticModel`: the present notion is
    STRICTLY STRONGER (it requires a single global hidden variable). -/
def HasLHVShadow (predictedCorrelation : Fin 2 → Fin 2 → ℝ) : Prop :=
  ∃ m : LHVModel, ∀ x y : Fin 2, m.correlation x y = predictedCorrelation x y

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE SINGLET QUANTUM CORRELATION TABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The singlet's CHSH-attaining correlation function at the standard
    angles `(0, π/2; π/4, -π/4)`:
       `E(x, y) := -cos(θ_x - θ_y)`
    where Alice's angles are `θ_0 = 0, θ_1 = π/2` and Bob's are
    `θ_0 = π/4, θ_1 = -π/4`.

    These are EXACTLY the correlations produced by the bipartite-qubit
    substrate at the four standard Bell angles, as proved by
    `BipartiteQubitCHSH.singlet_correlation_equator`. -/
noncomputable def singletQuantumCorrelation : Fin 2 → Fin 2 → ℝ :=
  fun x y => match x, y with
    | 0, 0 => -Real.cos (0 - Real.pi/4)
    | 0, 1 => -Real.cos (0 - -(Real.pi/4))
    | 1, 0 => -Real.cos (Real.pi/2 - Real.pi/4)
    | 1, 1 => -Real.cos (Real.pi/2 - -(Real.pi/4))

/-- **The singlet's CHSH value at the standard angles is `-2√2`.**

    Direct trig:
      `E(0,0) = -cos(-π/4) = -cos(π/4)`
      `E(0,1) = -cos(π/4) = -cos(π/4)`
      `E(1,0) = -cos(π/4) = -cos(π/4)`
      `E(1,1) = -cos(3π/4) = cos(π/4)`
      ⇒ S = -3·cos(π/4) - cos(π/4) = -4·cos(π/4) = -2√2. -/
theorem singletQuantumCorrelation_CHSH_eq :
    singletQuantumCorrelation 0 0 + singletQuantumCorrelation 0 1
      + singletQuantumCorrelation 1 0 - singletQuantumCorrelation 1 1
    = -(2 * Real.sqrt 2) := by
  -- Reduce the four `match` calls to their explicit forms.
  have e00 : singletQuantumCorrelation 0 0 = -Real.cos ((0 : ℝ) - Real.pi/4) := rfl
  have e01 : singletQuantumCorrelation 0 1 = -Real.cos ((0 : ℝ) - -(Real.pi/4)) := rfl
  have e10 : singletQuantumCorrelation 1 0 = -Real.cos (Real.pi/2 - Real.pi/4) := rfl
  have e11 : singletQuantumCorrelation 1 1 = -Real.cos (Real.pi/2 - -(Real.pi/4)) := rfl
  rw [e00, e01, e10, e11]
  -- Simplify each cosine argument.
  have h1 : Real.cos ((0 : ℝ) - Real.pi/4) = Real.cos (Real.pi/4) := by
    rw [show (0 : ℝ) - Real.pi/4 = -(Real.pi/4) by ring, Real.cos_neg]
  have h2 : Real.cos ((0 : ℝ) - -(Real.pi/4)) = Real.cos (Real.pi/4) := by
    rw [show (0 : ℝ) - -(Real.pi/4) = Real.pi/4 by ring]
  have h3 : Real.cos (Real.pi/2 - Real.pi/4) = Real.cos (Real.pi/4) := by
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring]
  have h4 : Real.cos (Real.pi/2 - -(Real.pi/4)) = -Real.cos (Real.pi/4) := by
    rw [show Real.pi/2 - -(Real.pi/4) = 3 * Real.pi/4 by ring]
    exact UnifiedTheory.LayerB.BellTheorem.cos_three_pi_four
  rw [h1, h2, h3, h4]
  -- Now reduces to: -cos + -cos + -cos - (-(-cos)) = -(2√2).
  -- That is -3cos - cos = -4 cos = -2 · (2 cos) = -2 · √2.
  have hkey :
      2 * Real.cos (Real.pi/4) = Real.sqrt 2 :=
    UnifiedTheory.LayerB.TsirelsonBound.two_mul_cos_pi_four_eq_sqrt_two
  have h_arith :
      -Real.cos (Real.pi/4) + -Real.cos (Real.pi/4)
        + -Real.cos (Real.pi/4) - -(-Real.cos (Real.pi/4))
      = -(2 * (2 * Real.cos (Real.pi/4))) := by ring
  rw [h_arith, hkey]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: NO LHV MODEL CAN REPRODUCE THE SINGLET CORRELATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A short arithmetic lemma: `2 * √2 > 2`. -/
private lemma two_sqrt_two_gt_two : 2 * Real.sqrt 2 > 2 := by
  have hs : Real.sqrt 2 > 1 := by
    have h1 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h1
    exact h1
  linarith

/-- **NO LHV MODEL CAN REPRODUCE THE SINGLET CORRELATIONS.**

    Suppose an LHV model `m` reproduced the singlet's CHSH-attaining
    correlations.  Then by `CHSH_le_two`, `|m.CHSH| ≤ 2`; but
    by `singletQuantumCorrelation_CHSH_eq`, `m.CHSH = -2√2`, hence
    `|m.CHSH| = 2√2 > 2`, contradiction. -/
theorem singlet_has_no_LHV_shadow :
    ¬ HasLHVShadow singletQuantumCorrelation := by
  rintro ⟨m, hm⟩
  have hbound : |m.CHSH| ≤ 2 := m.CHSH_le_two
  have hCHSH : m.CHSH = -(2 * Real.sqrt 2) := by
    unfold LHVModel.CHSH
    rw [hm 0 0, hm 0 1, hm 1 0, hm 1 1]
    exact singletQuantumCorrelation_CHSH_eq
  rw [hCHSH] at hbound
  have habs : |(-(2 * Real.sqrt 2) : ℝ)| = 2 * Real.sqrt 2 := by
    rw [abs_neg, abs_of_pos]
    exact two_sqrt_two_gt_two.trans_le' (by norm_num)
  rw [habs] at hbound
  linarith [two_sqrt_two_gt_two]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE ASYMMETRIC HEADLINE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE ASYMMETRIC HEADLINE.**

    The bipartite-qubit substrate of phase-quotient unitary QM:

      (1) HAS a Raymond-Robichaud local-realistic shadow
          (`bipartiteQubitUnitaryQM_has_localRealisticModel`,
          proved unconditionally modulo the standard five-postulate
          bundle).

      (2) DOES NOT HAVE a Bell-style local hidden variable shadow
          for the singlet's CHSH-attaining correlations
          (`singlet_has_no_LHV_shadow`).

    Philosophical content: **Bell's theorem refutes only the
    STRONGER LHV form of local realism, NOT Raymond-Robichaud's
    broader notion.**  The two forms are FORMALLY DISTINCT in Lean,
    and the bipartite-qubit substrate provides an explicit
    separating example: it admits the broader shadow but excludes
    the stronger one. -/
theorem bipartite_qubit_shadow_has_RR_but_not_LHV
    (hPost : BipartiteFullPostulates 2 2 bipartiteAnalyticCore_2_2) :
    (∃ L : LocalRealisticTheory,
        L.IsNoSignallingShadow bipartiteQubitUnitaryQuantumNoSignalling)
    ∧ ¬ HasLHVShadow singletQuantumCorrelation :=
  ⟨bipartiteQubitUnitaryQM_has_localRealisticModel hPost,
   singlet_has_no_LHV_shadow⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms LHVModel.CHSH_le_two
#print axioms singletQuantumCorrelation_CHSH_eq
#print axioms singlet_has_no_LHV_shadow
#print axioms bipartite_qubit_shadow_has_RR_but_not_LHV

end UnifiedTheory.LayerC.LHVvsRR
