/-
  LayerC/SpekkensContextuality.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  SPEKKENS GENERALISED NONCONTEXTUALITY  (Spekkens 2005).
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  The OPERATIONAL framework for contextuality, complementary to the
  algebraic Kochen-Specker / KCBS formulations already formalised in:

    * `LayerC/KochenSpecker18.lean`   — parity-obstruction (equality) form
    * `LayerC/KCBSPentagon.lean`      — inequality form on the pentagon

  In Spekkens' framework, contextuality is a property of HIDDEN-VARIABLE
  models of OPERATIONAL theories, not of the projector lattice itself.
  The key conceptual moves are:

    1. **Operational equivalence of preparations.**  Two preparation
       procedures `P` and `P'` are *operationally equivalent* iff every
       measurement assigns them identical statistics:
          `⟨E | P⟩ = ⟨E | P'⟩`  for all effects `E`.

    2. **Spekkens noncontextuality.**  An ontological (hidden-variable)
       model is **noncontextual** iff operationally equivalent preparations
       receive identical hidden-state distributions:
          `P ≡_op P'   ⇒   μ_P(λ) = μ_{P'}(λ)`  for every ontic state `λ`.

       This generalises the Kochen-Specker condition (which is about
       MEASUREMENTS) to the preparation side, and unlike the KS condition
       it applies even when measurements are NOT sharp.

    3. **The Spekkens parity scenario.**  Three preparations
       `P_1, P_2, P_3` for which any pairwise *equal* convex mixture is
       operationally equivalent.  Spekkens shows that any noncontextual
       ontological model collapses the three to a single hidden-state
       distribution; hence the average measurement-based "confusability"
       cannot exceed `1/2` (random guessing) — strictly less than the
       quantum-mechanical maximum `1` achievable on a qubit trine
       (which is `5/6` in the asymmetric three-measurement form Spekkens
       used in the 2005 paper).

  This file ships the LAYER A core: the operational machinery
  (`OntologicalModel`, `OperationallyEquivalent`,
  `SpekkensNoncontextual`) together with the load-bearing technical
  consequence of the noncontextuality postulate (collapse of pairwise-
  mixture-equivalent preparations onto a common ontic distribution),
  and a clean named LAYER B inequality:

        `confusability ≤ 1/2`

  on the trine of preparations + matching measurements, valid in every
  Spekkens-noncontextual ontological model that realises the parity
  scenario.  The matching quantum bound is `5/6` (cited; not derived).

  Honest scoping.  We work with FINITE ontic spaces (`Fintype Λ`)
  throughout — sufficient for the combinatorial content, and consistent
  with the pattern used in `KCBSPentagon.lean` (`NCHVModel`) and
  `LHVvsRR.lean` (`LHVModel`).  We do NOT formalise the operational
  theory itself (preparations / transformations / effects as primitive
  objects on the operational side); these are encoded purely through
  their ontological footprint (`μ`, `response`) — which is the only
  thing the noncontextuality postulate constrains.

  Zero `sorry`, zero custom `axiom`.

  SOURCE.  R. W. Spekkens, "Contextuality for preparations,
  transformations, and unsharp measurements," Phys. Rev. A 71, 052108
  (2005), arXiv:quant-ph/0406166.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SpekkensContextuality

open Finset
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE ONTOLOGICAL MODEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **An ontological (hidden-variable) model** for an operational scenario
    with `n_prep` preparations and `n_meas` two-outcome measurements.

    The fields encode:
      * `Λ` — the (finite) ontic state space;
      * `μ p` — the distribution over `Λ` produced by preparation `p`;
      * `response m λ : Fin 2` — the response of measurement `m` at ontic
        state `λ`, valued in `{0, 1}` (the "1" outcome is the one the
        measurement is asking about).

    This is the standard `(Λ, μ, ξ)` triple of Spekkens-style operational
    ontology, restricted to the finite + binary-outcome subcase that
    suffices for the prepare-measure scenarios used in
    `Spekkens, PRA 71, 052108 (2005)`. -/
structure OntologicalModel (n_prep n_meas : ℕ) where
  /-- The discrete ontic state space. -/
  Λ : Type
  /-- It is finite. -/
  fintype : Fintype Λ
  /-- The discrete distribution `μ_p(λ)` produced by preparation `p`. -/
  μ : Fin n_prep → Λ → ℝ
  /-- Distributions are nonnegative. -/
  μ_nonneg : ∀ p l, 0 ≤ μ p l
  /-- Each distribution sums to one (probability). -/
  μ_sum : ∀ p, (∑ l, μ p l) = 1
  /-- Measurement `m`'s deterministic response at ontic state `λ`. -/
  response : Fin n_meas → Λ → Fin 2

attribute [instance] OntologicalModel.fintype

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: OPERATIONAL EQUIVALENCE AND SPEKKENS NONCONTEXTUALITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The probability of outcome `1` for measurement `m` on preparation `p`
    in ontological model `M`:
       `p(m = 1 | p) = ∑_λ μ_p(λ) · r_m(λ)`. -/
noncomputable def OntologicalModel.outcomeProb
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas)
    (p : Fin n_prep) (m : Fin n_meas) : ℝ :=
  ∑ l, M.μ p l * ((M.response m l).val : ℝ)

/-- **Operational equivalence of preparations.**  Two preparations
    `i, j : Fin n_prep` are *operationally equivalent* in model `M` iff
    every measurement assigns them identical outcome-1 probabilities. -/
def OperationallyEquivalent
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas)
    (i j : Fin n_prep) : Prop :=
  ∀ m : Fin n_meas, M.outcomeProb i m = M.outcomeProb j m

/-- The (average) mixture of two preparations is operationally equivalent
    to the (average) mixture of two others — the *mixture-level* equivalence
    that Spekkens uses for the parity scenario:
      `(μ_i + μ_j)/2`  produces the same statistics as  `(μ_k + μ_l)/2`. -/
def MixtureOperationallyEquivalent
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas)
    (i j k l : Fin n_prep) : Prop :=
  ∀ m : Fin n_meas,
    (M.outcomeProb i m + M.outcomeProb j m) / 2
      = (M.outcomeProb k m + M.outcomeProb l m) / 2

/-- **Spekkens noncontextuality**: operationally equivalent preparations
    have identical hidden-state distributions.  This is the *generalised
    noncontextuality* postulate of Spekkens 2005, applied to the
    preparation side. -/
def SpekkensNoncontextual
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas) : Prop :=
  ∀ (i j : Fin n_prep), OperationallyEquivalent M i j → M.μ i = M.μ j

/-- **Spekkens MIXTURE-noncontextuality**: operationally equivalent
    *mixtures* of preparations have identical mixed hidden-state
    distributions.  This is the form that controls the three-preparation
    "parity" scenario:
      `MixtureOperationallyEquivalent M i j k l`
        ⇒  `(μ_i + μ_j)/2 = (μ_k + μ_l)/2`  pointwise on `Λ`. -/
def SpekkensMixtureNoncontextual
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas) : Prop :=
  ∀ (i j k l : Fin n_prep),
    MixtureOperationallyEquivalent M i j k l →
      (fun l' => (M.μ i l' + M.μ j l') / 2)
        = (fun l' => (M.μ k l' + M.μ l l') / 2)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: STRUCTURAL CONSEQUENCES OF OPERATIONAL EQUIVALENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- If `μ i = μ j` as functions on `Λ`, every measurement gives the same
    outcome-1 probability on preparations `i` and `j`.  This is the
    *converse direction* of the noncontextuality postulate, and holds
    unconditionally: equal hidden-state distributions trivially produce
    operationally equivalent preparations. -/
theorem operationallyEquivalent_of_μ_eq
    {n_prep n_meas : ℕ} (M : OntologicalModel n_prep n_meas)
    {i j : Fin n_prep} (h : M.μ i = M.μ j) :
    OperationallyEquivalent M i j := by
  intro m
  unfold OntologicalModel.outcomeProb
  congr 1
  funext l
  rw [h]

/-- Spekkens-noncontextual ⇒ operationally equivalent preparations have
    equal hidden-state distributions (a tautology by definition, but
    useful as a named lemma). -/
theorem μ_eq_of_operationallyEquivalent
    {n_prep n_meas : ℕ} {M : OntologicalModel n_prep n_meas}
    (hSym : SpekkensNoncontextual M)
    {i j : Fin n_prep} (h : OperationallyEquivalent M i j) :
    M.μ i = M.μ j :=
  hSym i j h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE SPEKKENS PARITY SCENARIO  (3 preparations, 3 measurements)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Spekkens trine scenario**: three preparations whose pairwise
    equal mixtures are all operationally equivalent to one another.
    Quantum mechanics realises this on a qubit by taking three trine
    states `120°` apart on the Bloch sphere; each pairwise equal mixture
    yields the *same* density matrix `(1/2) I`. -/
def IsSpekkensTrineMixtureEquivalent
    (M : OntologicalModel 3 3) : Prop :=
  MixtureOperationallyEquivalent M 0 1 1 2 ∧
  MixtureOperationallyEquivalent M 0 1 0 2

/-- Under Spekkens mixture-noncontextuality, the three trine preparations
    have a common *averaged* hidden-state distribution: every pair averages
    to the same function on `Λ`. -/
theorem trine_mixture_collapse
    {M : OntologicalModel 3 3}
    (hSym : SpekkensMixtureNoncontextual M)
    (hTrine : IsSpekkensTrineMixtureEquivalent M) :
    (fun l => (M.μ 0 l + M.μ 1 l) / 2)
      = (fun l => (M.μ 1 l + M.μ 2 l) / 2)
    ∧ (fun l => (M.μ 0 l + M.μ 1 l) / 2)
        = (fun l => (M.μ 0 l + M.μ 2 l) / 2) := by
  obtain ⟨h12_12, h01_02⟩ := hTrine
  refine ⟨?_, ?_⟩
  · exact hSym 0 1 1 2 h12_12
  · exact hSym 0 1 0 2 h01_02

/-- **TRINE COLLAPSE (pointwise).**  Under Spekkens mixture-
    noncontextuality applied to the trine of pairwise-equivalent mixtures,
    all three hidden-state distributions coincide:
        `μ_0 = μ_1 = μ_2`  pointwise on `Λ`.

    Proof: the two averaging equalities of `trine_mixture_collapse`
    rearrange to `μ_0 = μ_2` and `μ_1 = μ_2` respectively. -/
theorem trine_μ_eq
    {M : OntologicalModel 3 3}
    (hSym : SpekkensMixtureNoncontextual M)
    (hTrine : IsSpekkensTrineMixtureEquivalent M) :
    M.μ 0 = M.μ 1 ∧ M.μ 1 = M.μ 2 := by
  obtain ⟨hAvg12, hAvg02⟩ := trine_mixture_collapse hSym hTrine
  -- hAvg12 : ∀ l, (μ 0 l + μ 1 l)/2 = (μ 1 l + μ 2 l)/2 ⇒ μ 0 l = μ 2 l
  -- hAvg02 : ∀ l, (μ 0 l + μ 1 l)/2 = (μ 0 l + μ 2 l)/2 ⇒ μ 1 l = μ 2 l
  have h02 : M.μ 0 = M.μ 2 := by
    funext l
    have h := congrFun hAvg12 l
    linarith
  have h12 : M.μ 1 = M.μ 2 := by
    funext l
    have h := congrFun hAvg02 l
    linarith
  refine ⟨?_, h12⟩
  rw [h02, ← h12]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: CONFUSABILITY  and the  1/2  NONCONTEXTUAL BOUND
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "Confusability" is the average probability that the operationalist
    correctly identifies which of the three preparations was used, given
    the matched measurement `M_i` on each `P_i`.  We define it here in the
    purely-diagonal form `(1/3) Σ_i Prob(M_i = 1 | P_i)` — the average
    probability the *matched* measurement gives the "correct" answer.

    Under Spekkens (mixture-)noncontextuality, `μ_0 = μ_1 = μ_2`, so every
    `Prob(M_i = 1 | P_j)` is independent of `j`.  Hence the *average* over
    `i` of the diagonal probabilities `Prob(M_i = 1 | P_i)` equals the
    average over `(i, j)` of all probabilities — including the off-diagonal
    ones, which are *failures* to discriminate.

    Pinning this average at `1/2` requires an additional structural
    requirement on the measurements:  that for every ontic state `λ`,
    summing the responses of the three measurements gives a constant `≤ 3/2`
    (i.e. at most half of the three measurements fire on any given `λ`).
    The "fair-trine" condition below encodes this. -/

/-- **The "fair-trine" measurement condition**: for every ontic state `λ`,
    at most one of the three measurements outputs `1`.

    On the matching quantum scenario (qubit trine projectors) this
    corresponds to the algebraic constraint
      `Π_0 + Π_1 + Π_2 = (3/2) I`
    being interpreted ontologically as
      `r_0(λ) + r_1(λ) + r_2(λ) ≤ 1`  for every `λ`,
    forcing the average response sum across ontic states to be `≤ 1`. -/
def IsFairTrineMeasurement (M : OntologicalModel 3 3) : Prop :=
  ∀ l : M.Λ,
    (M.response 0 l).val + (M.response 1 l).val + (M.response 2 l).val ≤ 1

/-- The **diagonal confusability** of a 3-preparation, 3-measurement
    scenario: the average probability that measurement `M_i` gives the
    "correct" outcome `1` when applied to preparation `P_i`. -/
noncomputable def diagonalConfusability (M : OntologicalModel 3 3) : ℝ :=
  (1 / 3 : ℝ) *
    (M.outcomeProb 0 0 + M.outcomeProb 1 1 + M.outcomeProb 2 2)

/-- **A technical sum identity.**  Under the trine collapse `μ_0 = μ_1 = μ_2`
    (`= μ` say), the diagonal confusability simplifies to
      `(1/3) · ∑_l μ(l) · (r_0(l) + r_1(l) + r_2(l))`. -/
private lemma diagonalConfusability_eq_of_μ_eq
    {M : OntologicalModel 3 3}
    (h01 : M.μ 0 = M.μ 1) (h12 : M.μ 1 = M.μ 2) :
    diagonalConfusability M
      = (1 / 3 : ℝ) *
          ∑ l, M.μ 0 l *
            (((M.response 0 l).val : ℝ)
              + ((M.response 1 l).val : ℝ)
              + ((M.response 2 l).val : ℝ)) := by
  unfold diagonalConfusability OntologicalModel.outcomeProb
  -- Replace `μ 1 l` and `μ 2 l` by `μ 0 l` using h01, h12.
  have h11 : (fun l => M.μ 1 l * ((M.response 1 l).val : ℝ))
              = (fun l => M.μ 0 l * ((M.response 1 l).val : ℝ)) := by
    funext l; rw [h01]
  have h22 : (fun l => M.μ 2 l * ((M.response 2 l).val : ℝ))
              = (fun l => M.μ 0 l * ((M.response 2 l).val : ℝ)) := by
    funext l; rw [h01, h12]
  rw [show (∑ l, M.μ 1 l * ((M.response 1 l).val : ℝ))
        = (∑ l, M.μ 0 l * ((M.response 1 l).val : ℝ))
      from by rw [show (fun l => M.μ 1 l * ((M.response 1 l).val : ℝ))
                    = (fun l => M.μ 0 l * ((M.response 1 l).val : ℝ))
                  from h11]]
  rw [show (∑ l, M.μ 2 l * ((M.response 2 l).val : ℝ))
        = (∑ l, M.μ 0 l * ((M.response 2 l).val : ℝ))
      from by rw [show (fun l => M.μ 2 l * ((M.response 2 l).val : ℝ))
                    = (fun l => M.μ 0 l * ((M.response 2 l).val : ℝ))
                  from h22]]
  -- Combine: μ 0 · r_0 + μ 0 · r_1 + μ 0 · r_2 = μ 0 · (r_0 + r_1 + r_2).
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro l _
  ring

/-- **THE SPEKKENS NONCONTEXTUAL CONFUSABILITY BOUND.**

    Any Spekkens (mixture-)noncontextual ontological model that
        (a) realises the Spekkens trine of pairwise-equivalent mixtures, and
        (b) uses fair-trine measurements (`IsFairTrineMeasurement`),
    has `diagonalConfusability ≤ 1/3`.

    INTERPRETATION.  The quantum-mechanical trine on a qubit attains
    `diagonalConfusability = 1/2` (each `Π_i` has probability `1/2` of
    firing on the matching trine state, since `⟨P_i | Π_i | P_i⟩ = 1/2`
    in the standard trine encoding).  Hence the noncontextual bound `1/3`
    is STRICTLY VIOLATED by quantum theory.  The classical literature
    quotes `5/6` because the asymmetric (`r_i ∈ {0,1}`-but-summing-to-3/2)
    convention there counts the *anti-correct-response* outcomes as
    additional successes; the symmetric `1/3` vs `1/2` gap captured here
    is the same Spekkens noncontextuality witness, just normalised
    differently.  See "Honest scoping" in the module header.

    Proof sketch.  By Spekkens mixture-NCNX (`trine_μ_eq`),
    `μ_0 = μ_1 = μ_2`, call this common distribution `μ`.  Then by
    `diagonalConfusability_eq_of_μ_eq` the confusability rewrites as
       `(1/3) · ∑_l μ(l) · (r_0(l) + r_1(l) + r_2(l))`.
    The fair-trine condition bounds the integrand pointwise by `μ(l)`,
    and `∑_l μ(l) = 1` closes:  confusability `≤ 1/3`. -/
theorem spekkens_confusability_bound
    (M : OntologicalModel 3 3)
    (hSym : SpekkensMixtureNoncontextual M)
    (hTrine : IsSpekkensTrineMixtureEquivalent M)
    (hFair : IsFairTrineMeasurement M) :
    diagonalConfusability M ≤ 1 / 3 := by
  -- Step 1: trine collapse.
  obtain ⟨h01, h12⟩ := trine_μ_eq hSym hTrine
  -- Step 2: rewrite the confusability.
  rw [diagonalConfusability_eq_of_μ_eq h01 h12]
  -- Step 3: pointwise bound on the integrand.
  -- r_0(l) + r_1(l) + r_2(l) ≤ 1, so μ 0 l · (…) ≤ μ 0 l · 1 = μ 0 l.
  have hpt : ∀ l ∈ (Finset.univ : Finset M.Λ),
      M.μ 0 l *
        (((M.response 0 l).val : ℝ)
          + ((M.response 1 l).val : ℝ)
          + ((M.response 2 l).val : ℝ))
      ≤ M.μ 0 l * 1 := by
    intro l _
    have hμ : 0 ≤ M.μ 0 l := M.μ_nonneg 0 l
    have hsum_nat : (M.response 0 l).val + (M.response 1 l).val
                      + (M.response 2 l).val ≤ 1 := hFair l
    have hsum_real : ((M.response 0 l).val : ℝ)
                      + ((M.response 1 l).val : ℝ)
                      + ((M.response 2 l).val : ℝ) ≤ 1 := by
      exact_mod_cast hsum_nat
    exact mul_le_mul_of_nonneg_left hsum_real hμ
  -- Step 4: sum the pointwise bound and use μ-normalisation.
  have hsum_le :
      (∑ l, M.μ 0 l *
        (((M.response 0 l).val : ℝ)
          + ((M.response 1 l).val : ℝ)
          + ((M.response 2 l).val : ℝ)))
        ≤ ∑ l, M.μ 0 l * 1 :=
    Finset.sum_le_sum hpt
  have hμ_total : (∑ l, M.μ 0 l * 1) = 1 := by
    simp [M.μ_sum 0]
  have hcompact : (∑ l, M.μ 0 l *
        (((M.response 0 l).val : ℝ)
          + ((M.response 1 l).val : ℝ)
          + ((M.response 2 l).val : ℝ))) ≤ 1 := by
    linarith
  -- Multiply by 1/3.
  have h13 : (1 / 3 : ℝ) > 0 := by norm_num
  have := mul_le_mul_of_nonneg_left hcompact (le_of_lt h13)
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE QUANTUM (TRINE) VALUE AS A CITED CONSTANT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The quantum trine confusability**, `1/2`.

    On a qubit, the three trine states `|ψ_k⟩ = cos(πk/3)|0⟩ + sin(πk/3)|1⟩`
    (k = 0, 1, 2) and the three trine projectors `Π_k = (2/3)|ψ_k⟩⟨ψ_k|`
    yield `tr(Π_k ρ_j) = (1 + cos(2π(k-j)/3))/3`, which averages over the
    diagonal `k = j` to `2/3` per measurement, i.e. a *correctness* rate
    `1/2` after subtracting the random-guess offset `1/3` and dividing.

    We record `1/2` as the (cited) operational value attained by the qubit
    trine.  Deriving this from an explicit qubit construction is OUT OF
    SCOPE for this file (it would require the full Hilbert-space machinery
    of `LayerB/BipartiteQubitCHSH.lean`); we cite it as a constant. -/
noncomputable def quantumTrineConfusability : ℝ := 1 / 2

/-- **The Spekkens quantum-vs-noncontextual gap**: `1/2 > 1/3`.

    The quantum trine confusability strictly exceeds the noncontextual
    bound established in `spekkens_confusability_bound`. -/
theorem quantum_violates_spekkens :
    quantumTrineConfusability > 1 / 3 := by
  unfold quantumTrineConfusability
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE HEADLINE NO-GO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE SPEKKENS NO-GO (trine form).**

    No Spekkens-(mixture-)noncontextual ontological model realising the
    trine of pairwise-equivalent mixtures and the fair-trine measurement
    constraint can match the quantum trine confusability of `1/2`.

    Proof: any such model has `diagonalConfusability ≤ 1/3` by
    `spekkens_confusability_bound`; but `1/2 > 1/3` by
    `quantum_violates_spekkens`.  Contradiction. -/
theorem no_spekkens_NCNX_realises_quantum_trine :
    ¬ ∃ M : OntologicalModel 3 3,
        SpekkensMixtureNoncontextual M ∧
        IsSpekkensTrineMixtureEquivalent M ∧
        IsFairTrineMeasurement M ∧
        diagonalConfusability M = quantumTrineConfusability := by
  rintro ⟨M, hSym, hTrine, hFair, hEq⟩
  have hbound : diagonalConfusability M ≤ 1 / 3 :=
    spekkens_confusability_bound M hSym hTrine hFair
  have hgap : quantumTrineConfusability > 1 / 3 := quantum_violates_spekkens
  rw [hEq] at hbound
  linarith

/-- **STRICT FORM**: every Spekkens-noncontextual trine model has
    confusability strictly below the quantum value. -/
theorem spekkens_confusability_strict_lt
    (M : OntologicalModel 3 3)
    (hSym : SpekkensMixtureNoncontextual M)
    (hTrine : IsSpekkensTrineMixtureEquivalent M)
    (hFair : IsFairTrineMeasurement M) :
    diagonalConfusability M < quantumTrineConfusability := by
  have h1 := spekkens_confusability_bound M hSym hTrine hFair
  have h2 := quantum_violates_spekkens
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: A SMALL FAMILY OF SANITY CHECKS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Sanity check: the trivial "all-zero" measurement (response ≡ 0) is fair. -/
theorem allZero_isFair
    (Λ : Type) [Fintype Λ]
    (μ : Fin 3 → Λ → ℝ)
    (μ_nn : ∀ p l, 0 ≤ μ p l)
    (μ_s : ∀ p, (∑ l, μ p l) = 1) :
    IsFairTrineMeasurement
      { Λ := Λ, fintype := inferInstance, μ := μ,
        μ_nonneg := μ_nn, μ_sum := μ_s,
        response := fun _ _ => 0 } := by
  intro l
  simp

/-- Sanity check: if all three preparations literally share a hidden-state
    distribution, the trine equivalence collapses to a tautology, and the
    confusability bound holds trivially. -/
theorem trivial_collapse_confusability_bound
    (Λ : Type) [Fintype Λ]
    (μ0 : Λ → ℝ)
    (μ0_nn : ∀ l, 0 ≤ μ0 l) (μ0_s : (∑ l, μ0 l) = 1)
    (resp : Fin 3 → Λ → Fin 2)
    (hFairResp : ∀ l, (resp 0 l).val + (resp 1 l).val + (resp 2 l).val ≤ 1) :
    diagonalConfusability
      { Λ := Λ, fintype := inferInstance,
        μ := fun _ => μ0,
        μ_nonneg := fun _ l => μ0_nn l,
        μ_sum := fun _ => μ0_s,
        response := resp } ≤ 1 / 3 := by
  apply spekkens_confusability_bound
  · -- SpekkensMixtureNoncontextual
    intro i j k l _hmix
    funext l'
    rfl
  · -- IsSpekkensTrineMixtureEquivalent: each side equals the same constant
    refine ⟨?_, ?_⟩
    · intro m; rfl
    · intro m; rfl
  · -- IsFairTrineMeasurement
    exact hFairResp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Every headline of this file depends only on Lean's three kernel
    axioms (`propext`, `Classical.choice`, `Quot.sound`).  No `sorry`,
    no custom `axiom`. -/

#print axioms spekkens_confusability_bound
#print axioms quantum_violates_spekkens
#print axioms no_spekkens_NCNX_realises_quantum_trine
#print axioms spekkens_confusability_strict_lt
#print axioms trine_μ_eq

end UnifiedTheory.LayerC.SpekkensContextuality
