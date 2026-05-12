/-
  LayerB/Phase_E3_KP6_Unconditional_FreeCase.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — KP6 (FREE CASE): UNCONDITIONAL DISCHARGE OF
              THE MULTI-LINK HAAR TRUNCATION CONSISTENCY HYPOTHESIS,
              YIELDING UNCONDITIONAL FREE-CASE PROJECTIVE
              CONSISTENCY OF THE INTERACTING WILSON FAMILY AT β = 0.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict: `KP6_FREE_CASE_UNCONDITIONAL_PROVED`.

    `Phase_E3_KP6.lean` proves
    `interactingWilsonProjectiveConsistency_at_zero` CONDITIONAL on
    the Mathlib-level hypothesis `MultiLinkHaarTruncateConsistency`
    that pushing the multi-link product Haar measure forward along
    the truncation map `truncate : (Fin L₂ → G_SO10) → (Fin L₁ → G_SO10)`
    yields the smaller product Haar measure.

    This file DISCHARGES that hypothesis UNCONDITIONALLY using
    Mathlib's `Measure.pi_eq` characterization of the product measure,
    by showing that the pushforward agrees with `Measure.pi` on
    every cylinder set `Set.univ.pi s`, since:

      (1) The truncate map sends a cylinder `Set.univ.pi s` (with
          `s : Fin L₁ → Set G_SO10`) to the cylinder
          `Set.univ.pi t` on the L₂-side, where
              t j = s ⟨j.val, _⟩ if j.val < L₁
              t j = Set.univ          if j.val ≥ L₁.

      (2) `Measure.pi_pi` evaluates the L₂-product on
          `Set.univ.pi t` as `∏ j : Fin L₂, haarMeasureSO10 (t j)`.

      (3) For j with j.val ≥ L₁ the factor `haarMeasureSO10 Set.univ
          = 1` (since `haarMeasureSO10` is a probability measure).

      (4) The remaining product over j with j.val < L₁ matches
          `∏ i : Fin L₁, haarMeasureSO10 (s i)` via the canonical
          bijection `Fin L₁ ≃ {j : Fin L₂ // j.val < L₁}`.

    Consequence:
      `interactingWilsonProjectiveConsistency_at_zero_unconditional`
    holds for every `WilsonActionAssignment S`, with NO hypothesis
    beyond Mathlib's `Measure.pi`-API.

  WHAT THIS FILE PROVES UNCONDITIONALLY.

    (1) `multiLinkHaar_truncate_pushforward_eq` —
        `(multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁`,
        proved from `Measure.pi_eq` and `Measure.pi_pi`.

    (2) `multiLinkHaarTruncateConsistency_proved` —
        the bundled `MultiLinkHaarTruncateConsistency` hypothesis
        is discharged.

    (3) `interactingWilsonProjectiveConsistency_at_zero_unconditional` —
        the free-case projective consistency theorem with NO
        external hypothesis.

    (4) `phase_E3_KP6_unconditional_freecase_master` —
        bundled master theorem.

    (5) `verdict_E3_KP6_unconditional_freecase_check` —
        verdict = `KP6_FREE_CASE_UNCONDITIONAL_PROVED`.

  WHAT THIS FILE DOES NOT PROVE.

    (X1) The interacting case `β > 0` projective consistency.
         This remains conditional on `WilsonActionConsistency β S`
         (the DLR-style action factorization), which is the
         Glimm-Jaffe open question.  See parent file `Phase_E3_KP6`.

  Zero `sorry`.  Zero custom `axiom`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  REFERENCES.

    [Mathlib]  `Mathlib.MeasureTheory.Constructions.Pi`:
                 `Measure.pi`, `Measure.pi_eq`, `Measure.pi_pi`.
    [Mathlib]  `Mathlib.MeasureTheory.Constructions.Projective`:
                 `IsProjectiveMeasureFamily`, `IsProjectiveLimit`.
    [GJ87]     J. Glimm, A. Jaffe.  Quantum Physics, Springer 1987.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_E3_KP6

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.docString false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.LayerB.Phase_E3_KP6_Unconditional_FreeCase

open MeasureTheory MeasureTheory.Measure ENNReal
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_E3_KP6

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  CYLINDER-SET PREIMAGE UNDER TRUNCATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The truncate map `truncate h : (Fin L₂ → G_SO10) → (Fin L₁ → G_SO10)`
    sends a cylinder `Set.univ.pi s` (over `Fin L₁`) to a cylinder
    `Set.univ.pi (truncatedSet h s)` (over `Fin L₂`), where the
    "extension" is `Set.univ` on the L₂-only complement. -/

/-- The extension of an `s : Fin L₁ → Set G_SO10` to
    `truncatedSet h s : Fin L₂ → Set G_SO10`, used to describe the
    preimage of the canonical cylinder `Set.univ.pi s` under the
    truncation map. -/
noncomputable def truncatedSet {L₁ L₂ : ℕ} (h : L₁ ≤ L₂)
    (s : Fin L₁ → Set G_SO10) : Fin L₂ → Set G_SO10 :=
  fun j => if hj : j.val < L₁ then s ⟨j.val, hj⟩ else Set.univ

/-- The preimage of a cylinder set under `truncate h` is itself a
    cylinder set, with the L₂-only indices filled by `Set.univ`. -/
theorem truncate_preimage_pi {L₁ L₂ : ℕ} (h : L₁ ≤ L₂)
    (s : Fin L₁ → Set G_SO10) :
    (truncate h) ⁻¹' (Set.univ.pi s) = Set.univ.pi (truncatedSet h s) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hω j
    by_cases hj : j.val < L₁
    · -- in this case the truncatedSet is `s ⟨j.val, hj⟩`
      simp only [truncatedSet, dif_pos hj]
      -- Need: ω j ∈ s ⟨j.val, hj⟩.
      -- We have: ∀ i : Fin L₁, truncate h ω i ∈ s i.
      -- So at i := ⟨j.val, hj⟩, truncate h ω ⟨j.val, hj⟩ ∈ s ⟨j.val, hj⟩.
      have := hω ⟨j.val, hj⟩
      simp only [truncate] at this
      convert this
    · -- in this case the truncatedSet is Set.univ
      simp only [truncatedSet, dif_neg hj]
      exact Set.mem_univ _
  · intro hω i
    -- Need: truncate h ω i ∈ s i.
    -- We have: ∀ j : Fin L₂, ω j ∈ truncatedSet h s j.
    -- At j := ⟨i.val, lt_of_lt_of_le i.isLt h⟩, j.val < L₁ holds, and
    -- truncatedSet h s j = s ⟨i.val, ...⟩ = s i.
    have hj : (⟨i.val, lt_of_lt_of_le i.isLt h⟩ : Fin L₂).val < L₁ := i.isLt
    have := hω ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    simp only [truncatedSet, dif_pos hj] at this
    -- this : ω ⟨i.val, _⟩ ∈ s ⟨i.val, _⟩
    -- goal:  truncate h ω i ∈ s i
    -- but truncate h ω i = ω ⟨i.val, _⟩ by definition,
    -- and ⟨i.val, _⟩ = i because Fin is determined by the value.
    simp only [truncate]
    have hcoe : (⟨i.val, hj⟩ : Fin L₁) = i := Fin.ext rfl
    rw [hcoe] at this
    exact this

/-- Each `truncatedSet h s j` is a measurable set when each `s i` is. -/
theorem truncatedSet_measurable {L₁ L₂ : ℕ} (h : L₁ ≤ L₂)
    {s : Fin L₁ → Set G_SO10} (hs : ∀ i, MeasurableSet (s i))
    (j : Fin L₂) : MeasurableSet (truncatedSet h s j) := by
  unfold truncatedSet
  by_cases hj : j.val < L₁
  · rw [dif_pos hj]; exact hs ⟨j.val, hj⟩
  · rw [dif_neg hj]; exact MeasurableSet.univ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE PRODUCT IDENTITY ON THE EXTENDED SET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The L₂-product of the Haar-measures of `truncatedSet h s j`
    collapses to the L₁-product of the Haar-measures of `s i`,
    because the L₂-only factors give `haarMeasureSO10 Set.univ = 1`. -/

/-- The product over `Fin L₂` of the Haar-measures of `truncatedSet
    h s j` equals the product over `Fin L₁` of the Haar-measures
    of `s i`. -/
theorem prod_truncatedSet_eq {L₁ L₂ : ℕ} (h : L₁ ≤ L₂)
    (s : Fin L₁ → Set G_SO10) :
    (∏ j : Fin L₂, haarMeasureSO10 (truncatedSet h s j)) =
      ∏ i : Fin L₁, haarMeasureSO10 (s i) := by
  -- Split the L₂-product into the {j : j.val < L₁} part (which
  -- matches the L₁-product) and the {j : ¬ j.val < L₁} part (which
  -- contributes 1 each since each factor is `Set.univ`).
  classical
  -- Use Finset.prod_attach to identify Fin L₁ with the subtype.
  have h_split :
      (∏ j : Fin L₂, haarMeasureSO10 (truncatedSet h s j)) =
        (∏ j ∈ (Finset.univ : Finset (Fin L₂)).filter (fun j => j.val < L₁),
            haarMeasureSO10 (truncatedSet h s j)) *
        (∏ j ∈ (Finset.univ : Finset (Fin L₂)).filter (fun j => ¬ j.val < L₁),
            haarMeasureSO10 (truncatedSet h s j)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin L₂))
          (fun j => j.val < L₁)]
  rw [h_split]
  -- The second product is 1: each factor is `haarMeasureSO10 Set.univ = 1`.
  have h_second :
      (∏ j ∈ (Finset.univ : Finset (Fin L₂)).filter (fun j => ¬ j.val < L₁),
          haarMeasureSO10 (truncatedSet h s j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨_, hj_neg⟩ := hj
    simp only [truncatedSet, dif_neg hj_neg]
    exact MeasureTheory.measure_univ
  rw [h_second, mul_one]
  -- Now identify the first product with the L₁-product via the
  -- bijection Fin L₁ ≃ {j : Fin L₂ // j.val < L₁}.
  -- Use the embedding e : Fin L₁ → Fin L₂, e i = ⟨i.val, lt_of_lt_of_le i.isLt h⟩.
  let e : Fin L₁ ↪ Fin L₂ :=
    ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩, by
      intro i₁ i₂ heq
      apply Fin.ext
      exact Fin.mk.inj_iff.mp heq⟩
  have h_image :
      (Finset.univ : Finset (Fin L₂)).filter (fun j => j.val < L₁) =
        (Finset.univ : Finset (Fin L₁)).map e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Function.Embedding.coeFn_mk, e]
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [h_image]
  rw [Finset.prod_map]
  -- Now both sides are ∏ i : Fin L₁, haarMeasureSO10 of something.
  apply Finset.prod_congr rfl
  intro i _
  -- Need: haarMeasureSO10 (truncatedSet h s (e i)) = haarMeasureSO10 (s i)
  simp only [Function.Embedding.coeFn_mk, e]
  have hi : (⟨i.val, lt_of_lt_of_le i.isLt h⟩ : Fin L₂).val < L₁ := i.isLt
  simp only [truncatedSet, dif_pos hi]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  THE PUSHFORWARD IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE MAIN LEMMA.**  Pushing `multiLinkHaar L₂` forward along
    `truncate h` recovers `multiLinkHaar L₁`, by direct application
    of `Measure.pi_eq` to the cylinder-set characterization. -/
theorem multiLinkHaar_truncate_pushforward_eq
    {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁ := by
  unfold multiLinkHaar
  -- Apply `pi_eq` to characterize the LHS as `Measure.pi`-product.
  refine (Measure.pi_eq ?_).symm
  intro s hs
  -- LHS:  ((Measure.pi (fun _ => haarMeasureSO10)).map (truncate h)) (Set.univ.pi s)
  rw [Measure.map_apply (truncate_measurable h) (MeasurableSet.univ_pi hs)]
  -- Compute the preimage as a cylinder.
  rw [truncate_preimage_pi h s]
  -- Apply `Measure.pi_pi`.
  rw [Measure.pi_pi]
  -- Reduce to the product identity.
  exact prod_truncatedSet_eq h s

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  DISCHARGE OF THE HAAR-CONSISTENCY HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **DISCHARGE.**  The KP6 `MultiLinkHaarTruncateConsistency`
    hypothesis is unconditional. -/
theorem multiLinkHaarTruncateConsistency_proved :
    MultiLinkHaarTruncateConsistency := by
  intro L₁ L₂ h
  exact multiLinkHaar_truncate_pushforward_eq h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE UNCONDITIONAL FREE-CASE PROJECTIVE CONSISTENCY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE UNCONDITIONAL FREE-CASE THEOREM.**  At β = 0, the family
    of finite-`L` interacting Wilson measures is projectively
    consistent for every Wilson action assignment.  Discharged by
    chaining `interactingWilsonMeasure_L_at_zero_eq_haar` (the free-
    case collapse to multi-link Haar) with the unconditional
    `multiLinkHaar_truncate_pushforward_eq`. -/
theorem interactingWilsonProjectiveConsistency_at_zero_unconditional
    (S : WilsonActionAssignment) :
    InteractingWilsonProjectiveConsistency 0 S :=
  interactingWilsonProjectiveConsistency_at_zero S
    multiLinkHaarTruncateConsistency_proved

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Verdict enum for the unconditional free-case discharge. -/
inductive PhaseE3KP6UnconditionalFreeCaseVerdict
  /-- The free-case (β = 0) is unconditionally proved by direct
      application of Mathlib's `Measure.pi`-API, with no remaining
      hypothesis on the multi-link Haar truncation consistency. -/
  | KP6_FREE_CASE_UNCONDITIONAL_PROVED
  /-- A specific Mathlib lemma was missing and the discharge
      could not be completed.  (Not the case here.) -/
  | KP6_FREE_CASE_BLOCKED_BY_MATHLIB_GAP
  deriving DecidableEq, Repr

/-- THE PHASE E3 KP6 UNCONDITIONAL FREE-CASE VERDICT. -/
def verdict_E3_KP6_unconditional_freecase :
    PhaseE3KP6UnconditionalFreeCaseVerdict :=
  .KP6_FREE_CASE_UNCONDITIONAL_PROVED

/-- Self-check on the verdict. -/
theorem verdict_E3_KP6_unconditional_freecase_check :
    verdict_E3_KP6_unconditional_freecase =
      PhaseE3KP6UnconditionalFreeCaseVerdict.KP6_FREE_CASE_UNCONDITIONAL_PROVED :=
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM: PHASE E3 — KP6 UNCONDITIONAL FREE CASE.**

    Bundles the unconditional content of this file:

    (1) `multiLinkHaar_truncate_pushforward_eq` —
        the pushforward identity for the multi-link Haar measure
        under truncation.

    (2) `multiLinkHaarTruncateConsistency_proved` —
        the bundled Haar-side hypothesis is discharged.

    (3) `interactingWilsonProjectiveConsistency_at_zero_unconditional`
        —  the free-case projective consistency theorem holds for
        every `WilsonActionAssignment S`, with NO external hypothesis.

    (4) The verdict is `KP6_FREE_CASE_UNCONDITIONAL_PROVED`. -/
theorem phase_E3_KP6_unconditional_freecase_master :
    -- (1)  Pushforward identity.
    (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) ∧
    -- (2)  Bundled consistency.
    MultiLinkHaarTruncateConsistency ∧
    -- (3)  Unconditional free-case projective consistency.
    (∀ (S : WilsonActionAssignment),
      InteractingWilsonProjectiveConsistency 0 S) ∧
    -- (4)  Verdict.
    (verdict_E3_KP6_unconditional_freecase =
      PhaseE3KP6UnconditionalFreeCaseVerdict.KP6_FREE_CASE_UNCONDITIONAL_PROVED) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L₁ L₂ h
    exact multiLinkHaar_truncate_pushforward_eq h
  · exact multiLinkHaarTruncateConsistency_proved
  · intro S
    exact interactingWilsonProjectiveConsistency_at_zero_unconditional S
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE STATEMENT.**

    What this file PROVES (UNCONDITIONALLY, in real content):

      ✓ `multiLinkHaar_truncate_pushforward_eq` —
        `(multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁`,
        for all `L₁ ≤ L₂`, by direct application of `Measure.pi_eq`
        and `Measure.pi_pi`.

      ✓ `multiLinkHaarTruncateConsistency_proved` —
        the KP6 hypothesis `MultiLinkHaarTruncateConsistency` is
        discharged unconditionally.

      ✓ `interactingWilsonProjectiveConsistency_at_zero_unconditional` —
        for every `WilsonActionAssignment S`, the family
        `L ↦ interactingWilsonMeasure_L 0 L (S L)` is projectively
        consistent, with NO external hypothesis.

      ✓ `phase_E3_KP6_unconditional_freecase_master` — bundle.

    What this file does NOT prove (deliberately, out of scope):

      ✗ `WilsonActionConsistency β S` for `β > 0` and the canonical
        Wilson plaquette action.  This is the DLR-style action
        factorization, which remains the open Glimm-Jaffe question.
        See `Phase_E3_KP6.lean` for the conditional bridge theorem
        `KP_to_InteractingWilsonConsistency`.

    HONEST CLAIM.  At β = 0 the free-case projective consistency
    of the interacting Wilson family follows UNCONDITIONALLY from
    Mathlib's `Measure.pi`-API.  No remaining hypothesis on the
    Haar-side truncation behaviour is needed.

    Verdict: `KP6_FREE_CASE_UNCONDITIONAL_PROVED`. -/
theorem honest_phase_E3_KP6_unconditional_freecase_scope_statement :
    -- PROVED unconditionally:  pushforward identity.
    (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) ∧
    -- PROVED unconditionally:  bundled consistency.
    MultiLinkHaarTruncateConsistency ∧
    -- PROVED unconditionally:  free-case projective consistency.
    (∀ (S : WilsonActionAssignment),
      InteractingWilsonProjectiveConsistency 0 S) ∧
    -- HONEST:  verdict.
    (verdict_E3_KP6_unconditional_freecase =
      PhaseE3KP6UnconditionalFreeCaseVerdict.KP6_FREE_CASE_UNCONDITIONAL_PROVED) :=
  phase_E3_KP6_unconditional_freecase_master

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  TYPE-LEVEL SANITY CHECKS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- The pushforward identity is a Prop.
example {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) : Prop :=
  (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁

-- The discharged consistency is a Prop.
example : Prop := MultiLinkHaarTruncateConsistency

-- The unconditional free-case theorem has the right shape.
example (S : WilsonActionAssignment) :
    InteractingWilsonProjectiveConsistency 0 S :=
  interactingWilsonProjectiveConsistency_at_zero_unconditional S

-- The verdict is a definite enum value.
example : verdict_E3_KP6_unconditional_freecase =
    PhaseE3KP6UnconditionalFreeCaseVerdict.KP6_FREE_CASE_UNCONDITIONAL_PROVED := rfl

end UnifiedTheory.LayerB.Phase_E3_KP6_Unconditional_FreeCase
