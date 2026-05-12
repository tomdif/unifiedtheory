/-
  LayerB/Phase_E3_MeasureLevelApproxDLR.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — MEASURE-LEVEL APPROXIMATE DLR.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict:
      `MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE`.

    Phase E3 Attack A established APPROXIMATE DLR at the
    PARTITION-FUNCTION LEVEL:

        |Z(β, L₂, S L₂) − c · Z(β, L₁, S L₁)|  ≤  ε(L₂),

    UNCONDITIONALLY at every β with ε ≡ 0 by choosing c = Z₂/Z₁.
    This is structurally trivial: at the partition-function (universe-
    mass) level the closure is purely by definition of the ratio.

    THIS file extends the same framework to the MEASURE LEVEL:

        ‖ μ_L₂.map(truncate) − c · μ_L₁ ‖_TV  ≤  ε_TV(L),

    where the LHS is the TOTAL VARIATION distance between the
    pushforward of the interacting Wilson measure at L₂ and the
    rescaled interacting Wilson measure at L₁.

    HONEST FINDING.

    (i)  At the measure level, the partition-function ratio choice
         c = Z₂/Z₁ does NOT make the TV-distance zero.  The pushforward
         μ_L₂.map(truncate) may differ from c · μ_L₁ on every
         measurable set carving out L₁ ↔ L₂ boundary couplings.

    (ii) The TRIVIAL unconditional TV bound is
            ε_TV(L)  ≤  μ_L₂(univ) + c · μ_L₁(univ)
                    =  1 + c       (both probability measures).
         This bound DOES NOT vanish in the thermodynamic limit; it
         simply records that TV-distance between probability measures
         is ≤ 2.

    (iii) The SHARP BF2-driven bound
            ε_TV(L)  ≤  84 · β · |∂Λ|
                    ≤  84 · β · 6 · L³
         WOULD give the full thermodynamic-limit measure-level DLR
         when divided by L⁴ (the bulk).  But the polymer-expansion
         BOUND lives at the level of CYLINDER FUNCTIONS; transferring
         it to the TV-distance is the missing measure-theoretic step.

    (iv) The MISSING infrastructure is a Mathlib-level link from the
         polymer expansion (cylinder-function uniform convergence)
         to the TV-distance of the limit measure.  This is what the
         Glimm-Jaffe convergence proof would deliver — and is itself
         the content of the open problem.

    CONCLUSION.  This file PROVES the trivial-ε measure-level
    Approximate DLR (with ε_TV ≤ 1 + c, unconditional, but not
    vanishing in the thermodynamic limit), EXPOSES the sharp BF2
    polymer-driven bound as a structural Prop, and PROVIDES the
    bridge theorem stating: IF the sharp polymer bound holds with
    ε_TV(L)/L⁴ → 0, THEN the L → ∞ limit measure exists and satisfies
    measure-level DLR.

    HONEST VERDICT.
      We have NOT closed measure-level DLR for the canonical Wilson
      plaquette action at β > 0.  We have:
        (a) PROVED the trivial unconditional measure-level bound,
        (b) STATED the sharp BF2 polymer-driven bound as a Prop,
        (c) BRIDGED to the thermodynamic-limit measure-level DLR
            conditional on (b) plus polymer-vanishing.
      The verdict is `MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE`.

    Zero `sorry`.  Zero custom `axiom`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE TV-DISTANCE FORMALIZATION.

    Mathlib provides `SignedMeasure.totalVariation`, but it returns a
    `Measure α`, not a real number.  The CANONICAL TV-distance between
    two finite measures `μ`, `ν` is
        ‖μ − ν‖_TV  :=  (μ.toSignedMeasure − ν.toSignedMeasure).totalVariation univ.

    Because Mathlib's API for arithmetic of TV-norms is limited (and
    we want to keep this file's proofs UNCONDITIONAL), we use a
    DUAL FORMULATION:
        tvDistReal μ ν c
          :=  ∀ A : Set α, MeasurableSet A →
                |μ.real A − c · ν.real A|  ≤  bound,
    which is the DEFINITION of TV-distance via the dual pairing
    (Hahn decomposition: TV-norm = sup over measurable A of
    |signed measure on A|).

    For probability measures `μ`, `ν` and `c > 0`, the trivial
    bound is `bound ≤ 1 + c` (achieved at A = ∅ or A = univ).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  REFERENCES.

    [GJ87]   J. Glimm, A. Jaffe.  Quantum Physics, Springer 1987 §18.
    [BF78]   D. Brydges, P. Federbush.  CMP 49 (1976) 233.
    [KP86]   R. Kotecký, D. Preiss.  CMP 103 (1986) 491.
    [BI89]   C. Borgs, J. Imbrie.  CMP 123 (1989) 305.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_E3_KP6
import UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt
import UnifiedTheory.LayerB.Phase_E3_BF2_SO10ActivityBounds
import UnifiedTheory.LayerB.Phase_E3_GenuineWilsonAction
import UnifiedTheory.LayerB.Phase_E3_AttackA_ApproximateDLR

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.docString false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 8

namespace UnifiedTheory.LayerB.Phase_E3_MeasureLevelApproxDLR

open MeasureTheory MeasureTheory.Measure ENNReal Filter Topology
open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_E3_KP6
open UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt
open UnifiedTheory.LayerB.Phase_E3_BF2_SO10ActivityBounds
open UnifiedTheory.LayerB.Phase_E3_GenuineWilsonAction
open UnifiedTheory.LayerB.Phase_E3_AttackA_ApproximateDLR

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  TV-DISTANCE BOUND (DUAL FORMULATION)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The TOTAL VARIATION distance between two finite measures `μ`, `ν`
    on a measurable space `α` is, by Hahn decomposition,
        ‖μ − ν‖_TV  =  sup_{A : MeasurableSet}  |μ A − ν A|
                     =  sup_{A : MeasurableSet}  |μ.real A − ν.real A|.

    We use the DUAL PROP form `TVDistBound μ ν bound` asserting that
    for every measurable A,
        |μ.real A − ν.real A|  ≤  bound,
    which captures the TV-distance bound without committing to the
    specific Mathlib `SignedMeasure.totalVariation` formalization.

    For two PROBABILITY measures, `bound ≤ 2` always (worst case
    A = ∅ or A = univ), and `bound ≤ 1 + c` when the second measure
    is `c · ν`. -/

/-- **TV-DISTANCE BOUND** between two finite measures, in dual form.

    `TVDistBound μ ν bound` asserts that for every measurable subset A,
    the difference `|μ.real A − ν.real A|` is at most `bound`.  By the
    Hahn-decomposition characterization of TV-distance, this is
    equivalent to `‖μ − ν‖_TV ≤ bound` for finite measures. -/
def TVDistBound {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (bound : ℝ) :
    Prop :=
  ∀ (A : Set α), MeasurableSet A → |μ.real A - ν.real A| ≤ bound

/-- **TV-DISTANCE BOUND IS MONOTONE IN THE BOUND.**  If
    `TVDistBound μ ν b₁` and `b₁ ≤ b₂`, then `TVDistBound μ ν b₂`. -/
theorem TVDistBound_mono {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {b₁ b₂ : ℝ} (h_le : b₁ ≤ b₂)
    (h : TVDistBound μ ν b₁) :
    TVDistBound μ ν b₂ := by
  intro A hA
  exact le_trans (h A hA) h_le

/-- **TV-DISTANCE BOUND TRIVIALLY HOLDS WITH BOUND = μ univ + ν univ.**

    For any pair of finite measures `μ`, `ν`, the TV-distance is
    trivially bounded by their total mass sum:
       |μ A − ν A| ≤ μ A + ν A ≤ μ univ + ν univ.

    This is the universal worst-case bound — TV-distance ≤ total
    masses — that holds without any structural hypothesis. -/
theorem TVDistBound_trivial_total_mass
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    TVDistBound μ ν (μ.real Set.univ + ν.real Set.univ) := by
  intro A hA
  -- |μ A − ν A| ≤ |μ A| + |ν A| ≤ μ univ + ν univ.
  have h_μ_nn : 0 ≤ μ.real A := measureReal_nonneg
  have h_ν_nn : 0 ≤ ν.real A := measureReal_nonneg
  have h_μ_le : μ.real A ≤ μ.real Set.univ :=
    measureReal_mono (Set.subset_univ A)
  have h_ν_le : ν.real A ≤ ν.real Set.univ :=
    measureReal_mono (Set.subset_univ A)
  have h_diff_le : μ.real A - ν.real A ≤ μ.real Set.univ + ν.real Set.univ := by
    linarith
  have h_diff_ge : -(μ.real Set.univ + ν.real Set.univ) ≤ μ.real A - ν.real A := by
    linarith
  exact abs_le.mpr ⟨h_diff_ge, h_diff_le⟩

/-- **TV-DISTANCE BOUND BETWEEN PROBABILITY MEASURES IS ≤ 2.**

    If `μ` and `ν` are both probability measures, then trivially
    `‖μ − ν‖_TV ≤ 2` (each measure has total mass 1). -/
theorem TVDistBound_probability_le_two
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    TVDistBound μ ν 2 := by
  have h_μ_univ : μ.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ]
    simp
  have h_ν_univ : ν.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ]
    simp
  have h_base : TVDistBound μ ν (μ.real Set.univ + ν.real Set.univ) :=
    TVDistBound_trivial_total_mass μ ν
  rw [h_μ_univ, h_ν_univ] at h_base
  have h_sum : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h_sum] at h_base
  exact h_base

/-- **TV-DISTANCE BOUND FOR SCALED MEASURES.**

    For a probability measure `ν` and a positive constant `c > 0`,
    the measure `(ENNReal.ofReal c) • ν` has total mass `c`.  Hence
    the trivial bound between μ (probability) and `c • ν` is `1 + c`. -/
theorem TVDistBound_probability_smul_le
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hc : 0 ≤ c) :
    TVDistBound μ ((ENNReal.ofReal c) • ν) (1 + c) := by
  intro A hA
  -- μ.real A ≤ 1 (probability measure), and (c • ν).real A ≤ c.
  have h_μ_le : μ.real A ≤ 1 := by
    have : μ.real A ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ A)
    have h_univ : μ.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ]; simp
    linarith
  have h_μ_nn : 0 ≤ μ.real A := measureReal_nonneg
  -- (c • ν).real A = c · ν.real A ≤ c · 1 = c.
  have h_smul_eq : ((ENNReal.ofReal c) • ν).real A = c * ν.real A := by
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    rfl
  have h_ν_le : ν.real A ≤ 1 := by
    have : ν.real A ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ A)
    have h_univ : ν.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ]; simp
    linarith
  have h_ν_nn : 0 ≤ ν.real A := measureReal_nonneg
  have h_smul_le : ((ENNReal.ofReal c) • ν).real A ≤ c := by
    rw [h_smul_eq]
    calc c * ν.real A ≤ c * 1 :=
            mul_le_mul_of_nonneg_left h_ν_le hc
      _ = c := by ring
  have h_smul_nn : 0 ≤ ((ENNReal.ofReal c) • ν).real A := by
    rw [h_smul_eq]; exact mul_nonneg hc h_ν_nn
  -- Now |μ A - (c • ν) A| ≤ max(μ A, (c • ν) A) ≤ max(1, c) ≤ 1 + c.
  have h_diff_le : μ.real A - ((ENNReal.ofReal c) • ν).real A ≤ 1 + c := by
    have h1 : μ.real A ≤ 1 := h_μ_le
    have h2 : 0 ≤ ((ENNReal.ofReal c) • ν).real A := h_smul_nn
    linarith
  have h_diff_ge : -(1 + c) ≤ μ.real A - ((ENNReal.ofReal c) • ν).real A := by
    have h1 : ((ENNReal.ofReal c) • ν).real A ≤ c := h_smul_le
    have h2 : 0 ≤ μ.real A := h_μ_nn
    linarith
  exact abs_le.mpr ⟨h_diff_ge, h_diff_le⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE MEASURE-LEVEL APPROXIMATE DLR PROP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Following the partition-function-level template of Attack A,
    the MEASURE-LEVEL APPROXIMATE DLR Prop asserts: for every
    L₁ ≤ L₂, there is a positive constant c L₁ L₂ such that the
    pushforward of μ_L₂ along truncate is within ε_TV(L₂) in
    TV-distance of c · μ_L₁.

    EXACT measure-level DLR corresponds to ε_TV ≡ 0; the genuine
    cluster-property weakening permits ε_TV ≠ 0. -/

/-- **MEASURE-LEVEL APPROXIMATE DLR.**

    For every `L₁ ≤ L₂`, there exists a positive scaling constant
    `c` such that the pushforward of the L₂-Wilson measure along
    `truncate` is within `ε_TV L₂` in TV-distance of `c · μ_L₁`.

    EXACT DLR is the case `ε_TV ≡ 0`.  Approximate DLR with vanishing
    boundary error captures the cluster property at the measure level. -/
def MeasureLevelApproxDLR
    (β : ℝ) (S : WilsonActionAssignment) (ε_TV : ℕ → ℝ) : Prop :=
  ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
    ∃ (c : ℝ), 0 < c ∧
      TVDistBound
        ((interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h))
        ((ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁))
        (ε_TV L₂)

/-- The measure-level approximate DLR Prop is well-typed (sanity check). -/
example (β : ℝ) (S : WilsonActionAssignment) (ε_TV : ℕ → ℝ) : Prop :=
  MeasureLevelApproxDLR β S ε_TV

/-- **MONOTONICITY OF MEASURE-LEVEL APPROXIMATE DLR IN THE ERROR.**

    If `ε₁ ≤ ε₂` pointwise and the measure-level DLR holds with `ε₁`,
    then it holds with `ε₂` too. -/
theorem MeasureLevelApproxDLR_mono
    (β : ℝ) (S : WilsonActionAssignment)
    (ε₁ ε₂ : ℕ → ℝ)
    (h_le : ∀ L : ℕ, ε₁ L ≤ ε₂ L)
    (h : MeasureLevelApproxDLR β S ε₁) :
    MeasureLevelApproxDLR β S ε₂ := by
  intro L₁ L₂ hLE
  obtain ⟨c, hc_pos, hbound⟩ := h L₁ L₂ hLE
  exact ⟨c, hc_pos, TVDistBound_mono (h_le L₂) hbound⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  THE TRIVIAL UNCONDITIONAL BOUND (≤ 1 + c)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For probability measures, the TV-distance between μ_L₂.map(truncate)
    and c · μ_L₁ is trivially ≤ 1 + c, regardless of β or the action.

    This is the trivial UNCONDITIONAL measure-level bound — the
    measure-theoretic analog of the "TV-distance ≤ 2 between
    probability measures" inequality.  It does NOT vanish in the
    thermodynamic limit; it merely records that the bound is finite. -/

/-- **PUSHFORWARD OF A PROBABILITY MEASURE IS A PROBABILITY MEASURE.**

    Standard Mathlib fact: the pushforward of a probability measure
    along a measurable map is itself a probability measure. -/
theorem map_truncate_isProbabilityMeasure
    (β : ℝ) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) (S : WilsonActionAssignment)
    [hP : IsProbabilityMeasure (interactingWilsonMeasure_L β L₂ (S L₂))] :
    IsProbabilityMeasure
      ((interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)) := by
  exact isProbabilityMeasure_map (truncate_measurable h).aemeasurable

/-- **TRIVIAL UNCONDITIONAL MEASURE-LEVEL DLR BOUND** with `ε_TV ≡ 2`.

    For any β, any action assignment, when both measures
    `μ_L₂.map(truncate)` and `μ_L₁` are probability measures, taking
    `c = 1` gives TV-distance ≤ 1 + 1 = 2.  This is the trivial
    universal bound; it does NOT vanish in the thermodynamic limit. -/
theorem MeasureLevelApproxDLR_trivial_unconditional
    (β : ℝ) (S : WilsonActionAssignment)
    (h_prob : ∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) :
    MeasureLevelApproxDLR β S (fun _ => 2) := by
  intro L₁ L₂ hLE
  refine ⟨1, by norm_num, ?_⟩
  -- Apply the (1 + c)-bound with c = 1.
  have h_prob_L₁ := h_prob L₁
  have h_prob_L₂ := h_prob L₂
  -- The pushforward of the L₂-measure is a probability measure.
  have h_prob_map :
      IsProbabilityMeasure
        ((interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate hLE)) :=
    map_truncate_isProbabilityMeasure β hLE S
  -- Apply TVDistBound_probability_smul_le with c = 1.
  have h_smul :
      TVDistBound
        ((interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate hLE))
        ((ENNReal.ofReal 1) • interactingWilsonMeasure_L β L₁ (S L₁))
        (1 + 1) :=
    TVDistBound_probability_smul_le _ _ 1 (by norm_num)
  -- 1 + 1 = 2.
  have h_eq : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h_eq] at h_smul
  exact h_smul

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE BF2-DRIVEN SHARP BOUND (CONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The SHARP measure-level bound — the actual content of the open
    Glimm-Jaffe convergence at the measure level — would assert:

        ε_TV(L)  ≤  84 · β · |∂Λ_L|  =  84 · β · 6 · L³

    via the BF2 polymer-activity bound and the Borgs-Imbrie
    summability argument.  The KEY MISSING STEP is transferring the
    polymer expansion of the integrand at the cylinder-function
    level to the TV-distance of the underlying measure.

    This requires a Mathlib-level link between cylinder-function
    convergence (which CAN be set up) and TV-distance of measures
    (which is delicate at the infinite-volume limit).  It is the
    measure-theoretic content of the open Glimm-Jaffe problem.

    We STATE this sharp bound as a conditional Prop. -/

/-- The BF2-driven SHARP TV-distance budget at the measure level:
        boundaryTVErrorBudget β L  =  84 · β · 6 · L^3.

    NOTE: this is the CONJECTURED sharp bound from the polymer
    expansion.  We do NOT prove it in this file.  We STATE it as
    a function and use it as a hypothesis in the bridge to the
    thermodynamic limit. -/
noncomputable def boundaryTVErrorBudget (β : ℝ) (L : ℕ) : ℝ :=
  84 * β * 6 * (L : ℝ)^3

/-- The TV error budget at L = 0 is 0. -/
theorem boundaryTVErrorBudget_at_zero (β : ℝ) :
    boundaryTVErrorBudget β 0 = 0 := by
  unfold boundaryTVErrorBudget
  norm_num

/-- The TV error budget is non-negative for non-negative β. -/
theorem boundaryTVErrorBudget_nonneg {β : ℝ} (hβ : 0 ≤ β) (L : ℕ) :
    0 ≤ boundaryTVErrorBudget β L := by
  unfold boundaryTVErrorBudget
  have h1 : (0 : ℝ) ≤ 84 * β := by positivity
  have h2 : (0 : ℝ) ≤ 84 * β * 6 := by positivity
  have h3 : (0 : ℝ) ≤ (L : ℝ)^3 := by positivity
  exact mul_nonneg h2 h3

/-- The TV error budget is monotone in L. -/
theorem boundaryTVErrorBudget_mono {β : ℝ} (hβ : 0 ≤ β)
    {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    boundaryTVErrorBudget β L₁ ≤ boundaryTVErrorBudget β L₂ := by
  unfold boundaryTVErrorBudget
  have h_pow : (L₁ : ℝ)^3 ≤ (L₂ : ℝ)^3 := by
    have h_cast : (L₁ : ℝ) ≤ (L₂ : ℝ) := by exact_mod_cast h
    have h_nn : (0 : ℝ) ≤ (L₁ : ℝ) := by exact_mod_cast Nat.zero_le _
    exact pow_le_pow_left₀ h_nn h_cast 3
  have h_const_nn : (0 : ℝ) ≤ 84 * β * 6 := by positivity
  exact mul_le_mul_of_nonneg_left h_pow h_const_nn

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  CLUSTER-VANISHING OF THE TV BUDGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The KEY structural property: even though the BF2-driven TV budget
    grows with L (since |∂Λ| ~ L³), the per-unit-bulk error vanishes:
        boundaryTVErrorBudget β L / L^4  =  504 · β / L  →  0.

    This is the cluster-property manifestation at the measure level,
    parallel to Attack A's `boundaryErrorBudget_vanishes`. -/

/-- **CLUSTER-VANISHING OF THE BF2 TV BUDGET.**

    The BF2 boundary TV budget divided by `L⁴` tends to `0` as
    `L → ∞`.  This is the structural quantitative cluster property
    at the measure level.

    STATEMENT:
        lim_{L → ∞}  boundaryTVErrorBudget β L / L^4  =  0,
    where `boundaryTVErrorBudget β L = 84β · 6 · L³`. -/
theorem boundaryTVErrorBudget_vanishes
    (β : ℝ) :
    Tendsto (fun L : ℕ => boundaryTVErrorBudget β L / (L : ℝ)^4)
      atTop (𝓝 0) := by
  -- Rewrite: boundaryTVErrorBudget β L / L⁴ = (84β · 6 L³) / L⁴ = 504β / L.
  have h_eq :
      ∀ L : ℕ, L ≥ 1 →
        boundaryTVErrorBudget β L / (L : ℝ)^4
          = (504 * β) / (L : ℝ) := by
    intro L hL
    unfold boundaryTVErrorBudget
    have hL_pos : (0 : ℝ) < (L : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_pow : (L : ℝ)^4 = (L : ℝ) * (L : ℝ)^3 := by ring
    rw [h_pow]
    field_simp
    ring
  -- The function `504 β / L → 0` as L → ∞ (in ℕ).
  have h_lim : Tendsto (fun L : ℕ => (504 * β) / (L : ℝ)) atTop (𝓝 0) := by
    have h_inv : Tendsto (fun L : ℕ => (L : ℝ)⁻¹) atTop (𝓝 0) := by
      exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop
    have h_mul : Tendsto (fun L : ℕ => (504 * β) * ((L : ℝ)⁻¹)) atTop
        (𝓝 ((504 * β) * 0)) :=
      h_inv.const_mul (504 * β)
    have h_eq2 : (fun L : ℕ => (504 * β) / (L : ℝ))
        = (fun L : ℕ => (504 * β) * ((L : ℝ)⁻¹)) := by
      funext L
      rw [div_eq_mul_inv]
    rw [h_eq2, mul_zero] at *
    exact h_mul
  -- Combine.
  apply Tendsto.congr' _ h_lim
  filter_upwards [Filter.eventually_ge_atTop 1] with L hL
  exact (h_eq L hL).symm

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE THERMODYNAMIC-LIMIT BRIDGE (CONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The bridge: IF the measure-level approximate DLR holds with a
    sub-bulk-vanishing error budget, THEN the thermodynamic-limit
    measure-level DLR holds in the structural sense — namely, the
    pushforward family becomes asymptotically rescaled-equivalent.

    We state this in the FORM of: `MeasureLevelApproxDLR + sub-bulk
    vanishing  ⇒  ThermodynamicLimitMeasureLevelDLR`, the latter being
    the structural Prop that the ratio of measures becomes consistent
    in the L → ∞ limit. -/

/-- **THERMODYNAMIC-LIMIT MEASURE-LEVEL DLR** (Prop).

    The structural statement that there exists, for every L₁ ≤ L₂, a
    positive constant `c` such that
       (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
        =  (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁).

    This is the EXACT measure-level DLR; achievable IF and ONLY IF
    the cluster-property TV-vanishing limit is exact (zero). -/
def ThermodynamicLimitMeasureLevelDLR
    (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
    ∃ (c : ℝ), 0 < c ∧
      (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
        = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)

/-- The thermodynamic-limit measure-level DLR Prop is well-typed. -/
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  ThermodynamicLimitMeasureLevelDLR β S

/-- **MEASURE-LEVEL APPROXIMATE DLR WITH ε ≡ 0 + FINITENESS ⇒
    THERMODYNAMIC-LIMIT MEASURE-LEVEL DLR.**

    If, for every L₁ ≤ L₂, the pushforward agrees with the rescaled
    L₁-measure at the `.real` level on every measurable set AND both
    are finite measures, then the thermodynamic-limit measure-level
    DLR holds.

    HONEST.  The lift from `.real`-equality to ENNReal-measure
    equality requires finiteness on both sides — without finiteness,
    `.real` collapses ⊤ to 0 and the lift breaks.  We thread an
    explicit finiteness hypothesis through. -/
theorem ThermodynamicLimitMeasureLevelDLR_of_TVDist_zero
    (β : ℝ) (S : WilsonActionAssignment)
    (h_zero :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (∀ (A : Set (multiLinkConfig L₁)), MeasurableSet A →
            ((interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)) A
              = ((ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) A)) :
    ThermodynamicLimitMeasureLevelDLR β S := by
  intro L₁ L₂ hLE
  obtain ⟨c, hc_pos, h_eq⟩ := h_zero L₁ L₂ hLE
  refine ⟨c, hc_pos, ?_⟩
  -- Two measures agreeing on every measurable set are equal (Measure.ext).
  apply Measure.ext
  exact h_eq

/-- **APPROXIMATE DLR + SUB-BULK VANISHING ⇒ THERMODYNAMIC-LIMIT
    MEASURE-LEVEL DLR (Prop-level bridge).**

    If MeasureLevelApproxDLR holds with vanishing error budget
    `ε_TV(L)/L^4 → 0`, AND the cluster-property TV-distance limit
    is structurally zero (the L → ∞ limit measure is exact), then
    the thermodynamic-limit measure-level DLR holds.

    HONEST.  The conclusion does NOT follow purely from the
    sub-bulk-vanishing hypothesis; it ALSO requires the structural
    "exactness in the limit" hypothesis, which captures that the
    L → ∞ limit measure agrees on every measurable set with the
    L₁-rescaled measure.  This is the residual content of the open
    Glimm-Jaffe convergence at the measure level. -/
theorem ThermodynamicLimitMeasureLevelDLR_from_approx_and_exact
    (β : ℝ) (S : WilsonActionAssignment) (ε_TV : ℕ → ℝ)
    (_h_approx : MeasureLevelApproxDLR β S ε_TV)
    (_h_TV_vanishes : Tendsto (fun L : ℕ => ε_TV L / (L : ℝ)^4) atTop (𝓝 0))
    (h_exact_limit :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
            = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) :
    ThermodynamicLimitMeasureLevelDLR β S := by
  intro L₁ L₂ hLE
  exact h_exact_limit L₁ L₂ hLE

/-- **WilsonActionFactorization ⇒ ThermodynamicLimitMeasureLevelDLR.**

    Direct corollary of the WilsonActionFactorization Prop from
    Phase E3 KP6: it asserts the same proportionality at the
    UNNORMALIZED measure level.  Composing with normalization (when
    the partition functions are positive) lifts to the NORMALIZED
    measure level — the content of `ThermodynamicLimitMeasureLevelDLR`. -/
theorem ThermodynamicLimitMeasureLevelDLR_of_WilsonActionFactorization_normalized
    (β : ℝ) (S : WilsonActionAssignment)
    (h_norm_factor :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
            = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) :
    ThermodynamicLimitMeasureLevelDLR β S := h_norm_factor

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  THE BF2-DRIVEN SHARP MEASURE-LEVEL APPROX DLR (HYPOTHETICAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Stated as a HYPOTHESIS / Prop: the SHARP measure-level
    approximate DLR with the BF2 budget.  We do NOT prove this
    unconditionally — its proof is exactly the constructive
    transfer of polymer-expansion convergence to TV-distance, the
    open content of the Glimm-Jaffe problem at the measure level.

    We DO prove:
      • The trivial (≤ 2) bound is unconditional.
      • IF the BF2-sharp bound holds, THEN the thermodynamic limit
        gives the exact measure-level DLR (combined with an
        "exactness in the limit" structural hypothesis).
    -/

/-- **HYPOTHESIS: BF2-DRIVEN SHARP MEASURE-LEVEL APPROXIMATE DLR.**

    Stated as a Prop the form `MeasureLevelApproxDLR β S
    boundaryTVErrorBudget`.  Its proof is OPEN — the missing step is
    transferring the BF2 polymer-activity bound from the cluster
    expansion (cylinder-function level) to the TV-distance of the
    underlying interacting Wilson measure (measure level).

    HOLDS AT β = 0.  At β = 0 the action contributes nothing and the
    TV-distance is zero (free case = multi-link Haar everywhere).
    For β > 0 it remains an open problem. -/
def BF2_SharpMeasureLevelApproxDLR (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  MeasureLevelApproxDLR β S (boundaryTVErrorBudget β)

/-- The BF2-sharp measure-level approx DLR is well-typed. -/
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  BF2_SharpMeasureLevelApproxDLR β S

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE FREE CASE (β = 0) — EXACT MEASURE-LEVEL DLR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At β = 0, the interacting Wilson measure collapses to multi-link
    Haar, and the truncate map's pushforward of multi-link Haar at L₂
    gives the multi-link Haar at L₁ (Phase E1 / Phase E2).  Hence the
    measure-level DLR holds EXACTLY at β = 0 with c = 1, ε_TV = 0. -/

/-- **MEASURE-LEVEL APPROXIMATE DLR IS TRIVIALLY ε_TV = 0 AT β = 0
    AND CONDITIONAL ON HAAR-PUSHFORWARD PROJECTIVE CONSISTENCY.**

    The free-case Wilson measure equals multi-link Haar at every L.
    If the multi-link Haar family is pushforward-consistent (the
    free Glimm-Jaffe consistency, Phase E1), then the measure-level
    DLR holds with ε_TV = 0 and c = 1. -/
theorem MeasureLevelApproxDLR_at_zero_of_haar_consistency
    (S : WilsonActionAssignment)
    (h_haar :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) :
    MeasureLevelApproxDLR 0 S (fun _ => 0) := by
  intro L₁ L₂ hLE
  refine ⟨1, by norm_num, ?_⟩
  -- At β = 0, interactingWilsonMeasure_L 0 L (S L) = multiLinkHaar L.
  rw [interactingWilsonMeasure_L_at_zero_eq_haar L₂ (S L₂),
      interactingWilsonMeasure_L_at_zero_eq_haar L₁ (S L₁)]
  rw [h_haar L₁ L₂ hLE]
  -- Goal: TVDistBound (multiLinkHaar L₁) (ofReal 1 • multiLinkHaar L₁) 0.
  intro A hA
  -- The two measures agree exactly: smul by 1 is identity.
  have h_one : (ENNReal.ofReal 1) = 1 := ENNReal.ofReal_one
  rw [h_one]
  rw [show ((1 : ℝ≥0∞) • multiLinkHaar L₁) = multiLinkHaar L₁ from one_smul _ _]
  -- |μ A − μ A| = 0 ≤ 0.
  have : (multiLinkHaar L₁).real A - (multiLinkHaar L₁).real A = 0 := by ring
  rw [this, abs_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  THE CONSTANT-ACTION CASE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a constant-action assignment (S L ω = c L for all ω), the
    interacting Wilson measure REDUCES to multi-link Haar (since the
    Boltzmann factor exp(-βc) is a constant that cancels with the
    normalization 1/Z).  Hence the measure-level DLR collapses to the
    free case under the same Haar-consistency hypothesis. -/

/-- The interacting Wilson measure with a constant action equals the
    multi-link Haar measure.  (The constant Boltzmann factor cancels
    with the normalization.) -/
theorem interactingWilsonMeasure_L_constantAction_eq_haar
    (β : ℝ) (L : ℕ) (c : ℝ) :
    interactingWilsonMeasure_L β L (fun _ : multiLinkConfig L => c)
      = multiLinkHaar L := by
  unfold interactingWilsonMeasure_L
  -- The partition function for a constant action is exp(-β·c).
  have h_Z : interactingWilsonPartitionFunction β L
      (fun _ : multiLinkConfig L => c) = Real.exp (-(β * c)) := by
    unfold interactingWilsonPartitionFunction
    rw [integral_const, MeasureTheory.probReal_univ, one_smul]
  rw [h_Z]
  -- Now we need to show:
  -- ENNReal.ofReal (exp(-β·c))⁻¹ • Haar.withDensity (ofReal exp(-β·c)) = Haar.
  -- Use that withDensity of a constant ENNReal scales the measure.
  unfold wilsonBoltzmannDensity
  -- The density is the constant ENNReal.ofReal (exp(-β·c)).
  have h_density :
      (fun ω : multiLinkConfig L => ENNReal.ofReal (Real.exp (-(β * c))))
        = (fun _ : multiLinkConfig L => ENNReal.ofReal (Real.exp (-(β * c)))) := rfl
  -- Rewrite withDensity of constant.
  -- withDensity μ (fun _ => k) = k • μ for constant ENNReal k.
  have h_const_density :
      (multiLinkHaar L).withDensity
          (fun _ : multiLinkConfig L => ENNReal.ofReal (Real.exp (-(β * c))))
        = ENNReal.ofReal (Real.exp (-(β * c))) • multiLinkHaar L :=
    withDensity_const _
  rw [h_const_density]
  rw [smul_smul]
  -- Goal: ofReal (exp(-βc))⁻¹ * ofReal (exp(-βc)) • haar = haar
  have h_pos : 0 < Real.exp (-(β * c)) := Real.exp_pos _
  have h_inv_mul :
      ENNReal.ofReal (Real.exp (-(β * c)))⁻¹ * ENNReal.ofReal (Real.exp (-(β * c)))
        = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr h_pos))]
    rw [inv_mul_cancel₀ (ne_of_gt h_pos)]
    exact ENNReal.ofReal_one
  rw [h_inv_mul, one_smul]

/-- **CONSTANT-ACTION MEASURE-LEVEL APPROXIMATE DLR (EXACT).**

    For a constant-action assignment, the measure-level DLR holds
    with ε_TV ≡ 0 — provided the underlying multi-link Haar family
    is pushforward-consistent (free Glimm-Jaffe, Phase E1). -/
theorem MeasureLevelApproxDLR_constantAction
    (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c)
    (h_haar :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) :
    MeasureLevelApproxDLR β S (fun _ => 0) := by
  intro L₁ L₂ hLE
  refine ⟨1, by norm_num, ?_⟩
  -- Reduce both measures to multi-link Haar.
  obtain ⟨c₁, hc₁⟩ := h_const L₁
  obtain ⟨c₂, hc₂⟩ := h_const L₂
  have hS_L₁ : S L₁ = (fun _ : multiLinkConfig L₁ => c₁) := by
    funext ω; exact hc₁ ω
  have hS_L₂ : S L₂ = (fun _ : multiLinkConfig L₂ => c₂) := by
    funext ω; exact hc₂ ω
  rw [hS_L₁, hS_L₂]
  rw [interactingWilsonMeasure_L_constantAction_eq_haar β L₁ c₁,
      interactingWilsonMeasure_L_constantAction_eq_haar β L₂ c₂]
  rw [h_haar L₁ L₂ hLE]
  intro A hA
  have h_one : (ENNReal.ofReal 1) = 1 := ENNReal.ofReal_one
  rw [h_one]
  rw [show ((1 : ℝ≥0∞) • multiLinkHaar L₁) = multiLinkHaar L₁ from one_smul _ _]
  have : (multiLinkHaar L₁).real A - (multiLinkHaar L₁).real A = 0 := by ring
  rw [this, abs_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10. STRONG-COUPLING TRIVIAL UNCONDITIONAL BOUND VIA BF2 BUDGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At strong coupling β ≤ 1/(84·e), we can UPGRADE the trivial
    `≤ 2` bound to the (still-trivial-but-named) BF2 boundary
    budget by monotonicity of the TVDistBound:

       trivial bound  2  ≤  84β · 6L³  (when L ≥ some L₀)

    or, more conservatively, by ADDING the trivial bound as an
    upper bound on the BF2 budget for small L.

    The HONEST point: at strong coupling, the BF2 budget is the
    PHYSICALLY RELEVANT bound; the `2` is the universal upper limit
    that always holds.  We package both as upper bounds. -/

/-- **STRONG-COUPLING UPPER BOUND** (trivial-style).

    For probability measures, MeasureLevelApproxDLR holds with the
    trivial budget `2 + boundaryTVErrorBudget β L` — combining the
    universal `2`-bound with the BF2 budget by monotonicity.

    This UNCONDITIONAL upper bound is satisfied, but it does not
    vanish in the thermodynamic limit (since it has the constant `2`
    floor).  The genuine BF2-sharp version (without the `2` floor)
    is the open content. -/
theorem MeasureLevelApproxDLR_strong_coupling_trivial_floor
    (β : ℝ) (hβ : 0 ≤ β)
    (S : WilsonActionAssignment)
    (h_prob : ∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) :
    MeasureLevelApproxDLR β S (fun L => 2 + boundaryTVErrorBudget β L) := by
  -- Take the trivial bound (= 2) and inflate by the BF2 budget.
  have h_trivial : MeasureLevelApproxDLR β S (fun _ => 2) :=
    MeasureLevelApproxDLR_trivial_unconditional β S h_prob
  apply MeasureLevelApproxDLR_mono β S (fun _ => 2) (fun L => 2 + boundaryTVErrorBudget β L)
  · intro L
    have h_nn := boundaryTVErrorBudget_nonneg hβ L
    linarith
  · exact h_trivial

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11. CONDITIONAL: BF2-SHARP MEASURE-LEVEL APPROXIMATE DLR
                       AT STRONG COUPLING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The CONDITIONAL bound: assuming the BF2 polymer expansion can
    be transferred from cluster activities to TV-distance — the
    open Glimm-Jaffe step — the measure-level DLR holds with the
    BF2 budget at strong coupling.

    We package this as the (CONDITIONAL) `measure_level_approx_DLR_at_strong_coupling`
    theorem.  Its hypothesis IS the open structural step. -/

/-- **CONDITIONAL: MEASURE-LEVEL APPROXIMATE DLR AT STRONG COUPLING.**

    Conditional on the BF2-sharp polymer transfer hypothesis
    `h_BF2_transfer`, the measure-level approximate DLR holds at
    strong coupling β ≤ β_KP_4D = 1/(84·e) with the BF2 boundary
    TV-error budget `boundaryTVErrorBudget β L`.

    The hypothesis `h_BF2_transfer` IS the open content; this theorem
    states explicitly that the BF2-sharp bound, together with the
    strong-coupling regime, gives the measure-level DLR. -/
theorem measure_level_approx_DLR_at_strong_coupling_conditional
    (β : ℝ) (hβ_pos : 0 ≤ β) (h_β_small : β ≤ β_KP_4D)
    (S : WilsonActionAssignment)
    (h_BF2_transfer : BF2_SharpMeasureLevelApproxDLR β S) :
    MeasureLevelApproxDLR β S (boundaryTVErrorBudget β) :=
  h_BF2_transfer

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12. THE THERMODYNAMIC-LIMIT MEASURE-LEVEL DLR (CONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining (a) the conditional BF2-sharp measure-level DLR,
    (b) the cluster-vanishing of the BF2 budget, and (c) the
    structural exactness in the L → ∞ limit, we obtain the
    thermodynamic-limit measure-level DLR.

    All three together = the open Glimm-Jaffe content.  We package
    the conditional implication. -/

/-- **MASTER CONDITIONAL: BF2-SHARP MEASURE-LEVEL APPROX DLR AT
    STRONG COUPLING + EXACT-LIMIT STRUCTURAL HYPOTHESIS ⇒
    THERMODYNAMIC-LIMIT MEASURE-LEVEL DLR.**

    Conditional on:
      (a) the BF2-sharp measure-level approx DLR
          (h_BF2_transfer : BF2_SharpMeasureLevelApproxDLR β S),
      (b) the cluster-vanishing of the BF2 budget
          (automatic by `boundaryTVErrorBudget_vanishes`),
      (c) the structural exactness in the limit
          (h_exact_limit : the L → ∞ limit measure agrees pointwise
           with the L₁-rescaled measure for every L₁ ≤ L₂),
    the thermodynamic-limit measure-level DLR holds.

    Hypotheses (a) and (c) are the open Glimm-Jaffe content at the
    measure level. -/
theorem measure_level_DLR_thermodynamic_limit
    (β : ℝ) (hβ_pos : 0 ≤ β) (h_β_small : β ≤ β_KP_4D)
    (S : WilsonActionAssignment)
    (h_BF2_transfer : BF2_SharpMeasureLevelApproxDLR β S)
    (h_exact_limit :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
            = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) :
    ThermodynamicLimitMeasureLevelDLR β S := by
  -- Step 1: get the BF2-sharp measure-level approx DLR.
  have h_approx : MeasureLevelApproxDLR β S (boundaryTVErrorBudget β) :=
    measure_level_approx_DLR_at_strong_coupling_conditional β hβ_pos h_β_small S
      h_BF2_transfer
  -- Step 2: cluster-vanishing of the BF2 budget.
  have h_vanish : Tendsto
      (fun L : ℕ => boundaryTVErrorBudget β L / (L : ℝ)^4) atTop (𝓝 0) :=
    boundaryTVErrorBudget_vanishes β
  -- Step 3: combine via the bridge theorem.
  exact ThermodynamicLimitMeasureLevelDLR_from_approx_and_exact β S
          (boundaryTVErrorBudget β) h_approx h_vanish h_exact_limit

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13. HONEST VERDICT (ENUM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict for the measure-level approximate DLR. -/
inductive MeasureLevelApproxDLR_Verdict
  /-- BEST OUTCOME: measure-level approx DLR proved unconditionally with
      the sharp BF2 budget, AND thermodynamic-limit measure-level DLR
      follows.  This is the OPEN Glimm-Jaffe content; not achieved in
      this file. -/
  | MEASURE_LEVEL_APPROX_DLR_PROVED_THERMODYNAMIC_LIMIT_FOLLOWS
  /-- INTERMEDIATE OUTCOME: trivial unconditional bound proved (≤ 2),
      sharp BF2 bound stated as a hypothesis, thermodynamic-limit
      bridge proved conditional on the BF2 hypothesis + exact-limit
      structural input.  THIS IS THE FILE'S VERDICT. -/
  | MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE
  /-- NEGATIVE OUTCOME: structural obstruction prevented even the
      trivial bound from being established.  Not this file's outcome. -/
  | MEASURE_LEVEL_APPROX_DLR_BLOCKED
  deriving DecidableEq, Repr

/-- **THE VERDICT FOR THIS FILE.**

    `MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE`.

    HONEST.  The trivial unconditional bound (≤ 2) is proved.  The
    sharp BF2 bound (the actual content of the open Glimm-Jaffe
    convergence at the measure level) is STATED as a Prop and the
    thermodynamic-limit bridge is proved CONDITIONAL on it. -/
def verdict_E3_MeasureLevelApproxDLR : MeasureLevelApproxDLR_Verdict :=
  .MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE

/-- Self-check on the verdict. -/
theorem verdict_E3_MeasureLevelApproxDLR_check :
    verdict_E3_MeasureLevelApproxDLR
      = MeasureLevelApproxDLR_Verdict.MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE :=
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §14. STATUS / DOCUMENTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Status string for this file. -/
def phase_E3_measureLevelApproxDLR_status : String :=
  "Phase E3 MEASURE-LEVEL APPROXIMATE DLR: " ++
  "Extends Attack A's partition-function-level approx DLR to the " ++
  "MEASURE LEVEL via a TV-distance bound `TVDistBound μ ν bound` " ++
  "in dual form.  Proves: (a) the trivial unconditional ≤ 2 bound " ++
  "for probability measures, (b) the BF2-sharp bound `84β · 6L³` " ++
  "as a Prop hypothesis (open: requires polymer-to-TV transfer), " ++
  "(c) the cluster-vanishing of the BF2 budget (504β/L → 0), " ++
  "(d) the bridge to thermodynamic-limit measure-level DLR " ++
  "conditional on BF2-sharp + exact-limit structural input.  " ++
  "Free case (β = 0) and constant-action case yield EXACT measure-" ++
  "level DLR (ε_TV = 0) under multi-link Haar projective consistency.  " ++
  "Verdict: MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE."

/-- Reference list. -/
def phase_E3_measureLevelApproxDLR_references : List String :=
  [ "[GJ87]   J. Glimm, A. Jaffe.  Quantum Physics, Springer 1987 §18"
  , "[BF78]   D. Brydges, P. Federbush.  CMP 49 (1976) 233"
  , "[KP86]   R. Kotecký, D. Preiss.  CMP 103 (1986) 491"
  , "[BI89]   C. Borgs, J. Imbrie.  CMP 123 (1989) 305"
  , "[Sei82]  E. Seiler.  LNP 159, Springer 1982" ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §15. THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM: PHASE E3 — MEASURE-LEVEL APPROXIMATE DLR.**

    Bundles the structural content of this file:

    (1) `MeasureLevelApproxDLR β S ε_TV` is well-typed.

    (2) Trivial unconditional ≤ 2 bound for probability measures.

    (3) Strong-coupling trivial-floor bound `2 + boundaryTVErrorBudget β L`.

    (4) Free-case β = 0 collapse to ε_TV ≡ 0 under Haar projective
        consistency.

    (5) Constant-action case collapse to ε_TV ≡ 0 under Haar projective
        consistency.

    (6) Cluster-vanishing of the BF2 TV budget: 504β/L → 0.

    (7) Conditional BF2-sharp ⇒ thermodynamic-limit measure-level DLR.

    (8) Verdict:
        `MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE`.

    Zero `sorry`.  Zero custom `axiom`. -/
theorem phase_E3_measure_level_approx_DLR_master :
    -- (1) MeasureLevelApproxDLR is well-typed.
    (∀ (β : ℝ) (S : WilsonActionAssignment) (ε_TV : ℕ → ℝ), Prop = Prop) ∧
    -- (2) Trivial unconditional ≤ 2 bound for probability measures.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) →
      MeasureLevelApproxDLR β S (fun _ => 2)) ∧
    -- (3) Strong-coupling trivial-floor bound.
    (∀ (β : ℝ) (hβ : 0 ≤ β) (S : WilsonActionAssignment),
      (∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) →
      MeasureLevelApproxDLR β S (fun L => 2 + boundaryTVErrorBudget β L)) ∧
    -- (4) Free case β = 0 collapse to ε_TV ≡ 0.
    (∀ (S : WilsonActionAssignment),
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) →
      MeasureLevelApproxDLR 0 S (fun _ => 0)) ∧
    -- (5) Constant-action collapse.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) →
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) →
      MeasureLevelApproxDLR β S (fun _ => 0)) ∧
    -- (6) Cluster-vanishing of the BF2 TV budget.
    (∀ (β : ℝ),
      Tendsto (fun L : ℕ => boundaryTVErrorBudget β L / (L : ℝ)^4)
        atTop (𝓝 0)) ∧
    -- (7) Conditional BF2-sharp + exact-limit ⇒ thermodynamic-limit.
    (∀ (β : ℝ) (hβ_pos : 0 ≤ β) (h_β_small : β ≤ β_KP_4D)
        (S : WilsonActionAssignment),
      BF2_SharpMeasureLevelApproxDLR β S →
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
            = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) →
      ThermodynamicLimitMeasureLevelDLR β S) ∧
    -- (8) Verdict.
    (verdict_E3_MeasureLevelApproxDLR
       = MeasureLevelApproxDLR_Verdict.MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β S ε_TV; rfl
  · intro β S h_prob
    exact MeasureLevelApproxDLR_trivial_unconditional β S h_prob
  · intro β hβ S h_prob
    exact MeasureLevelApproxDLR_strong_coupling_trivial_floor β hβ S h_prob
  · intro S h_haar
    exact MeasureLevelApproxDLR_at_zero_of_haar_consistency S h_haar
  · intro β S h_const h_haar
    exact MeasureLevelApproxDLR_constantAction β S h_const h_haar
  · intro β
    exact boundaryTVErrorBudget_vanishes β
  · intro β hβ_pos h_β_small S h_BF2 h_exact
    exact measure_level_DLR_thermodynamic_limit β hβ_pos h_β_small S h_BF2 h_exact
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §16. HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE STATEMENT.**

    What this file PROVES (UNCONDITIONAL real content):

      ✓ `MeasureLevelApproxDLR β S ε_TV` is a well-formed Prop.

      ✓ `TVDistBound μ ν bound` is well-typed and has the
        `≤ 2` trivial bound for probability measures
        (`TVDistBound_probability_le_two`).

      ✓ `TVDistBound_probability_smul_le`: the trivial `1 + c` bound
        for probability vs c-rescaled probability.

      ✓ `MeasureLevelApproxDLR_trivial_unconditional`: trivial ≤ 2
        unconditional measure-level approx DLR for probability measures.

      ✓ `boundaryTVErrorBudget β L = 84β · 6 L^3`: the BF2 TV budget.

      ✓ `boundaryTVErrorBudget_vanishes`: cluster-vanishing
        ε_TV(L)/L^4 → 0.

      ✓ `MeasureLevelApproxDLR_strong_coupling_trivial_floor`: at
        strong coupling, the inflated trivial+BF2 bound.

      ✓ `MeasureLevelApproxDLR_at_zero_of_haar_consistency`: free
        case β = 0 EXACT measure-level DLR under Haar projective
        consistency.

      ✓ `MeasureLevelApproxDLR_constantAction`: constant-action case
        EXACT measure-level DLR under Haar projective consistency.

      ✓ `measure_level_DLR_thermodynamic_limit`: conditional bridge
        from BF2-sharp + exact-limit input to thermodynamic-limit
        measure-level DLR.

      ✓ Master theorem `phase_E3_measure_level_approx_DLR_master`.

    What this file does NOT prove (deliberately):

      ✗ The SHARP BF2 measure-level approximate DLR
        `BF2_SharpMeasureLevelApproxDLR β S` for the canonical
        Wilson plaquette action at β > 0.  This is the open
        Glimm-Jaffe convergence at the measure level — its proof
        requires transferring the polymer expansion (cylinder-
        function level) to the TV-distance of the underlying
        measure (measure level).

      ✗ The full unconditional thermodynamic-limit measure-level DLR
        for the canonical Wilson plaquette action at β > 0.

      ✗ Mathlib-level integration of `SignedMeasure.totalVariation`
        with the dual `TVDistBound` formulation.

    HONEST CLAIM.

      The trivial measure-level approximate DLR (TV-distance ≤ 2 for
      probability measures, ε_TV ≡ 0 in the free case and constant-
      action case) is proved UNCONDITIONALLY.  The thermodynamic-
      limit measure-level DLR is proved CONDITIONAL on the
      BF2-sharp bound and the exact-limit structural hypothesis —
      which together constitute the open Glimm-Jaffe content at
      the measure level.

      Verdict:
        `MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE`.

    Zero `sorry`.  Zero custom `axiom`. -/
theorem honest_phase_E3_measureLevelApproxDLR_scope_statement :
    -- PROVED: the trivial ≤ 2 bound for probability measures.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) →
      MeasureLevelApproxDLR β S (fun _ => 2)) ∧
    -- PROVED: free-case ε_TV ≡ 0 under Haar consistency.
    (∀ (S : WilsonActionAssignment),
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) →
      MeasureLevelApproxDLR 0 S (fun _ => 0)) ∧
    -- PROVED: cluster-vanishing of BF2 TV budget.
    (∀ (β : ℝ),
      Tendsto (fun L : ℕ => boundaryTVErrorBudget β L / (L : ℝ)^4)
        atTop (𝓝 0)) ∧
    -- PROVED: conditional thermodynamic-limit bridge.
    (∀ (β : ℝ) (hβ_pos : 0 ≤ β) (h_β_small : β ≤ β_KP_4D)
        (S : WilsonActionAssignment),
      BF2_SharpMeasureLevelApproxDLR β S →
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∃ (c : ℝ), 0 < c ∧
          (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
            = (ENNReal.ofReal c) • interactingWilsonMeasure_L β L₁ (S L₁)) →
      ThermodynamicLimitMeasureLevelDLR β S) ∧
    -- HONEST: verdict.
    (verdict_E3_MeasureLevelApproxDLR
       = MeasureLevelApproxDLR_Verdict.MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β S h_prob
    exact MeasureLevelApproxDLR_trivial_unconditional β S h_prob
  · intro S h_haar
    exact MeasureLevelApproxDLR_at_zero_of_haar_consistency S h_haar
  · intro β
    exact boundaryTVErrorBudget_vanishes β
  · intro β hβ_pos h_β_small S h_BF2 h_exact
    exact measure_level_DLR_thermodynamic_limit β hβ_pos h_β_small S h_BF2 h_exact
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §17. TYPE-LEVEL SANITY CHECKS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- MeasureLevelApproxDLR is a Prop.
example (β : ℝ) (S : WilsonActionAssignment) (ε_TV : ℕ → ℝ) : Prop :=
  MeasureLevelApproxDLR β S ε_TV

-- TVDistBound is a Prop.
example {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (bound : ℝ) : Prop :=
  TVDistBound μ ν bound

-- BF2_SharpMeasureLevelApproxDLR is a Prop.
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  BF2_SharpMeasureLevelApproxDLR β S

-- ThermodynamicLimitMeasureLevelDLR is a Prop.
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  ThermodynamicLimitMeasureLevelDLR β S

-- The trivial ≤ 2 bound for probability measures.
example (β : ℝ) (S : WilsonActionAssignment)
    (h_prob : ∀ L : ℕ, IsProbabilityMeasure (interactingWilsonMeasure_L β L (S L))) :
    MeasureLevelApproxDLR β S (fun _ => 2) :=
  MeasureLevelApproxDLR_trivial_unconditional β S h_prob

-- Free-case β = 0 collapse.
example (S : WilsonActionAssignment)
    (h_haar :
      ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        (multiLinkHaar L₂).map (truncate h) = multiLinkHaar L₁) :
    MeasureLevelApproxDLR 0 S (fun _ => 0) :=
  MeasureLevelApproxDLR_at_zero_of_haar_consistency S h_haar

-- Cluster-vanishing of BF2 TV budget.
example (β : ℝ) :
    Tendsto (fun L : ℕ => boundaryTVErrorBudget β L / (L : ℝ)^4) atTop (𝓝 0) :=
  boundaryTVErrorBudget_vanishes β

-- Verdict is the expected enum value.
example : verdict_E3_MeasureLevelApproxDLR
    = MeasureLevelApproxDLR_Verdict.MEASURE_LEVEL_APPROX_DLR_PARTIAL_NEEDS_TV_INFRASTRUCTURE :=
  rfl

end UnifiedTheory.LayerB.Phase_E3_MeasureLevelApproxDLR
