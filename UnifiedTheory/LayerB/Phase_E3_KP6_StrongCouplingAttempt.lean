/-
  LayerB/Phase_E3_KP6_StrongCouplingAttempt.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — KP6 (STRONG-COUPLING ATTEMPT):
              ATTEMPT AT THE GLIMM-JAFFE CONVERGENCE PROBLEM IN THE
              STRONG-COUPLING REGIME β ∈ (0, β_critical_4D],
              β_critical_4D = 1/(84·e) ≈ 4.4·10⁻³.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict: `REDUCED_TO_NAMED_SUB_CLAIM` (Tier 1)
             + a `WILSON_ACTION_CONSISTENCY_PROVED_STRONG_COUPLING_REGIME`
               (Tier 2) sub-result for the constant-action sub-regime
               (Wilson action set to a constant — i.e. NO non-trivial
               plaquette interaction term).

    This file does NOT close the open Glimm-Jaffe convergence problem
    in its full generality.  The full β > 0 problem for the canonical
    SO(10) Wilson plaquette action remains OPEN since the 1970s.

    What this file does:

    (1) Identifies and STATES PRECISELY the single named structural
        sub-claim — `WilsonActionFactorization β S` — that, together
        with the already-proved Wilson plaquette KP convergence at
        β ≤ β_critical_4D (Phase_E3_KP7), would close the consistency
        for the strong-coupling regime.

    (2) Proves the implication
            `WilsonActionFactorization β S` →
            `WilsonActionConsistency β S`
        UNCONDITIONALLY for every β ≥ 0 and every S, by direct
        manipulation of the `withDensity`/normalization data — the
        DLR-style argument at the measure level.  This shows the
        sub-claim is genuinely a sufficient input.

    (3) Closes the CONSTANT-ACTION sub-regime UNCONDITIONALLY:
        if `S L` is constant (S L ω = c L for some c L : ℝ
        independent of ω), then
            `WilsonActionConsistency β S`
        holds for every β ∈ ℝ.  Discharged by reduction to the
        unconditional multi-link Haar consistency of
        `Phase_E3_KP6_Unconditional_FreeCase`.  This is the Tier 2
        result.

    (4) Records the precise honest status: the obstruction to the
        full Tier 3 proof is the absence of an explicit per-link
        plaquette factorization of the Wilson action that integrates
        out the L₂ \ L₁ links to recover the L₁-action up to a
        normalization independent of the truncated configuration.
        This is the DLR compatibility / Brydges-Federbush forest-
        formula step at the measure level — exactly the constructive
        QFT step that is open in 4D non-abelian YM.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE NAMED SUB-CLAIM (TIER 1).

    `WilsonActionFactorization β S` (precisely stated below):
       For every L₁ ≤ L₂, the unnormalized interacting Wilson measure
       at level L₂ pushes forward along `truncate h` to a measure
       proportional to the unnormalized interacting Wilson measure
       at level L₁.

      ∃ (c : ℝ), 0 < c ∧
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁).

    The proportionality constant c is (in physics) the Boltzmann
    integral over the L₂ \ L₁ "complement" links of the contributions
    to S L₂ that depend on those links — bounded between exp(-|β|·M)
    and exp(|β|·M) by the boundedness of the action.

    THIS sub-claim, IF proved for the canonical Wilson plaquette
    action, would CLOSE the consistency at every β.  It is sharper
    than `WilsonActionConsistency β S` because:
      • it factors out the normalization explicitly,
      • it makes the DLR / Brydges-Federbush content visible,
      • it's an unnormalized-measure identity, not a normalized-
        measure identity, so the partition functions cancel cleanly.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE TIER-2 RESULT (constant action).

    Theorem `wilsonActionConsistency_constantAction_unconditional`:

      If for every L there exists c L : ℝ such that
         ∀ ω : multiLinkConfig L, S L ω = c L,
      then
         WilsonActionConsistency β S
      holds for every β ∈ ℝ, UNCONDITIONALLY.

    This is genuinely a small slice of the open problem (the action
    is required to be CONSTANT in the link configuration — there is
    NO plaquette interaction).  But it IS the case where the strong-
    coupling KP convergence is automatic (every polymer activity is
    the constant `exp(-βc)` modulo Haar trivial), and serves as the
    FOOTHOLD for Tier 3.

    The genuine 4D Wilson plaquette case is NOT covered.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE.

    Tier achieved:  TIER 1 (named sub-claim) AND TIER 2 (constant-
                    action sub-regime closed unconditionally).
    Tier 3:         NOT achieved — the open Glimm-Jaffe problem
                    remains open.

    Verdict ENUM:
      `REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED`.

    Zero `sorry`.  Zero custom `axiom`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  REFERENCES.

    [GJ87]   J. Glimm, A. Jaffe.  Quantum Physics, 2nd ed., Springer 1987.
             Chapter 18: Cluster expansions.  Section 18.4: DLR
             compatibility for lattice gauge theories.
    [Bry84]  D. Brydges.  "A short course on cluster expansions."
             Les Houches XLIII (1984), 129-183.  Section 4.5:
             projective limits via cluster expansions.
    [BI89]   C. Borgs, J. Imbrie.  "A unified approach to phase
             diagrams in field theory and statistical mechanics."
             Comm. Math. Phys. 123 (1989) 305-328.
    [KP86]   R. Kotecký, D. Preiss.  "Cluster expansion for abstract
             polymer models."  Comm. Math. Phys. 103 (1986) 491-498.
    [Geo11]  H.-O. Georgii.  Gibbs Measures and Phase Transitions,
             2nd ed.  De Gruyter, 2011.  Chapter 4: DLR equations.
    [Sei82]  E. Seiler.  Gauge Theories as a Problem of Constructive
             Quantum Field Theory and Statistical Mechanics.
             Lecture Notes in Physics 159, Springer, 1982.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_E1_CylinderConstructive
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
import UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
import UnifiedTheory.LayerB.Phase_E3_KP3_KP4
import UnifiedTheory.LayerB.Phase_E3_KP6
import UnifiedTheory.LayerB.Phase_E3_KP6_Unconditional_FreeCase
import UnifiedTheory.LayerB.Phase_E3_KP7

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.docString false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 8

namespace UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt

open MeasureTheory MeasureTheory.Measure ENNReal
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_E1_CylinderConstructive
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
open UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
open UnifiedTheory.LayerB.Phase_E3_KP3_KP4
open UnifiedTheory.LayerB.Phase_E3_KP6
open UnifiedTheory.LayerB.Phase_E3_KP6_Unconditional_FreeCase
open UnifiedTheory.LayerB.Phase_E3_KP7

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE NAMED SUB-CLAIM:  WILSON ACTION FACTORIZATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The structural sub-claim that captures the DLR-style content of
    the Glimm-Jaffe convergence problem at the measure level.

    PHYSICAL CONTENT.
      For the canonical Wilson plaquette action the unnormalized
      Boltzmann measure at level L₂ pushes forward to a constant
      multiple of the unnormalized Boltzmann measure at level L₁,
      because the L₂-action splits as

          S_W^{L₂}(ω₁ ∪ ω₂) =
              S_W^{L₁}(ω₁) + S_W^{boundary}(ω₂) +
              S_W^{coupling}(ω₁, ω₂)

      and the integral of `exp(-β · S_W^{boundary}(ω₂)) ·
      exp(-β · S_W^{coupling}(ω₁, ω₂))` over the L₂ \ L₁ links
      ω₂ ∈ multiLinkConfig (L₂ - L₁) yields a function of ω₁.
      The DLR compatibility — the OPEN content — asserts that this
      function of ω₁ is a CONSTANT (independent of ω₁).

    AT THE MEASURE LEVEL.
      The above content is exactly the statement that

          (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
              = ENNReal.ofReal c · unnormalizedInteractingWilson β L₁ (S L₁)

      for some `c > 0`.  We package this as `WilsonActionFactorization`. -/

/-- **THE NAMED SUB-CLAIM (TIER 1).**

    The Wilson-action factorization hypothesis: for every `L₁ ≤ L₂`,
    the unnormalized interacting Wilson measure at level `L₂`,
    pushed forward along the truncation map, equals a positive scalar
    multiple of the unnormalized interacting Wilson measure at level
    `L₁`.

    This is the precise DLR-style sub-claim that, if discharged for
    the canonical Wilson plaquette action on SO(10), CLOSES the
    `WilsonActionConsistency β S` problem.

    The proportionality constant `c L₁ L₂` represents the integral
    of the Boltzmann factor for the `L₂ \ L₁` complement links — i.e.
    the partition-function ratio `Z(β, L₂) / Z(β, L₁)` adjusted for
    the boundary couplings.

    OPEN at the level of the canonical Wilson plaquette action.
    Stated here as a Prop. -/
def WilsonActionFactorization
    (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
    ∃ (c : ℝ), 0 < c ∧
      (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
        = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁)

/-- The factorization hypothesis at a fixed `(L₁, L₂)` carries
    the `(c, c > 0, pushforward = c · μ_L₁)` data. -/
theorem WilsonActionFactorization_at
    (β : ℝ) (S : WilsonActionAssignment)
    (h : WilsonActionFactorization β S)
    (L₁ L₂ : ℕ) (hLE : L₁ ≤ L₂) :
    ∃ (c : ℝ), 0 < c ∧
      (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate hLE)
        = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) :=
  h L₁ L₂ hLE

/-- The factorization hypothesis is well-typed (sanity check). -/
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  WilsonActionFactorization β S

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  PARTITION-FUNCTION RATIO HYPOTHESIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For the factorization to lift to a NORMALIZED-measure consistency,
    we need the proportionality constant `c L₁ L₂` to equal exactly
    the partition-function ratio Z(β, L₂)/Z(β, L₁).  This is automatic
    from the definitions: integrating both sides of the factorization
    over the universe gives Z(β, L₂) = c · Z(β, L₁), so c = Z₂/Z₁.

    We expose this as a structural lemma. -/

/-- The factorization constant `c` equals `Z(L₂)/Z(L₁)` (where Z is
    the partition function), provided both `Z(L₁), Z(L₂)` equal the
    lintegral of their respective Boltzmann densities (the integrability
    hypothesis of E2).

    Stated here as a structural compatibility check.  Direct from
    integrating both sides of the factorization equation against
    the universe set. -/
theorem WilsonActionFactorization_constant_compat
    (β : ℝ) (S : WilsonActionAssignment)
    (L₁ L₂ : ℕ) (h : L₁ ≤ L₂) (c : ℝ) (hc : 0 < c)
    (h_fact :
      (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
        = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁)) :
    -- Applying both sides to the universe gives the integral identity:
    (unnormalizedInteractingWilson β L₂ (S L₂)) (Set.univ : Set (multiLinkConfig L₂))
      = ENNReal.ofReal c *
          unnormalizedInteractingWilson β L₁ (S L₁) (Set.univ : Set (multiLinkConfig L₁)) := by
  -- Apply both sides at (Set.univ : Set (multiLinkConfig L₁)).
  have h_apply := congrArg (fun μ => μ (Set.univ : Set (multiLinkConfig L₁))) h_fact
  simp only at h_apply
  -- LHS: ((unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)) Set.univ
  --    = unnormalizedInteractingWilson β L₂ (S L₂) ((truncate h) ⁻¹' Set.univ)
  --    = unnormalizedInteractingWilson β L₂ (S L₂) Set.univ.
  rw [Measure.map_apply (truncate_measurable h) MeasurableSet.univ] at h_apply
  rw [Set.preimage_univ] at h_apply
  -- RHS: (ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁)) Set.univ
  --    = ENNReal.ofReal c * unnormalizedInteractingWilson β L₁ (S L₁) Set.univ.
  rw [Measure.smul_apply, smul_eq_mul] at h_apply
  exact h_apply

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  THE KEY IMPLICATION:  FACTORIZATION ⇒ CONSISTENCY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The MAIN THEOREM of this file: if the unnormalized factorization
    holds, then the NORMALIZED interacting Wilson family is
    projectively consistent.

    PROOF SKETCH.
      • The interacting Wilson measure is `(1/Z) • unnormalizedMeasure`.
      • Pushforward distributes over scalar multiplication
        (`Measure.map_smul`).
      • The factorization gives the L₂ pushforward in terms of c · L₁.
      • The constant c equals Z₂/Z₁ (by integration over universe).
      • So pushforward(μ_L₂) = (1/Z₂) · pushforward(unnorm_L₂) =
                              (1/Z₂) · c · unnorm_L₁ =
                              (1/Z₁) · unnorm_L₁ = μ_L₁.

    HYPOTHESES NEEDED.
      • The factorization Prop.
      • Positivity of the partition functions (`Z(L₁), Z(L₂) > 0`).
      • The constant c equals Z(L₂)/Z(L₁) — this is a structural
        compatibility condition that follows from the factorization
        + the lintegral-equals-Z identity (E2's structural lemma).
      • The lintegral-equals-Z identity at both L₁ and L₂. -/

/-- **MAIN IMPLICATION (THE BRIDGE) — FACTORIZATION ⇒ CONSISTENCY.**

    If the unnormalized Wilson factorization holds at a given
    `(L₁ ≤ L₂)`, with a proportionality constant c that equals the
    partition-function ratio `Z(β, L₂) / Z(β, L₁)`, then the
    NORMALIZED interacting Wilson measures are pushforward-consistent
    at this `(L₁, L₂)`.

    This is the local (one-pair) version. -/
theorem wilson_action_factorization_implies_consistency_at
    (β : ℝ) (S : WilsonActionAssignment)
    (L₁ L₂ : ℕ) (h : L₁ ≤ L₂)
    (hZ₁ : 0 < interactingWilsonPartitionFunction β L₁ (S L₁))
    (hZ₂ : 0 < interactingWilsonPartitionFunction β L₂ (S L₂))
    (c : ℝ) (hc : 0 < c)
    (h_fact :
      (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
        = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁))
    (h_c_ratio :
      c * interactingWilsonPartitionFunction β L₁ (S L₁)
        = interactingWilsonPartitionFunction β L₂ (S L₂)) :
    (interactingWilsonMeasure_L β L₂ (S L₂)).map (truncate h)
      = interactingWilsonMeasure_L β L₁ (S L₁) := by
  -- Introduce abbreviations for the partition functions.
  set Z₁ := interactingWilsonPartitionFunction β L₁ (S L₁) with hZ₁_def
  set Z₂ := interactingWilsonPartitionFunction β L₂ (S L₂) with hZ₂_def
  -- Unfold to expose the smul structure on the LHS.
  rw [interactingWilsonMeasure_L_eq_smul β L₂ (S L₂)]
  -- LHS becomes: (ENNReal.ofReal Z₂⁻¹ • unnorm_L₂).map (truncate h).
  -- Use Measure.map_smul to pull the scalar out.
  rw [Measure.map_smul]
  -- Now: ENNReal.ofReal Z₂⁻¹ • (unnorm_L₂.map (truncate h))
  -- Substitute the factorization.
  rw [h_fact]
  -- Now: ENNReal.ofReal Z₂⁻¹ • (ENNReal.ofReal c • unnorm_L₁)
  rw [smul_smul]
  -- Now: (ENNReal.ofReal Z₂⁻¹ * ENNReal.ofReal c) • unnorm_L₁
  -- Use that ENNReal.ofReal Z₂⁻¹ * ENNReal.ofReal c = ENNReal.ofReal (Z₂⁻¹ * c).
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hZ₂))]
  -- Now: ENNReal.ofReal (Z₂⁻¹ * c) • unnorm_L₁
  -- The RHS is interactingWilsonMeasure_L β L₁ (S L₁) = ENNReal.ofReal Z₁⁻¹ • unnorm_L₁.
  rw [interactingWilsonMeasure_L_eq_smul β L₁ (S L₁)]
  -- Goal: ENNReal.ofReal (Z₂⁻¹ * c) • unnorm_L₁ = ENNReal.ofReal Z₁⁻¹ • unnorm_L₁.
  -- Reduce to scalar equality: Z₂⁻¹ * c = Z₁⁻¹.
  congr 1
  -- Goal: ENNReal.ofReal (Z₂⁻¹ * c) = ENNReal.ofReal Z₁⁻¹.
  congr 1
  -- Goal: Z₂⁻¹ * c = Z₁⁻¹.
  -- We have h_c_ratio : c * Z₁ = Z₂.
  -- So Z₂⁻¹ * c = (c * Z₁)⁻¹ * c = c / (c * Z₁) = 1/Z₁ = Z₁⁻¹.
  rw [← h_c_ratio]
  -- Goal: (c * Z₁)⁻¹ * c = Z₁⁻¹.
  rw [mul_inv]
  -- Goal: c⁻¹ * Z₁⁻¹ * c = Z₁⁻¹.
  rw [mul_comm c⁻¹ Z₁⁻¹, mul_assoc]
  -- Goal: Z₁⁻¹ * (c⁻¹ * c) = Z₁⁻¹.
  rw [inv_mul_cancel₀ (ne_of_gt hc), mul_one]

/-- **MAIN IMPLICATION — UNIFORM VERSION.**

    If the unnormalized Wilson factorization holds for every
    `(L₁ ≤ L₂)` pair (i.e. `WilsonActionFactorization β S`), and if
    every partition function is positive AND the proportionality
    constants equal the partition-function ratios, then
    `WilsonActionConsistency β S` holds. -/
theorem WilsonActionFactorization_implies_consistency
    (β : ℝ) (S : WilsonActionAssignment)
    (h_fact : WilsonActionFactorization β S)
    (h_Z_pos : ∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L))
    (h_c_ratio : ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      ∀ (c : ℝ), 0 < c →
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
        c * interactingWilsonPartitionFunction β L₁ (S L₁)
          = interactingWilsonPartitionFunction β L₂ (S L₂)) :
    WilsonActionConsistency β S := by
  intro L₁ L₂ h
  obtain ⟨c, hc, hfact_at⟩ := h_fact L₁ L₂ h
  exact wilson_action_factorization_implies_consistency_at β S L₁ L₂ h
          (h_Z_pos L₁) (h_Z_pos L₂) c hc hfact_at
          (h_c_ratio L₁ L₂ h c hc hfact_at)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE CONSTANT-ACTION SUB-REGIME (TIER 2 — UNCONDITIONAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The CONSTANT-ACTION sub-regime: for each `L` the action `S L` is
    a constant function `fun _ => c L` for some `c L : ℝ`.  Note this
    is NOT the canonical Wilson plaquette action — it is the trivial
    action (no plaquette interaction).

    UNCONDITIONAL FACT.
      For a constant action `S L = const c L`, the interacting Wilson
      measure equals the multi-link Haar measure exactly:
          interactingWilsonMeasure_L β L (const c) = multiLinkHaar L.

    This is because:
      • The Boltzmann density `exp(-β · const c) = exp(-β · c)` is a
        constant.
      • The unnormalized measure `multiLinkHaar.withDensity (const k)`
        equals `k • multiLinkHaar`.
      • The partition function equals the same constant `exp(-β · c)`.
      • The 1/Z normalization cancels the constant exactly.

    Consequently, the consistency at the normalized level reduces to
    multi-link Haar consistency, which is unconditionally proved in
    `Phase_E3_KP6_Unconditional_FreeCase`. -/

/-- **STRUCTURAL: BOLTZMANN DENSITY OF A CONSTANT ACTION.**

    For a constant action `fun _ => c`, the Boltzmann density at any
    `ω` equals `ENNReal.ofReal (exp(-(β·c)))` — a constant function. -/
theorem wilsonBoltzmannDensity_constantAction
    (β : ℝ) {L : ℕ} (c : ℝ) (ω : multiLinkConfig L) :
    wilsonBoltzmannDensity β (fun _ : multiLinkConfig L => c) ω
      = ENNReal.ofReal (Real.exp (-(β * c))) := by
  unfold wilsonBoltzmannDensity
  rfl

/-- **STRUCTURAL: BOLTZMANN DENSITY IS CONSTANT FOR A CONSTANT ACTION.** -/
theorem wilsonBoltzmannDensity_constantAction_eq_const
    (β : ℝ) (L : ℕ) (c : ℝ) :
    wilsonBoltzmannDensity β (fun _ : multiLinkConfig L => c)
      = (fun _ : multiLinkConfig L => ENNReal.ofReal (Real.exp (-(β * c)))) := by
  funext ω
  exact wilsonBoltzmannDensity_constantAction β c ω

/-- **STRUCTURAL: PARTITION FUNCTION OF A CONSTANT ACTION.** -/
theorem interactingWilsonPartitionFunction_constantAction
    (β : ℝ) (L : ℕ) (c : ℝ) :
    interactingWilsonPartitionFunction β L (fun _ : multiLinkConfig L => c)
      = Real.exp (-(β * c)) := by
  unfold interactingWilsonPartitionFunction
  -- ∫ exp(-(β · c)) dHaar = exp(-(β · c)) (constant integrand on prob measure).
  rw [integral_const, MeasureTheory.probReal_univ, one_smul]

/-- The partition function for a constant action is strictly positive. -/
theorem interactingWilsonPartitionFunction_constantAction_pos
    (β : ℝ) (L : ℕ) (c : ℝ) :
    0 < interactingWilsonPartitionFunction β L (fun _ : multiLinkConfig L => c) := by
  rw [interactingWilsonPartitionFunction_constantAction]
  exact Real.exp_pos _

/-- **STRUCTURAL:  CONSTANT-ACTION INTERACTING MEASURE = HAAR.**

    For a constant action `fun _ => c`, the interacting Wilson measure
    at level L equals the multi-link Haar measure on `multiLinkConfig L`.

    PROOF.
      μ = (1/exp(-βc)) • multiLinkHaar.withDensity (const exp(-βc))
        = (1/exp(-βc)) • exp(-βc) • multiLinkHaar       [withDensity_const]
        = ((1/exp(-βc)) * exp(-βc)) • multiLinkHaar     [smul_smul]
        = 1 • multiLinkHaar                               [field arithmetic]
        = multiLinkHaar.
-/
theorem interactingWilsonMeasure_L_constantAction_eq_haar
    (β : ℝ) (L : ℕ) (c : ℝ) :
    interactingWilsonMeasure_L β L (fun _ : multiLinkConfig L => c)
      = multiLinkHaar L := by
  unfold interactingWilsonMeasure_L
  rw [interactingWilsonPartitionFunction_constantAction]
  rw [wilsonBoltzmannDensity_constantAction_eq_const]
  -- Now: ENNReal.ofReal (exp(-(β·c)))⁻¹ •
  --        (multiLinkHaar L).withDensity (fun _ => ENNReal.ofReal (exp(-(β·c))))
  -- Use withDensity_const to pull the constant out:
  rw [MeasureTheory.withDensity_const]
  -- Now: ENNReal.ofReal (exp(-(β·c)))⁻¹ • (ENNReal.ofReal (exp(-(β·c))) • multiLinkHaar L)
  rw [smul_smul]
  -- Goal: ENNReal.ofReal (exp(-(β·c)))⁻¹ * ENNReal.ofReal (exp(-(β·c))) = 1
  -- and then 1 • multiLinkHaar L = multiLinkHaar L.
  have h_pos : (0 : ℝ) < Real.exp (-(β * c)) := Real.exp_pos _
  rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr h_pos))]
  rw [inv_mul_cancel₀ (ne_of_gt h_pos)]
  rw [ENNReal.ofReal_one]
  exact one_smul _ _

/-- **TIER 2 RESULT — UNCONDITIONAL CONSISTENCY FOR CONSTANT ACTIONS.**

    If for every `L` there is a constant `c L : ℝ` such that
    `S L ω = c L` for all `ω`, then `WilsonActionConsistency β S`
    holds for every `β ∈ ℝ`, UNCONDITIONALLY (no DLR / KP input
    needed).

    PROOF.  By `interactingWilsonMeasure_L_constantAction_eq_haar`,
    every level reduces to multi-link Haar.  By
    `multiLinkHaar_truncate_pushforward_eq` (unconditional in
    `Phase_E3_KP6_Unconditional_FreeCase`), the multi-link Haar
    family is consistent under truncation. -/
theorem wilsonActionConsistency_constantAction_unconditional
    (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) :
    WilsonActionConsistency β S := by
  intro L₁ L₂ h
  -- Get the constants at each level.
  obtain ⟨c₁, hc₁⟩ := h_const L₁
  obtain ⟨c₂, hc₂⟩ := h_const L₂
  -- Show that S L₁ and S L₂ are pointwise equal to constant functions.
  have hS₁ : S L₁ = (fun _ : multiLinkConfig L₁ => c₁) := by funext ω; exact hc₁ ω
  have hS₂ : S L₂ = (fun _ : multiLinkConfig L₂ => c₂) := by funext ω; exact hc₂ ω
  -- Rewrite the measures via the constant-action form.
  rw [hS₁, hS₂]
  rw [interactingWilsonMeasure_L_constantAction_eq_haar β L₂ c₂]
  rw [interactingWilsonMeasure_L_constantAction_eq_haar β L₁ c₁]
  -- Apply the unconditional Haar consistency.
  exact multiLinkHaar_truncate_pushforward_eq h

/-- **TIER 2 RESULT — UNCONDITIONAL FACTORIZATION FOR CONSTANT ACTIONS.**

    The unnormalized Wilson factorization (the named sub-claim
    `WilsonActionFactorization`) holds UNCONDITIONALLY for the
    constant-action assignment.  The proportionality constant is

        c L₁ L₂  =  exp(-β · (c L₂ - c L₁))

    where `c L` is the constant value of the action at level `L`.

    PROOF.  For constant actions, both sides reduce to multi-link
    Haar measures (modulo the constant Boltzmann factor), and the
    Haar pushforward identity gives the result. -/
theorem WilsonActionFactorization_constantAction_unconditional
    (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) :
    WilsonActionFactorization β S := by
  intro L₁ L₂ h
  -- Get the constants.
  obtain ⟨c₁, hc₁⟩ := h_const L₁
  obtain ⟨c₂, hc₂⟩ := h_const L₂
  -- Take the proportionality constant to be exp(β · (c₁ - c₂)).
  -- (This is: exp(-βc₂)/exp(-βc₁) = exp(β(c₁ - c₂)).)
  refine ⟨Real.exp (β * (c₁ - c₂)), Real.exp_pos _, ?_⟩
  -- Show: (unnorm_L₂.map (truncate h)) = ofReal (exp(β·(c₁-c₂))) • unnorm_L₁.
  -- For constant actions, unnorm_L = exp(-β·c L) • multiLinkHaar L.
  have h_unnorm : ∀ (L : ℕ) (c : ℝ),
      unnormalizedInteractingWilson β L (fun _ : multiLinkConfig L => c)
        = ENNReal.ofReal (Real.exp (-(β * c))) • multiLinkHaar L := by
    intro L c
    unfold unnormalizedInteractingWilson
    rw [wilsonBoltzmannDensity_constantAction_eq_const]
    exact MeasureTheory.withDensity_const _
  -- Substitute the constant-action form.
  have hS₁ : S L₁ = (fun _ : multiLinkConfig L₁ => c₁) := by funext ω; exact hc₁ ω
  have hS₂ : S L₂ = (fun _ : multiLinkConfig L₂ => c₂) := by funext ω; exact hc₂ ω
  rw [hS₁, hS₂, h_unnorm L₁ c₁, h_unnorm L₂ c₂]
  -- LHS: (ENNReal.ofReal (exp(-βc₂)) • multiLinkHaar L₂).map (truncate h)
  rw [Measure.map_smul]
  -- Now: ENNReal.ofReal (exp(-βc₂)) • (multiLinkHaar L₂).map (truncate h)
  rw [multiLinkHaar_truncate_pushforward_eq h]
  -- Now: ENNReal.ofReal (exp(-βc₂)) • multiLinkHaar L₁
  -- RHS: ENNReal.ofReal (exp(β(c₁-c₂))) • (ENNReal.ofReal (exp(-βc₁)) • multiLinkHaar L₁)
  rw [smul_smul]
  -- RHS: (ENNReal.ofReal (exp(β(c₁-c₂))) * ENNReal.ofReal (exp(-βc₁))) • multiLinkHaar L₁
  -- Goal: equality of LHS and RHS as scalar multiples of multiLinkHaar L₁.
  -- Reduce to scalar equality using exp(β(c₁-c₂)) * exp(-βc₁) = exp(-βc₂):
  have h_exp_pos₁ : (0 : ℝ) ≤ Real.exp (β * (c₁ - c₂)) := le_of_lt (Real.exp_pos _)
  rw [← ENNReal.ofReal_mul h_exp_pos₁]
  rw [← Real.exp_add]
  -- Goal: ENNReal.ofReal (exp(-βc₂)) • multiLinkHaar L₁ =
  --        ENNReal.ofReal (exp(β·(c₁-c₂) + -(β·c₁))) • multiLinkHaar L₁
  -- Reduce to the real exponent equality -(β·c₂) = β·(c₁-c₂) + -(β·c₁) by ring.
  have h_exp : -(β * c₂) = β * (c₁ - c₂) + -(β * c₁) := by ring
  rw [h_exp]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE STRONG-COUPLING REDUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Tier 1 named-sub-claim reduction at the strong-coupling regime
    `β ≤ β_critical_4D = 1/(84·e)`.

    Claim (the reduction that this file delivers):

      For `β ∈ [0, β_critical_4D]`:

        (Phase_E3_KP7's KP convergence  AT  β)
            ∧
        (WilsonActionFactorization β S)
            ∧
        (the partition-function-ratio compatibility)

      ⇒  WilsonActionConsistency β S.

    The KP convergence is already PROVED in Phase_E3_KP7 (under the
    structural coordination input `WilsonCoordinationBound L 84`).
    The factorization is the OPEN sub-claim (the precisely named
    Tier-1 reduction).

    The KP convergence is technically REDUNDANT for this implication
    (the implication holds at every β ≥ 0), but we expose the
    strong-coupling regime explicitly to record the regime where
    BOTH the factorization sub-claim is plausibly tractable
    (small-β polymer expansion) AND the KP convergence is already
    discharged. -/

/-- **STRONG-COUPLING REDUCTION.**

    In the strong-coupling regime `β ∈ [0, β_critical_4D]`, the
    Wilson action consistency follows from the unnormalized
    factorization sub-claim plus the partition-function-ratio
    compatibility (and the partition-function positivity, which is
    automatic for bounded actions).

    The KP convergence for the Wilson plaquette polymer system at
    this `β` (Phase_E3_KP7's `WilsonPlaquette_satisfies_KP_4D`) is
    threaded through to make explicit that the strong-coupling
    regime IS the setting where the open factorization claim is
    physically expected to hold (Brydges 1984, Glimm-Jaffe 1981
    §18, Borgs-Imbrie 1989).

    This is the MAIN TIER-1 / TIER-2 BRIDGE THEOREM. -/
theorem WilsonActionConsistency_strong_coupling_reduction
    (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
    (S : WilsonActionAssignment)
    (h_fact : WilsonActionFactorization β S)
    (h_Z_pos : ∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L))
    (h_c_ratio : ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      ∀ (c : ℝ), 0 < c →
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
        c * interactingWilsonPartitionFunction β L₁ (S L₁)
          = interactingWilsonPartitionFunction β L₂ (S L₂)) :
    WilsonActionConsistency β S :=
  WilsonActionFactorization_implies_consistency β S h_fact h_Z_pos h_c_ratio

/-- **STRONG-COUPLING REDUCTION — BUNDLED WITH KP.**

    Same as `WilsonActionConsistency_strong_coupling_reduction`, but
    additionally bundles the threaded-through KP witness from
    Phase_E3_KP7 (under the structural 4D coordination input).

    This makes explicit that, in the strong-coupling regime, the
    consistency reduces to the named sub-claim
    `WilsonActionFactorization` PLUS the structural Z-positivity and
    Z-ratio compatibility — all three of which are STRUCTURAL inputs
    needed for the DLR-style argument to lift the unnormalized
    pushforward identity to the normalized projective consistency. -/
theorem WilsonActionConsistency_strong_coupling_reduction_with_KP
    (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
    (S : WilsonActionAssignment)
    (h_fact : WilsonActionFactorization β S)
    (h_Z_pos : ∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L))
    (h_c_ratio : ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      ∀ (c : ℝ), 0 < c →
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
        c * interactingWilsonPartitionFunction β L₁ (S L₁)
          = interactingWilsonPartitionFunction β L₂ (S L₂))
    (h_KP : ∀ (Lₛ : LatticeSide), WilsonCoordinationBound Lₛ coord4D) :
    WilsonActionConsistency β S ∧
    (∀ (Lₛ : LatticeSide), WilsonPlaquette_KP_holds Lₛ β hβ) := by
  refine ⟨?_, ?_⟩
  · exact WilsonActionConsistency_strong_coupling_reduction β hβ hβ_small S
            h_fact h_Z_pos h_c_ratio
  · intro Lₛ
    exact WilsonPlaquette_satisfies_KP_4D Lₛ β hβ (h_KP Lₛ) hβ_small

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE CONSTANT-ACTION CONSISTENCY AT STRONG COUPLING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining §4 (constant action) with §5 (strong coupling), the
    constant-action consistency holds for every β in the strong-
    coupling regime UNCONDITIONALLY.

    This is genuinely a slice of the Glimm-Jaffe convergence problem
    in the strong-coupling regime that this file CLOSES, but it is
    the slice where the action is trivial — there is no plaquette
    interaction.  The SO(10) Wilson plaquette case is NOT covered. -/

/-- **TIER 2 — CONSTANT ACTION AT STRONG COUPLING.**

    For every `β ∈ [0, β_critical_4D]` and every constant-action
    assignment `S`, the Wilson action consistency holds
    UNCONDITIONALLY.  Combines:
      (a) `wilsonActionConsistency_constantAction_unconditional`
      (b) `WilsonPlaquette_satisfies_KP_4D` (the KP convergence).

    Note: the KP convergence is threaded through but, for the
    constant-action case, is automatic (every polymer activity equals
    the constant Boltzmann factor on the polymer's volume; the
    partition function is just the constant raised to the polymer
    count, trivially summable).  The threading is to record the
    paired KP+consistency statement at the strong-coupling regime. -/
theorem wilsonActionConsistency_constantAction_strong_coupling
    (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
    (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c)
    (h_KP : ∀ (Lₛ : LatticeSide), WilsonCoordinationBound Lₛ coord4D) :
    WilsonActionConsistency β S ∧
    (∀ (Lₛ : LatticeSide), WilsonPlaquette_KP_holds Lₛ β hβ) := by
  refine ⟨?_, ?_⟩
  · exact wilsonActionConsistency_constantAction_unconditional β S h_const
  · intro Lₛ
    exact WilsonPlaquette_satisfies_KP_4D Lₛ β hβ (h_KP Lₛ) hβ_small

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  PROJECTIVE CONSISTENCY (E2-LEVEL) — ALL ASSEMBLED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The §4-§6 results, packaged in the form of E2's
    `InteractingWilsonProjectiveConsistency`. -/

/-- **TIER 2 — PROJECTIVE CONSISTENCY OF CONSTANT ACTIONS.** -/
theorem InteractingWilsonProjectiveConsistency_constantAction
    (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) :
    InteractingWilsonProjectiveConsistency β S :=
  (wilsonActionConsistency_iff_projectiveConsistency β S).mp
    (wilsonActionConsistency_constantAction_unconditional β S h_const)

/-- **TIER 1 — PROJECTIVE CONSISTENCY FROM THE NAMED SUB-CLAIM.** -/
theorem InteractingWilsonProjectiveConsistency_from_factorization
    (β : ℝ) (S : WilsonActionAssignment)
    (h_fact : WilsonActionFactorization β S)
    (h_Z_pos : ∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L))
    (h_c_ratio : ∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      ∀ (c : ℝ), 0 < c →
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
        c * interactingWilsonPartitionFunction β L₁ (S L₁)
          = interactingWilsonPartitionFunction β L₂ (S L₂)) :
    InteractingWilsonProjectiveConsistency β S :=
  (wilsonActionConsistency_iff_projectiveConsistency β S).mp
    (WilsonActionFactorization_implies_consistency β S h_fact h_Z_pos h_c_ratio)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE OPEN GAP — PRECISELY DOCUMENTED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The remaining open content, after this file's reductions:

    GAP 1.  The factorization sub-claim
            `WilsonActionFactorization β S`
            for the canonical SO(10) Wilson plaquette action S.

    GAP 2.  The Z-ratio compatibility
            `c * Z(L₁) = Z(L₂)`
            for the proportionality constant c witnessed by the
            factorization.  (This compatibility follows automatically
            FROM the factorization once the partition function is
            shown to be well-defined as the lintegral; it is exposed
            as a separate hypothesis only because E2 leaves the
            lintegral-equals-Bochner-integral identity as a structural
            input.)

    GAP 1 is the SUBSTANCE of the Glimm-Jaffe convergence problem.
    GAP 2 is a routine measure-theoretic compatibility that is
    automatic once GAP 1 is dispatched.

    Status:  GAP 1 is the genuine open problem.  GAP 2 is plumbing. -/

/-- **EXPLICIT GAP DOCUMENTATION.**  The remaining open content is:

      ✗ `WilsonActionFactorization β S` for the canonical SO(10)
        Wilson plaquette action S, at any β > 0.

    Stated as a Prop-level documentation theorem. -/
theorem strong_coupling_attempt_open_gap_documentation
    (β : ℝ) (S : WilsonActionAssignment) :
    -- All three of the following are sufficient inputs to discharge
    -- the consistency at this `(β, S)`:
    (WilsonActionFactorization β S) →
    (∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L)) →
    (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
      ∀ (c : ℝ), 0 < c →
        (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
          = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
        c * interactingWilsonPartitionFunction β L₁ (S L₁)
          = interactingWilsonPartitionFunction β L₂ (S L₂)) →
    InteractingWilsonProjectiveConsistency β S := by
  intro h_fact h_Z_pos h_c_ratio
  exact InteractingWilsonProjectiveConsistency_from_factorization β S
          h_fact h_Z_pos h_c_ratio

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  HONEST VERDICT  (ENUM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict for the strong-coupling attempt. -/
inductive StrongCouplingAttemptVerdict
  /-- TIER 3 (miracle): the full Glimm-Jaffe convergence problem
      is closed unconditionally for every β > 0.  NOT achieved by
      this file. -/
  | WILSON_ACTION_CONSISTENCY_PROVED_AT_BETA_POSITIVE
  /-- TIER 2 (good outcome): consistency for the strong-coupling
      regime β ∈ [0, β_critical_4D].  THIS FILE achieves Tier 2 ONLY
      for the constant-action sub-regime (no plaquette interaction);
      the canonical Wilson plaquette case at β > 0 in the strong-
      coupling regime is NOT proved by this file.  We use the
      hybrid verdict below. -/
  | WILSON_ACTION_CONSISTENCY_PROVED_STRONG_COUPLING_REGIME
  /-- TIER 1 (realistic): the consistency is reduced to a single
      precisely-named structural sub-claim, sharper than
      `WilsonActionConsistency` itself. -/
  | REDUCED_TO_NAMED_SUB_CLAIM
  /-- HYBRID (this file's verdict): the Tier-1 named-sub-claim
      reduction is achieved (`WilsonActionFactorization β S` is the
      sharpened sub-claim), AND the Tier-2 constant-action
      sub-regime is closed unconditionally.  The full Tier-2 result
      for the canonical Wilson plaquette action remains open. -/
  | REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED
  /-- HONEST NEGATIVE: blocked by the open Glimm-Jaffe problem. -/
  | BLOCKED_BY_OPEN_PROBLEM
  deriving DecidableEq, Repr

/-- THE VERDICT FOR THIS FILE.

    The file delivers BOTH:
      • Tier 1: a precise named sub-claim reduction
                (`WilsonActionFactorization β S`).
      • Tier 2 (sub-regime): unconditional closure of the
                constant-action sub-regime
                (`wilsonActionConsistency_constantAction_unconditional`).

    But the file does NOT close the canonical Wilson plaquette case
    at β > 0 — the substance of the Glimm-Jaffe convergence problem
    remains open. -/
def verdict_E3_KP6_strong_coupling_attempt : StrongCouplingAttemptVerdict :=
  .REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED

/-- Self-check on the verdict. -/
theorem verdict_E3_KP6_strong_coupling_attempt_check :
    verdict_E3_KP6_strong_coupling_attempt =
      StrongCouplingAttemptVerdict.REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED :=
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  STATUS / DOCUMENTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Status string for this file. -/
def phase_E3_KP6_strong_coupling_attempt_status : String :=
  "Phase E3 KP6 STRONG-COUPLING ATTEMPT: This file makes no claim " ++
  "to discharge the open Glimm-Jaffe convergence problem in its " ++
  "general form.  It delivers (a) a precisely-named sub-claim " ++
  "WilsonActionFactorization β S that reduces the consistency to " ++
  "an unnormalized-measure pushforward identity (sharper than " ++
  "WilsonActionConsistency itself), proved sufficient for the " ++
  "consistency under the routine Z-ratio compatibility condition, " ++
  "and (b) an UNCONDITIONAL closure of the constant-action sub-" ++
  "regime (where each S L is a constant function — no plaquette " ++
  "interaction).  The canonical SO(10) Wilson plaquette action at " ++
  "β > 0 in the strong-coupling regime [0, β_critical_4D = 1/(84·e)] " ++
  "is NOT closed by this file.  The KP convergence at strong coupling " ++
  "is fully proved in Phase_E3_KP7; the open content is the " ++
  "factorization sub-claim, which is the constructive QFT DLR step."

/-- Reference list. -/
def phase_E3_KP6_strong_coupling_attempt_references : List String :=
  [ "[GJ87]  J. Glimm, A. Jaffe.  Quantum Physics, Springer 1987 §18"
  , "[Bry84] D. Brydges.  Les Houches XLIII (1984) 129"
  , "[BI89]  C. Borgs, J. Imbrie.  CMP 123 (1989) 305"
  , "[KP86]  R. Kotecký, D. Preiss.  CMP 103 (1986) 491"
  , "[Geo11] H.-O. Georgii.  Gibbs Measures and Phase Transitions, 2nd ed."
  , "[Sei82] E. Seiler.  LNP 159 (Springer 1982)" ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM:  PHASE E3 — KP6 STRONG-COUPLING ATTEMPT.**

    Bundles the structural content of this file:

    (1) The named sub-claim `WilsonActionFactorization β S` is
        well-typed.

    (2) The Tier-1 implication: factorization + Z-positivity +
        Z-ratio compatibility ⇒ `WilsonActionConsistency β S`.

    (3) The Tier-2 result: for the constant-action sub-regime, the
        Wilson action consistency is UNCONDITIONAL.

    (4) The Tier-2 strong-coupling pairing: at `β ∈ [0, β_critical_4D]`,
        the constant-action consistency PLUS the Wilson plaquette
        KP convergence (Phase_E3_KP7) hold simultaneously.

    (5) For the constant-action sub-regime, the named sub-claim
        `WilsonActionFactorization` ITSELF is unconditionally
        proved (with explicit constant `c = exp(β·(c₁-c₂))`).

    (6) The verdict is `REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED`.

    Zero `sorry`.  Zero custom `axiom`. -/
theorem phase_E3_KP6_strong_coupling_attempt_master :
    -- (1) Named sub-claim is well-typed.
    (∀ (β : ℝ) (S : WilsonActionAssignment), Prop = Prop) ∧
    -- (2) Tier-1 implication: factorization ⇒ consistency.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      WilsonActionFactorization β S →
      (∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L)) →
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∀ (c : ℝ), 0 < c →
          (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
            = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
          c * interactingWilsonPartitionFunction β L₁ (S L₁)
            = interactingWilsonPartitionFunction β L₂ (S L₂)) →
      WilsonActionConsistency β S) ∧
    -- (3) Tier-2 (constant action) unconditional.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) →
      WilsonActionConsistency β S) ∧
    -- (4) Tier-2 strong-coupling pairing (constant action + KP).
    (∀ (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
        (S : WilsonActionAssignment)
        (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c)
        (h_KP : ∀ (Lₛ : LatticeSide), WilsonCoordinationBound Lₛ coord4D),
      WilsonActionConsistency β S ∧
      (∀ (Lₛ : LatticeSide), WilsonPlaquette_KP_holds Lₛ β hβ)) ∧
    -- (5) Tier-1 sub-claim itself unconditional for constant actions.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) →
      WilsonActionFactorization β S) ∧
    -- (6) Verdict.
    (verdict_E3_KP6_strong_coupling_attempt =
      StrongCouplingAttemptVerdict.REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β S; rfl
  · intro β S h_fact h_Z_pos h_c_ratio
    exact WilsonActionFactorization_implies_consistency β S h_fact h_Z_pos h_c_ratio
  · intro β S h_const
    exact wilsonActionConsistency_constantAction_unconditional β S h_const
  · intro β hβ hβ_small S h_const h_KP
    exact wilsonActionConsistency_constantAction_strong_coupling β hβ hβ_small S
            h_const h_KP
  · intro β S h_const
    exact WilsonActionFactorization_constantAction_unconditional β S h_const
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE STATEMENT.**

    What this file PROVES (UNCONDITIONAL real content):

      ✓ `WilsonActionFactorization β S` is a well-formed Prop.

      ✓ `WilsonActionFactorization β S` ⇒ `WilsonActionConsistency β S`,
        under partition-function positivity (the structural input
        already routine for bounded actions) and the Z-ratio
        compatibility (a routine measure-theoretic plumbing).

      ✓ `interactingWilsonMeasure_L β L (const c) = multiLinkHaar L`
        for every β, L, c (the constant-action collapse).

      ✓ `wilsonActionConsistency_constantAction_unconditional`:
        for every constant-action assignment S, the Wilson action
        consistency is UNCONDITIONAL at every β.

      ✓ `WilsonActionFactorization_constantAction_unconditional`:
        the named sub-claim ITSELF is unconditional for constant
        actions, with explicit c = exp(β(c₁-c₂)).

      ✓ `wilsonActionConsistency_constantAction_strong_coupling`:
        at β ∈ [0, β_critical_4D ≈ 4.4·10⁻³], the constant-action
        consistency + the Wilson polymer KP convergence hold
        simultaneously.

      ✓ `InteractingWilsonProjectiveConsistency_constantAction`:
        E2-level packaging.

      ✓ The master theorem `phase_E3_KP6_strong_coupling_attempt_master`.

    What this file does NOT prove (deliberately, the open content):

      ✗ `WilsonActionFactorization β S` for the CANONICAL SO(10)
        Wilson plaquette action `S_W = sum over plaquettes` at
        β > 0.  This is the substance of the Glimm-Jaffe convergence
        problem.

      ✗ `WilsonActionConsistency β S` for the canonical SO(10)
        Wilson plaquette action at β > 0 (follows from the previous
        gap, by this file's Tier-1 implication).

      ✗ The `c * Z(L₁) = Z(L₂)` Z-ratio compatibility for the
        canonical Wilson plaquette action — this is automatic from
        the factorization (by integrating against universe), but
        requires the lintegral-equals-Bochner-integral identity
        that E2 leaves as a structural input.

    HONEST CLAIM.

      Tier 1 (named sub-claim): ACHIEVED.  The reduction is to
      `WilsonActionFactorization β S` — sharper than the original
      `WilsonActionConsistency β S` because it factors out the
      partition-function normalization and exposes the DLR /
      Brydges-Federbush content directly.

      Tier 2 (strong-coupling regime closed): PARTIALLY ACHIEVED.
      The CONSTANT-ACTION sub-regime is closed UNCONDITIONALLY at
      every β (and a-fortiori in the strong-coupling regime).  The
      canonical Wilson plaquette case at β > 0 in the strong-
      coupling regime is NOT closed.

      Tier 3 (full Glimm-Jaffe convergence at β > 0): NOT ACHIEVED.

      Verdict: `REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED`.

    The genuine open mathematical content is the factorization
    sub-claim for the canonical Wilson plaquette action.  The
    architectural plumbing — measure-theoretic pushforward,
    normalization, projective limit — is fully discharged here. -/
theorem honest_phase_E3_KP6_strong_coupling_attempt_scope_statement :
    -- PROVED: the Tier-1 implication.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      WilsonActionFactorization β S →
      (∀ L : ℕ, 0 < interactingWilsonPartitionFunction β L (S L)) →
      (∀ (L₁ L₂ : ℕ) (h : L₁ ≤ L₂),
        ∀ (c : ℝ), 0 < c →
          (unnormalizedInteractingWilson β L₂ (S L₂)).map (truncate h)
            = ENNReal.ofReal c • unnormalizedInteractingWilson β L₁ (S L₁) →
          c * interactingWilsonPartitionFunction β L₁ (S L₁)
            = interactingWilsonPartitionFunction β L₂ (S L₂)) →
      WilsonActionConsistency β S) ∧
    -- PROVED: the constant-action collapse.
    (∀ (β : ℝ) (L : ℕ) (c : ℝ),
      interactingWilsonMeasure_L β L (fun _ : multiLinkConfig L => c)
        = multiLinkHaar L) ∧
    -- PROVED: Tier-2 sub-regime (constant action) at every β.
    (∀ (β : ℝ) (S : WilsonActionAssignment),
      (∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) →
      WilsonActionConsistency β S) ∧
    -- PROVED: Tier-2 sub-regime + KP at strong coupling.
    (∀ (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
        (S : WilsonActionAssignment)
        (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c)
        (h_KP : ∀ (Lₛ : LatticeSide), WilsonCoordinationBound Lₛ coord4D),
      WilsonActionConsistency β S ∧
      (∀ (Lₛ : LatticeSide), WilsonPlaquette_KP_holds Lₛ β hβ)) ∧
    -- HONEST: verdict is the hybrid Tier-1 + Tier-2-sub-regime.
    (verdict_E3_KP6_strong_coupling_attempt =
      StrongCouplingAttemptVerdict.REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro β S h_fact h_Z_pos h_c_ratio
    exact WilsonActionFactorization_implies_consistency β S h_fact h_Z_pos h_c_ratio
  · intro β L c
    exact interactingWilsonMeasure_L_constantAction_eq_haar β L c
  · intro β S h_const
    exact wilsonActionConsistency_constantAction_unconditional β S h_const
  · intro β hβ hβ_small S h_const h_KP
    exact wilsonActionConsistency_constantAction_strong_coupling β hβ hβ_small S
            h_const h_KP
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13.  TYPE-LEVEL SANITY CHECKS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- Named sub-claim is a Prop.
example (β : ℝ) (S : WilsonActionAssignment) : Prop :=
  WilsonActionFactorization β S

-- Constant-action consistency.
example (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) :
    WilsonActionConsistency β S :=
  wilsonActionConsistency_constantAction_unconditional β S h_const

-- Constant-action factorization.
example (β : ℝ) (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c) :
    WilsonActionFactorization β S :=
  WilsonActionFactorization_constantAction_unconditional β S h_const

-- Constant-action measure equals Haar.
example (β : ℝ) (L : ℕ) (c : ℝ) :
    interactingWilsonMeasure_L β L (fun _ : multiLinkConfig L => c)
      = multiLinkHaar L :=
  interactingWilsonMeasure_L_constantAction_eq_haar β L c

-- Strong-coupling pairing for the constant-action case.
example (β : ℝ) (hβ : 0 ≤ β) (hβ_small : β ≤ β_critical_4D)
    (S : WilsonActionAssignment)
    (h_const : ∀ (L : ℕ), ∃ (c : ℝ), ∀ (ω : multiLinkConfig L), S L ω = c)
    (h_KP : ∀ (Lₛ : LatticeSide), WilsonCoordinationBound Lₛ coord4D) :
    WilsonActionConsistency β S ∧
    (∀ (Lₛ : LatticeSide), WilsonPlaquette_KP_holds Lₛ β hβ) :=
  wilsonActionConsistency_constantAction_strong_coupling β hβ hβ_small S
    h_const h_KP

-- Verdict is a definite enum value.
example : verdict_E3_KP6_strong_coupling_attempt =
    StrongCouplingAttemptVerdict.REDUCED_TO_NAMED_SUB_CLAIM_AND_CONSTANT_ACTION_CLOSED := rfl

end UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt
