/-
  LayerB/Phase_E3_MediatorTest_hub15.lean

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PURPOSE — TEST THE UNIFICATION-MEDIATOR HYPOTHESIS ON HUB 15
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (2026-05-13)

  The Conjecture C (atomic-vocabulary-is-Lie-structured) was
  refuted in strong form: atomic monomials are dense in [3, 250].
  However, framework HUBS (multi-sector observables) hit Lie
  dimensions at ~3× enrichment over baseline.  The new conjecture
  in `Phase_E3_PhysicalMechanism.lean` is:

    > Cross-sector observable hubs are mediated by unification
    > groups; their representation dimensions appear in the hub.

  In particular, the catalog entry for hub 15 (Phase_E3_PhysicalMechanism
  line 101–107) names

      mediator_group  = A_3 = SU(4)
      rep_type        = adjoint   (dim su(4) = 15)
      physical_role   = "Pati-Salam SU(4) ≅ Spin(6):
                          lepton-color unification mediator"
      sectors_connected = ["lepton", "color"]

  and asserts the integer 15 appearing as the numerator of
  m_c/m_b = 15/49 is mediated by Pati-Salam SU(4).

  THIS FILE TESTS THAT CLAIM by tracing the framework's actual
  derivation of m_c/m_b = 15/49 in
  `LayerB/Phase_E3_Discovery_LeptonQuarkMasses.lean` and
  `LayerB/Phase_E3_Discovery_FermionChamberConnection.lean`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero sorry, zero custom axiom):

  PART 1.  Re-exports the framework's actual `mc_over_mb_pred`
           definition (= 15/49) and atomic factorisation
           theorems, so the derivation chain is in scope.

  PART 2.  Documents the actual derivation chain step-by-step.
           Result: the chain is purely combinatorial.  15 is
           identified with `cayleyDicksonDimSum = 1+2+4+8`,
           NOT with `dimSU4 = 4²-1`.  The two are equal by
           arithmetic but the framework's derivation goes via
           Cayley-Dickson.  Pati-Salam SU(4) is in fact
           EXCLUDED by `LayerA/BSMExclusions.lean` line 96
           (Pati-Salam SU(4)×SU(2)×SU(2) ruled out by minimality).

  PART 3.  Documents the unification-mediator hypothesis as a
           negative result for hub 15: the integer 15 appears
           in m_c/m_b for combinatorial reasons (gen_step
           prefactor) anchored to the Cayley-Dickson tower,
           not for Lie-group-mediator reasons.  The dim SU(4)
           = 15 coincidence is NOT load-bearing in the
           derivation; it is a NUMERICAL coincidence of the
           A_3 ≅ D_3 isogeny intersecting the CD sum.

  PART 4.  Verdict (NOT_SUPPORTED) + recommendation for the
           next test target (hub 8 = dim SU(3) adjoint, where
           the gluon adjoint is unambiguously physical).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HEADLINE VERDICT.  NOT_SUPPORTED for hub 15.

    The framework's derivation of m_c/m_b = 15/49 is
    `15 / disc² = 15 · gen_step` where:
      • `gen_step = 1/disc² = 1/49` is a Yukawa-rung suppression
        anchored at the J₄ chamber discriminant, NOT at any
        Lie casimir.
      • The numerator 15 is identified with the Cayley-Dickson
        dimension sum cdSum = 1+2+4+8 = realDim_ℝ + realDim_ℂ
        + realDim_ℍ + realDim_𝕆.
      • dim SU(4) = 15 ALSO equals 15, but the framework's
        derivation does NOT use SU(4) branching, Casimir,
        anomaly residue, or coset.
      • Pati-Salam (SU(4)×SU(2)×SU(2)) is EXPLICITLY EXCLUDED
        by `LayerA/BSMExclusions.lean` line 96, removing the
        physical context in which SU(4) would mediate
        lepton-color crossings.

  IMPLICATION.  The unification-mediator hypothesis fails on
  the hub 15 test.  The integer 15 = dim SU(4) appearance is
  NUMERICALLY COINCIDENT with the Pati-Salam interpretation
  but STRUCTURALLY ROUTED through the Cayley-Dickson tower
  in the framework.  This is the classical "hub coincidence"
  pitfall: equal integers, distinct derivation paths.

  Note on AMBIGUITY: there is a residual SOFT version of the
  hypothesis where the CD-sum identification IS itself a
  proxy for octonion-G_2-Spin(7)-Spin(8) Magic-Square
  structure, which Pati-Salam Spin(6) sits inside.  That soft
  version is NOT testable from this hub alone — it requires
  testing the CD-sum derivation chain itself, not the m_c/m_b
  bookkeeping.  We record this and move on.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  NEXT TEST TARGET.  Hub 8 = dim SU(3) (adjoint, gluon).

  Hub 8 is the cleanest follow-up because:
    • SU(3)_color is unambiguously physical (gluons in QCD).
    • The framework's atomic factorisation 8 = N_W·d_eff
      = 2·4 routes through (N_W, d_eff), NOT through (N_c² − 1).
    • If hub 8 ALSO factors combinatorially with no SU(3)
      branching/Casimir reference, the unification-mediator
      hypothesis fails for the strongest-physics hub, and the
      Phase_E3_PhysicalMechanism catalog should be downgraded
      to a numerical-coincidence taxonomy.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Zero sorry.  Zero custom axioms.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import UnifiedTheory.LayerB.Phase_E3_Discovery_LeptonQuarkMasses
import UnifiedTheory.LayerB.Phase_E3_Discovery_FermionChamberConnection
import UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace UnifiedTheory.LayerB.Phase_E3_MediatorTest_hub15

open UnifiedTheory.LayerB.Phase_E3_Discovery_LeptonQuarkMasses
open UnifiedTheory.LayerB.Phase_E3_Discovery_FermionChamberConnection
open UnifiedTheory.LayerB.Phase_E3_Discovery_CayleyDickson_YMGap
open UnifiedTheory.LayerB.CrossSectorIdentitySearch

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — RE-EXPORT THE FRAMEWORK'S ACTUAL m_c/m_b PREDICTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's prediction for m_c/m_b is `15 / 49`.

    Source: `Phase_E3_Discovery_LeptonQuarkMasses.lean` line 244,
    `def mc_over_mb_pred : ℚ := 15 / 49`. -/
theorem mc_over_mb_pred_value :
    mc_over_mb_pred = (15 : ℚ) / 49 := rfl

/-- The framework's atomic factorisation of m_c/m_b is `15 / disc²`.

    Source: `Phase_E3_Discovery_LeptonQuarkMasses.lean` line 274,
    `mc_over_mb_pred_atomic`. -/
theorem mc_over_mb_factorisation :
    mc_over_mb_pred = (15 : ℚ) / (atom_disc : ℚ) ^ 2 :=
  mc_over_mb_pred_atomic

/-- The framework's identification of the numerator 15 is the
    Cayley-Dickson dimension sum 1 + 2 + 4 + 8.

    Source: `Phase_E3_Discovery_FermionChamberConnection.lean`
    line 343, `mc_mb_numerator_eq_cdSum`. -/
theorem mc_mb_numerator_via_CD :
    (15 : ℚ) = (cayleyDicksonDimSum : ℚ) :=
  mc_mb_numerator_eq_cdSum

/-- Therefore m_c/m_b factors as `cdSum / disc²` atomically.

    Source: `Phase_E3_Discovery_FermionChamberConnection.lean`
    line 348, `mc_over_mb_pred_via_cd`. -/
theorem mc_over_mb_via_CD :
    mc_over_mb_pred = (cayleyDicksonDimSum : ℚ) / (atom_disc : ℚ) ^ 2 :=
  mc_over_mb_pred_via_cd

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — THE THREE 15-READOUTS (CD sum, dim SU(4), SM count)

    All three integers equal 15 BY ARITHMETIC; the framework
    proves NO derivation between them.  This is recorded
    explicitly in `Phase_E3_Discovery_CayleyDickson_YMGap.lean`
    line 357 (`three_15_readouts`) which states the equality
    of the three 15s but does NOT promote any to a "structural
    cause" of any other.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- READOUT (i): Cayley-Dickson dimension sum.
    cdSum = realDim_ℝ + realDim_ℂ + realDim_ℍ + realDim_𝕆
          = 1 + 2 + 4 + 8 = 15. -/
theorem readout_CD : cayleyDicksonDimSum = 15 :=
  cayleyDicksonDimSum_eq_15

/-- READOUT (ii): adjoint dimension of SU(4) ≅ Spin(6).
    dim SU(4) = 4² − 1 = 15. -/
theorem readout_SU4 : dimSU4 = 15 :=
  dimSU4_eq_15

/-- READOUT (iii): SM fermion count per generation.
    fermionsPerGeneration = 1·3·2 + 2·3 + 1·2 + 1 = 15. -/
theorem readout_SM : fermionsPerGeneration = 15 :=
  fermionsPerGeneration_eq_15

/-- All three readouts are equal — but BY ARITHMETIC, not by any
    derivation chain inside the framework.

    Source: `Phase_E3_Discovery_CayleyDickson_YMGap.lean` line 357,
    `three_15_readouts`. -/
theorem three_15_readouts_agree :
    cayleyDicksonDimSum = 15
    ∧ dimSU4 = 15
    ∧ fermionsPerGeneration = 15
    ∧ cayleyDicksonDimSum = dimSU4
    ∧ cayleyDicksonDimSum = fermionsPerGeneration :=
  three_15_readouts

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — THE DERIVATION TRACE (what actually happens in the
             framework when m_c/m_b = 15/49 is proved)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Step-by-step trace of the framework's actual derivation of
    m_c/m_b = 15/49.  Each entry cites a Lean file + line. -/
def derivation_trace : List String := [
  "STEP 1 [LayerB/CKMPreRegistration.lean:122-128]: " ++
    "The five framework atoms are defined as nat constants " ++
    "N_W = 2, N_c = 3, N_total = 5, d_eff = 4, disc = 7.  " ++
    "These are bookkeeping names for small integers.",
  "STEP 2 [LayerA/FermionMassesIndividual.lean]: " ++
    "Existing framework reduces every charged-fermion mass " ++
    "to a power of the J_4 eigenvalue ratio (5±√7)/18 with " ++
    "ONE OR TWO FREE EXPONENTS per sector.  m_c/m_b sits in " ++
    "the down sector and uses fitted exponents.",
  "STEP 3 [LayerB/Phase_E3_Discovery_LeptonQuarkMasses.lean:244]: " ++
    "ATOMIC SEARCH replaces the fitted exponents.  " ++
    "`def mc_over_mb_pred : ℚ := 15 / 49` is the simplest " ++
    "atomic rational landing inside 5% of the observed value " ++
    "0.305.  Match is 0.37%.",
  "STEP 4 [LayerB/Phase_E3_Discovery_LeptonQuarkMasses.lean:274]: " ++
    "`mc_over_mb_pred_atomic` proves the factorisation " ++
    "15/49 = 15 / disc² where disc = 7.  Pure rational " ++
    "arithmetic; no group theory.",
  "STEP 5 [LayerB/Phase_E3_Disc2HubAudit.lean:159,202]: " ++
    "The fraction 15/49 is identified as `15 · gen_step` " ++
    "where `gen_step = 1/disc² = 1/49` is the SHARED Yukawa-" ++
    "rung suppression for m_s/m_b, m_μ/m_τ, and m_c/m_b.  " ++
    "The 15 is a multiplicative prefactor, not a Casimir.",
  "STEP 6 [LayerB/Phase_E3_Discovery_CayleyDickson_YMGap.lean:201,343]: " ++
    "The numerator 15 is identified with " ++
    "`cayleyDicksonDimSum := 1 + 2 + 4 + 8`, the sum of " ++
    "real dimensions of ℝ, ℂ, ℍ, 𝕆 in the Cayley-Dickson " ++
    "tower.  Proof is `decide` on naturals.",
  "STEP 7 [LayerB/Phase_E3_Discovery_FermionChamberConnection.lean:343,348]: " ++
    "`mc_mb_numerator_eq_cdSum` and `mc_over_mb_pred_via_cd` " ++
    "complete the derivation: m_c/m_b = cdSum / disc².  " ++
    "This is the framework's STRUCTURAL EXPLANATION of 15.",
  "STEP 8 [LayerB/Phase_E3_Discovery_CayleyDickson_YMGap.lean:357]: " ++
    "`three_15_readouts` proves that cdSum = dimSU4 = " ++
    "fermionsPerGeneration = 15, but ONLY by arithmetic — " ++
    "the framework provides NO derivation FROM the CD tower " ++
    "TO SU(4) adjoint and NO derivation FROM dim SU(4) TO " ++
    "the m_c/m_b numerator.",
  "STEP 9 [LayerA/BSMExclusions.lean:96-97]: " ++
    "Pati-Salam SU(4)×SU(2)×SU(2) is EXPLICITLY EXCLUDED by " ++
    "the framework's minimality argument.  The physical " ++
    "context in which SU(4) would mediate lepton-color " ++
    "crossings is RULED OUT by the framework's own derivation."
]

/-- The trace has nine concrete steps (not just a sketch). -/
theorem derivation_trace_length :
    derivation_trace.length = 9 := by
  unfold derivation_trace; decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — VERDICT + NEXT TEST RECOMMENDATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Three-valued verdict for a single mediator hypothesis test. -/
inductive MediatorVerdict
  /-- The framework's derivation explicitly uses the named
      unification group's branching, Casimir, anomaly residue,
      or coset structure. -/
  | SUPPORTED
  /-- The framework's derivation is purely combinatorial /
      atomic and does NOT route through the named unification
      group, even though the integer matches. -/
  | NOT_SUPPORTED
  /-- The derivation is partially group-theoretic, partially
      combinatorial, or the named group is one of several
      isomorphic-dimension candidates. -/
  | AMBIGUOUS
  deriving DecidableEq, Repr

/-- The verdict for hub 15 (m_c/m_b numerator). -/
def mediator_test_verdict : String :=
  "NOT_SUPPORTED for hub 15.  The framework's derivation of " ++
  "m_c/m_b = 15/49 is `15 · gen_step` with 15 identified as " ++
  "the Cayley-Dickson dimension sum 1+2+4+8 (cdSum), NOT as " ++
  "dim SU(4) = 4²-1.  Pati-Salam SU(4)×SU(2)×SU(2) is in fact " ++
  "EXPLICITLY EXCLUDED in LayerA/BSMExclusions.lean line 96.  " ++
  "The catalog claim that hub 15 is `Pati-Salam SU(4) ≅ " ++
  "Spin(6): lepton-color unification mediator` is a numerical " ++
  "coincidence of dim A_3 = 15 = cdSum, not a structural " ++
  "derivation.  The dim SU(4) = cdSum coincidence is the " ++
  "classical hub-coincidence pitfall: equal integers, distinct " ++
  "paths.  A SOFT residual hypothesis (CD tower itself ⊃ " ++
  "octonion-Magic-Square structure ⊃ Spin(6) ⊃ Pati-Salam) " ++
  "is not testable from this hub alone."

/-- The verdict as a typed enum. -/
def mediator_test_verdict_enum : MediatorVerdict :=
  .NOT_SUPPORTED

/-- The next hub to test if this hub's verdict is inconclusive
    or to triangulate the hypothesis. -/
def next_test_target : String :=
  "Hub 8 = dim SU(3) (gluon adjoint).  This is the cleanest " ++
  "follow-up because SU(3)_color is unambiguously physical " ++
  "(QCD), but the framework's atomic factorisation of 8 is " ++
  "8 = N_W · d_eff = 2·4, routing through (N_W, d_eff) NOT " ++
  "through (N_c² − 1).  If the derivation chain for any " ++
  "hub-8 observable goes through gen_step or N_W·d_eff " ++
  "without referencing dim SU(3) as an adjoint, the " ++
  "unification-mediator hypothesis ALSO fails for the " ++
  "strongest-physics hub, and the Phase_E3_PhysicalMechanism " ++
  "catalog should be downgraded.  If instead it goes through " ++
  "an explicit SU(3) branching, the hypothesis is RESCUED " ++
  "for color-sector hubs and only fails for matter-sector " ++
  "hubs (15, 16).  Either outcome is informative."

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — MASTER THEOREM (PACKAGED FACTS + VERDICT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Master theorem.  Bundles:
      (i)   the framework's actual m_c/m_b prediction (15/49);
      (ii)  the atomic factorisation through disc;
      (iii) the Cayley-Dickson identification of the numerator;
      (iv)  the three-15-readouts arithmetic agreement;
      (v)   the formal verdict NOT_SUPPORTED. -/
theorem hub15_mediator_test_master :
    -- (i)
    mc_over_mb_pred = (15 : ℚ) / 49
    -- (ii)
    ∧ mc_over_mb_pred = (15 : ℚ) / (atom_disc : ℚ) ^ 2
    -- (iii)
    ∧ mc_over_mb_pred = (cayleyDicksonDimSum : ℚ) / (atom_disc : ℚ) ^ 2
    -- (iv)  three readouts
    ∧ (cayleyDicksonDimSum = 15
       ∧ dimSU4 = 15
       ∧ fermionsPerGeneration = 15
       ∧ cayleyDicksonDimSum = dimSU4
       ∧ cayleyDicksonDimSum = fermionsPerGeneration)
    -- (v)  verdict
    ∧ mediator_test_verdict_enum = MediatorVerdict.NOT_SUPPORTED := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mc_over_mb_pred_value
  · exact mc_over_mb_factorisation
  · exact mc_over_mb_via_CD
  · exact three_15_readouts_agree
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    DOCUMENTATION FOOTER

    HONEST INTERPRETATION.

    The framework SUCCEEDS at producing m_c/m_b = 15/49 within
    0.4 % of the observed PDG value.  That is a genuine, sub-1 %
    cross-sector match using only the five-letter atomic alphabet.

    The unification-mediator hypothesis is a SEPARATE claim:
    that the integer 15 appearing in this match is mediated by
    Pati-Salam SU(4) ≅ Spin(6) for lepton-color crossings.

    This file shows that hypothesis FAILS for hub 15.  The
    framework's derivation routes the 15 through the Cayley-
    Dickson tower, not through Pati-Salam branching.  And
    Pati-Salam itself is excluded by the framework's
    minimality argument (LayerA/BSMExclusions).

    The result is HONEST and the failure is INFORMATIVE: it
    tells us that the integer-coincidence interpretation
    stands for hub 15.  The mediator catalog in
    Phase_E3_PhysicalMechanism, which lists 17 such hubs,
    should be tested EACH ONE INDIVIDUALLY before accepting
    its taxonomy.  The next-natural test is hub 8 (gluon
    adjoint), where the physics is unambiguous and the
    derivation chain — if it routes through SU(3) branching
    — would directly refute this null result.

    Zero sorry.  Zero custom axioms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.Phase_E3_MediatorTest_hub15
