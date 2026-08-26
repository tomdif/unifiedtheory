/-
  Audit/KFGate6PhysicalBoundaryAudit.lean

  GATE-6 PHYSICAL-BOUNDARY AUDIT

  The existing Hayden--Preskill specialization asks every dimensional setup
  to satisfy the Hayden gap.  That domain condition is false for a concrete
  valid setup, so the specialization is uninhabited.  This file records the
  counterexample rather than allowing downstream conditional capstones to
  hide the contradiction.

  The harmonic binary QQG readout is also checked against the viability
  window already declared by `QQGViableParameters`.  Both of its explicit
  scenarios have matter weight one and therefore lie outside the declared
  interval `[10^5, 10^6]`.

  Finally, `Gate6PhysicalHaydenPreskillFrontier` states the shape of the
  genuinely missing physical bridge using typed dynamics and recovery-channel
  data.  No inhabitant is constructed: arithmetic bounds and zero-valued
  proxy witnesses do not prove scrambling, trace-norm decoupling, or CPTP
  recovery for selected microscopic dynamics.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout
import UnifiedTheory.Audit.KFTOESevenGateAttack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate6PhysicalBoundaryAudit

open UnifiedTheory.LayerC.HaydenPreskill
open UnifiedTheory.Cosmology.QQG
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout

/-! ## 1. The current all-setups Hayden-gap bridge is impossible -/

/-- A valid Hayden--Preskill dimensional setup whose diary dimension exceeds
the product of the new-radiation and black-hole dimensions. -/
def haydenGapCounterexample : HPSetup where
  k := 2
  N := 1
  e := 1
  r := 1
  k_pos := by norm_num
  N_pos := by norm_num
  e_pos := by norm_num
  r_pos := by norm_num
  r_le_N := by norm_num
  hPagePast := by norm_num

theorem haydenGapCounterexample_not :
    ¬ HaydenGap haydenGapCounterexample := by
  norm_num [HaydenGap, haydenGapCounterexample]

/-- The current microscopic-evaporation bridge is uninhabited because its
`recoveryTargetAndHaydenGap` field requires the Hayden gap for every `HPSetup`,
including `haydenGapCounterexample`. -/
theorem gate6_haydenPreskillMicroscopicEvaporationBridgeClosed_uninhabited :
    ¬ Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed := by
  intro h
  exact haydenGapCounterexample_not
    (h.recoveryTargetAndHaydenGap haydenGapCounterexample).2

/-! ## 2. The binary QQG records are outside the declared viable window -/

/-- A scenario is in the repository's declared QQG viability window when its
derived 't Hooft coupling and matter weight are realized by an inhabitant of
`QQGViableParameters`.  Referring to that structure keeps this audit tied to
the actual bounds instead of duplicating numerical constants locally. -/
def QQGScenarioInDeclaredViabilityWindow (S : QQGScenario) : Prop :=
  ∃ V : QQGViableParameters,
    V.lam_tH = S.lam_tH ∧ V.N_matter = S.N

theorem qqgScenarioInDeclaredViabilityWindow_bounds
    {S : QQGScenario} (h : QQGScenarioInDeclaredViabilityWindow S) :
    (1 : ℝ) / 10 ≤ S.lam_tH ∧
      S.lam_tH ≤ 1 ∧
        (100000 : ℝ) ≤ S.N ∧ S.N ≤ 1000000 := by
  rcases h with ⟨V, hLam, hN⟩
  exact
    ⟨by simpa [hLam] using V.lam_tH_ge_tenth,
      by simpa [hLam] using V.lam_tH_le_one,
      by simpa [hN] using V.N_matter_lower,
      by simpa [hN] using V.N_matter_upper⟩

theorem binaryQQGLowScenario_not_in_declared_viability_window :
    ¬ QQGScenarioInDeclaredViabilityWindow binaryQQGLowScenario := by
  intro h
  have hLower :=
    (qqgScenarioInDeclaredViabilityWindow_bounds h).2.2.1
  norm_num [binaryQQGLowScenario] at hLower

theorem binaryQQGHighScenario_not_in_declared_viability_window :
    ¬ QQGScenarioInDeclaredViabilityWindow binaryQQGHighScenario := by
  intro h
  have hLower :=
    (qqgScenarioInDeclaredViabilityWindow_bounds h).2.2.1
  norm_num [binaryQQGHighScenario] at hLower

/-! ## 3. Honest typed physical frontier -/

universe u v

/-- Data and evidence required for a physical Hayden--Preskill bridge at one
selected setup.  The predicates are parameters so that a caller must first
fix their concrete microscopic, trace-norm, and channel semantics.  In
particular, this record cannot be filled merely by choosing zero real-valued
deviation or recovery-error proxies.

No constructor theorem is supplied in this module. -/
structure Gate6PhysicalHaydenPreskillFrontier
    (Dynamics : Type u)
    (RecoveryChannel : Type v)
    (scrambles : Dynamics → HPSetup → Prop)
    (traceNormDecouples : Dynamics → HPSetup → Prop)
    (isCPTP : RecoveryChannel → Prop)
    (recovers : RecoveryChannel → Dynamics → HPSetup → Prop) where
  setup : HPSetup
  setupHasHaydenGap : HaydenGap setup
  selectedDynamics : Dynamics
  selectedDynamicsScrambles : scrambles selectedDynamics setup
  selectedDynamicsTraceNormDecouples :
    traceNormDecouples selectedDynamics setup
  recoveryChannel : RecoveryChannel
  recoveryChannelIsCPTP : isCPTP recoveryChannel
  recoveryChannelRecoversSelectedDynamics :
    recovers recoveryChannel selectedDynamics setup

#print axioms haydenGapCounterexample_not
#print axioms gate6_haydenPreskillMicroscopicEvaporationBridgeClosed_uninhabited
#print axioms qqgScenarioInDeclaredViabilityWindow_bounds
#print axioms binaryQQGLowScenario_not_in_declared_viability_window
#print axioms binaryQQGHighScenario_not_in_declared_viability_window

end UnifiedTheory.Audit.KFGate6PhysicalBoundaryAudit
