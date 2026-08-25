/-
  Audit/KFGate5ChamberScatteringPremiseRemoval.lean

  Remove the redundant chamber `ScatteringConstruction` premise from the
  strongest current Gate 5 closure route.

  `KFTOESevenGateAttack` asks a caller to provide
  `S : ScatteringConstruction C` to its named Haag-Ruelle/spin-statistics
  bridge.  But `Clay2_HaagRuelleConstruction` already constructs the canonical
  chamber witness `chamberScatteringConstruction C` for every finite causal
  set.  The theorems below compose those two files, so the caller need only
  provide the still-open continuum spin-statistics lift.

  Scope is deliberately exact: this removes a chamber-level witness premise.
  The existing witness is a noncomputable set-theoretic parametrization of the
  three-dimensional chamber, not a substrate-derived continuum scattering
  theory.  No claim about full Haag-Ruelle dynamics or spin-statistics is made.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOESevenGateAttack
import UnifiedTheory.LayerB.Clay2_HaagRuelleConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate5ChamberScatteringPremiseRemoval

universe u v w z t

open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFGate5OctonionS6ComplexBridge
open UnifiedTheory.LayerA.CausalFoundation
open UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
open UnifiedTheory.LayerB.Clay2_HaagRuelleConstruction

/-- The chamber scattering witness required by the old Gate 5 bridge is
already inhabited for every finite causal set. -/
theorem gate5_chamberScatteringConstruction_nonempty
    (C : CausalSet) [Fintype C.Event] :
    Nonempty (ScatteringConstruction C) :=
  chamberScatteringConstruction_exists C

/-- The exact W7 chamber outputs used by the Gate 5 bridge, with no supplied
`ScatteringConstruction`. -/
theorem gate5_chamberW7_without_scattering_input
    (C : CausalSet) [Fintype C.Event] :
    (∀ ψ : ChamberState,
        ∃ s : ℝ, (chamberScatteringConstruction C).inWavePacket s = ψ) ∧
      (∀ ψ : ChamberState,
        ∃ s : ℝ, (chamberScatteringConstruction C).outWavePacket s = ψ) ∧
        (∃ s : ℝ,
          (chamberScatteringConstruction C).inWavePacket s = Ω_chamber) ∧
          (∃ s : ℝ,
            (chamberScatteringConstruction C).outWavePacket s = Ω_chamber) :=
  W7_chamber_unconditional C

/-- Premise-removing version of the named Gate 5 Haag-Ruelle bridge.  The
chamber scattering object is derived; only the continuum spin-statistics lift
remains a hypothesis. -/
theorem gate5_haagRuelleSpinStatisticsBridge_closed_without_scattering_input
    (C : CausalSet) [Fintype C.Event]
    (T : Gate5HaagRuelleSpinStatisticsBridgeTargets)
    (hSpinStatistics : T.qftSpinStatisticsLift) :
    Gate5HaagRuelleSpinStatisticsBridgeClosed
      (chamberScatteringConstruction C) T := by
  exact
    gate5_haagRuelleSpinStatisticsBridge_closed
      (chamberScatteringConstruction C) T hSpinStatistics

/-- Strongest current named-continuum-bridge Gate 5 closure with the redundant
`ScatteringConstruction` input removed.  The Hilbert/QFT bridge, continuum
spin-statistics proposition, and Yang-Mills/Higgs/renormalization bridge remain
explicit because none follows from chamber cardinality. -/
theorem gate5_qftStandardModelIR_closed_of_namedContinuumBridges_without_scattering_input
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (C : CausalSet) [Fintype C.Event]
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    (THilbert : Gate5OctonionS6ComplexGeometryBridgeTargets)
    (TSpin : Gate5HaagRuelleSpinStatisticsBridgeTargets)
    (TGauge : Gate5YangMillsHiggsRenormalizationBridgeTargets)
    (hHilbertBridge : Gate5OctonionS6ComplexGeometryBridgeClosed THilbert)
    (hSpinStatistics : TSpin.qftSpinStatisticsLift)
    (hGaugeBridge : Gate5YangMillsHiggsRenormalizationBridgeClosed TGauge) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
        fA fB F G THilbert.complexGeometryFeedsConstructiveQFTLimit
        TSpin.qftSpinStatisticsLift TGauge.qftGaugeRenormalizationLift) := by
  exact
    gate5_qftStandardModelIR_closed_of_namedContinuumBridgesAndFiniteAudits
      fA fB hA hB F G (chamberScatteringConstruction C)
      THilbert TSpin TGauge hHilbertBridge
      (gate5_haagRuelleSpinStatisticsBridge_closed_without_scattering_input
        C TSpin hSpinStatistics)
      hGaugeBridge

#print axioms gate5_chamberScatteringConstruction_nonempty
#print axioms gate5_chamberW7_without_scattering_input
#print axioms gate5_haagRuelleSpinStatisticsBridge_closed_without_scattering_input
#print axioms gate5_qftStandardModelIR_closed_of_namedContinuumBridges_without_scattering_input

end UnifiedTheory.Audit.KFGate5ChamberScatteringPremiseRemoval
