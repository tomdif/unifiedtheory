/-
  Audit/KFTOEFullClosureTarget.lean

  Top-level TOE closure target assembled from the seven-gate ledger and the
  microscopic Gate 3/4 supplier interface.

  This file does not claim the missing physical inputs are proved.  It states
  the exact Lean-facing package that would close the current seven-gate TOE
  ledger once those inputs are supplied.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEFullClosureTarget

open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
open UnifiedTheory.Audit.KFTOESevenGateAttack

/-- The seven-gate TOE target record after the microscopic Gate 3/4 handoff is
made explicit.  Gate 3 is represented by the exact-recovery certificate
induced by the named microscopic supplier, while Gates 1, 2, 4, 5, 6, and 7
retain their existing ledger targets. -/
structure TOEClosureTargets : Type where
  gate1Targets : Gate1MicroscopicLawTargets
  gate2Targets : Gate2HauptvermutungSemanticTargets
  gate3ExactRecovery : Prop
  gate4Targets : Gate4HorizonEinsteinAnalyticTargets
  gate5Targets : Gate5QFTStandardModelIRTargets
  gate6Targets : Gate6CosmologyBlackHoleTargets
  gate7Targets : Gate7ExternalTestTargets

/-- The repo's current formal meaning of "full TOE closed": each of the seven
ledger gates has its corresponding closure certificate. -/
structure TOEClosureClosed
    (T : TOEClosureTargets) : Prop where
  gate1Closed : Gate1MicroscopicLawClosed T.gate1Targets
  gate2Closed : Gate2HauptvermutungSemanticClosed T.gate2Targets
  gate3Closed : T.gate3ExactRecovery
  gate4Closed : Gate4HorizonEinsteinAnalyticClosed T.gate4Targets
  gate5Closed : Gate5QFTStandardModelIRClosed T.gate5Targets
  gate6Closed : Gate6CosmologyBlackHoleClosed T.gate6Targets
  gate7Closed : Gate7ExternalTestClosed T.gate7Targets

/-- Build the full TOE target from one named microscopic Gate 4
scheduled-kernel supplier plus the remaining abstract Gate 1, Gate 2, Gate 5,
Gate 6, and Gate 7 targets.  The Gate 4 headline target keeps its four still
external analytic/physical inputs named separately. -/
noncomputable def microscopicTOEClosureTargets
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    (gate1Targets : Gate1MicroscopicLawTargets)
    (gate2Targets : Gate2HauptvermutungSemanticTargets)
    (gate5Targets : Gate5QFTStandardModelIRTargets)
    (gate6Targets : Gate6CosmologyBlackHoleTargets)
    (gate7Targets : Gate7ExternalTestTargets)
    (horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop) :
    TOEClosureTargets where
  gate1Targets := gate1Targets
  gate2Targets := gate2Targets
  gate3ExactRecovery :=
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        G.gate3)
  gate4Targets :=
    microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargets
      G horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics
  gate5Targets := gate5Targets
  gate6Targets := gate6Targets
  gate7Targets := gate7Targets

/-- Full TOE target specialized to the finite-spectrum Gate 2 semantics
already supplied by the quantized residual counters inside the microscopic
Gate 4 supplier. -/
noncomputable def microscopicTOEClosureTargetsWithQuantizedGate2
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    (gate1Targets : Gate1MicroscopicLawTargets)
    (gate5Targets : Gate5QFTStandardModelIRTargets)
    (gate6Targets : Gate6CosmologyBlackHoleTargets)
    (gate7Targets : Gate7ExternalTestTargets)
    (horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop) :
    TOEClosureTargets :=
  microscopicTOEClosureTargets G gate1Targets
    (gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum)
    gate5Targets gate6Targets gate7Targets
    horizonEstimatorConvergence physicalScheduledDensity
    bdgKernelProfileCertificate nullBalanceFromDynamics

/-- Top-level closure theorem: after the microscopic Gate 4 scheduled-kernel
supplier is provided, the full TOE ledger reduces exactly to Gate 1, Gate 2,
the four remaining Gate 4 analytic/physical inputs, Gate 5, Gate 6, and Gate 7
closure certificates. -/
theorem microscopicTOEClosureTargets_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate2Targets : Gate2HauptvermutungSemanticTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {gate7Targets : Gate7ExternalTestTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hgate2 : Gate2HauptvermutungSemanticClosed gate2Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets)
    (hgate7 : Gate7ExternalTestClosed gate7Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargets G gate1Targets gate2Targets
        gate5Targets gate6Targets gate7Targets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics) := by
  exact
    ⟨hgate1, hgate2,
      gate3_exactRecoveryCertificate_closed
        (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
          G.gate3),
      microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed
        G hhorizon hscheduled hkernel hnull,
      hgate5, hgate6, hgate7⟩

/-- Full-closure theorem specialized to the quantized-residual Gate 2 semantic
target.  Compared with `microscopicTOEClosureTargets_closed`, this removes the
separate Gate 2 closure hypothesis: the named microscopic supplier provides it
by projection. -/
theorem microscopicTOEClosureTargetsWithQuantizedGate2_closed
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {gate7Targets : Gate7ExternalTestTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets)
    (hgate7 : Gate7ExternalTestClosed gate7Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithQuantizedGate2
        G gate1Targets gate5Targets gate6Targets gate7Targets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics) := by
  simpa [microscopicTOEClosureTargetsWithQuantizedGate2] using
    microscopicTOEClosureTargets_closed
      G hgate1
      (microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed
        G)
      hhorizon hscheduled hkernel hnull hgate5 hgate6 hgate7

/-- Same full-closure theorem with the current preregistration ledger used for
Gate 7.  The future empirical outcomes are still not asserted here; this only
uses the repository's closed protocol layer. -/
theorem microscopicTOEClosureTargets_closed_with_preRegistrationLedger
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate2Targets : Gate2HauptvermutungSemanticTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hgate2 : Gate2HauptvermutungSemanticClosed gate2Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargets G gate1Targets gate2Targets
        gate5Targets gate6Targets gate7PreRegistrationLedgerTargets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics) := by
  exact
    microscopicTOEClosureTargets_closed
      G hgate1 hgate2 hhorizon hscheduled hkernel hnull hgate5 hgate6
      gate7_externalTests_closed_from_preRegistrationLedger

/-- Quantized-residual Gate 2 plus the current preregistration ledger: the
remaining full-TOE closure hypotheses are now Gate 1, the four Gate 4
analytic/physical assumptions, Gate 5, and Gate 6. -/
theorem microscopicTOEClosureTargetsWithQuantizedGate2_closed_with_preRegistrationLedger
    {ι X Y chart : Type*} [Fintype ι]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
    {stepFloor weightBase sourceBase countGap curvatureGap spectralGap : ℝ}
    {chartCertificate :
      ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart}
    {fixedScale densityBase densityStep : ℝ}
    {coord : Y → Fin 4 → ℝ}
    {chartOfCell : ι → chart}
    {sampleEvent : ℕ → ι → X}
    {phiAtPoint curvaturePhi : ℝ}
    {operatorKernelData : BDG4DOperatorProfileKernelSplitData}
    {errorScale : ℝ}
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithQuantizedGate2
        G gate1Targets gate5Targets gate6Targets
        gate7PreRegistrationLedgerTargets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics) := by
  exact
    microscopicTOEClosureTargetsWithQuantizedGate2_closed
      G hgate1 hhorizon hscheduled hkernel hnull hgate5 hgate6
      gate7_externalTests_closed_from_preRegistrationLedger

end UnifiedTheory.Audit.KFTOEFullClosureTarget
