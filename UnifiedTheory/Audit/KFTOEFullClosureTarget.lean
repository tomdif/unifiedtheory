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
open UnifiedTheory.Audit.KFCausalCSpecArakiHorizonRelativeEntropy
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Cosmology.QQG

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

/-- Full TOE target specialized to both quantized-residual Gate 2 semantics
and the finite recovered-carrier cover-independence part of Gate 5. -/
noncomputable def microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F H : ProjectiveQubitCarrierField site)
    (gate1Targets : Gate1MicroscopicLawTargets)
    (gate6Targets : Gate6CosmologyBlackHoleTargets)
    (gate7Targets : Gate7ExternalTestTargets)
    (horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop) :
    TOEClosureTargets :=
  microscopicTOEClosureTargetsWithQuantizedGate2 G gate1Targets
    (gate5QFTStandardModelIRTargetsOfFiniteCarrierCover
      fA fB F H effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain)
    gate6Targets gate7Targets
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

/-- Full-closure theorem with quantized-residual Gate 2 and finite
recovered-carrier Gate 5 cover-independence supplied.  The remaining Gate 5
inputs are exactly the effective Hilbert/QFT limit, propagators and
spin-statistics, gauge/renormalization, and Standard-Model parameter chain. -/
theorem microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5_closed
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F H : ProjectiveQubitCarrierField site)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {gate7Targets : Gate7ExternalTestTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets)
    (hgate7 : Gate7ExternalTestClosed gate7Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5
        G fA fB F H gate1Targets gate6Targets gate7Targets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain) := by
  exact
    microscopicTOEClosureTargetsWithQuantizedGate2_closed
      G hgate1 hhorizon hscheduled hkernel hnull
      (gate5_qftStandardModelIR_closed_of_finiteCarrierCover
        fA fB hA hB F H heffective hpropagators hgauge hparameters)
      hgate6 hgate7

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

/-- Quantized Gate 2, finite recovered-carrier Gate 5 cover-independence, and
the current preregistration ledger: the remaining full-TOE closure hypotheses
are Gate 1, the four Gate 4 analytic/physical assumptions, four genuine Gate 5
IR/QFT assumptions, and Gate 6. -/
theorem microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5_closed_with_preRegistrationLedger
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F H : ProjectiveQubitCarrierField site)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5
        G fA fB F H gate1Targets gate6Targets
        gate7PreRegistrationLedgerTargets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain) := by
  exact
    microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5_closed
      G fA fB hA hB F H hgate1 hhorizon hscheduled hkernel hnull
      heffective hpropagators hgauge hparameters hgate6
      gate7_externalTests_closed_from_preRegistrationLedger

/-- Strongest current full-TOE target specialization: quantized-residual Gate
2 semantics, finite recovered-carrier Gate 5 cover-independence, the finite
Gate 6 audit package, and the existing Gate 7 preregistration ledger. -/
noncomputable def microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5Gate6Audits
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F H : ProjectiveQubitCarrierField site)
    (gate1Targets : Gate1MicroscopicLawTargets)
    (horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop)
    (initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets :=
  microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5
    G fA fB F H gate1Targets
    (gate6CosmologyBlackHoleTargetsOfFiniteAudits
      initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility)
    gate7PreRegistrationLedgerTargets
    horizonEstimatorConvergence physicalScheduledDensity
    bdgKernelProfileCertificate nullBalanceFromDynamics
    effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
    gaugeFieldsAndRenormalization standardModelParameterChain

/-- Strongest current full-closure theorem.  After supplying the named
microscopic Gate 4 package, finite recovered-carrier covers, and the existing
finite Gate 6 audits, the remaining assumptions are exactly Gate 1; the four
Gate 4 analytic/physical assumptions; four genuine Gate 5 IR/QFT assumptions;
and the two still-external Gate 6 cosmology inputs. -/
theorem microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5Gate6Audits_closed
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F H : ProjectiveQubitCarrierField site)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {horizonEstimatorConvergence physicalScheduledDensity
      bdgKernelProfileCertificate nullBalanceFromDynamics : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    {initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hscheduled : physicalScheduledDensity)
    (hkernel : bdgKernelProfileCertificate)
    (hnull : nullBalanceFromDynamics)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hcmb : cmbStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5Gate6Audits
        G fA fB F H gate1Targets
        horizonEstimatorConvergence physicalScheduledDensity
        bdgKernelProfileCertificate nullBalanceFromDynamics
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain
        initialConditionOrCosmologicalMeasure
        cmbStructureGravitationalWaveCompatibility) := by
  simpa
    [microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5Gate6Audits]
    using
      microscopicTOEClosureTargetsWithQuantizedGate2FiniteGate5_closed_with_preRegistrationLedger
        G fA fB hA hB F H hgate1 hhorizon hscheduled hkernel hnull
        heffective hpropagators hgauge hparameters
        (gate6_cosmologyBlackHole_closed_of_finiteAudits hinitial hcmb)

/-- Strongest current full-TOE target specialization with Gate 4 supplier data
itself used for the physical scheduled-density and kernel/profile-certificate
fields.  Only horizon-estimator convergence and null-balance dynamics remain
from Gate 4. -/
noncomputable def microscopicTOEClosureTargetsWithGate4DataFiniteGate5Gate6Audits
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F H : ProjectiveQubitCarrierField site)
    (gate1Targets : Gate1MicroscopicLawTargets)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop)
    (initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets where
  gate1Targets := gate1Targets
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery :=
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        G.gate3)
  gate4Targets :=
    microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargetsOfSuppliedData
      G horizonEstimatorConvergence nullBalanceFromDynamics
  gate5Targets :=
    gate5QFTStandardModelIRTargetsOfFiniteCarrierCover
      fA fB F H effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain
  gate6Targets :=
    gate6CosmologyBlackHoleTargetsOfFiniteAudits
      initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Strongest current full-closure theorem after harvesting the supplied Gate
4 scheduled-kernel data.  The remaining assumptions are Gate 1; Gate 4
horizon-estimator convergence and null-balance dynamics; four genuine Gate 5
IR/QFT assumptions; and Gate 6 initial-condition/cosmological-measure plus
CMB/structure/GW compatibility. -/
theorem microscopicTOEClosureTargetsWithGate4DataFiniteGate5Gate6Audits_closed
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F H : ProjectiveQubitCarrierField site)
    {gate1Targets : Gate1MicroscopicLawTargets}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    {initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hcmb : cmbStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithGate4DataFiniteGate5Gate6Audits
        G fA fB F H gate1Targets
        horizonEstimatorConvergence nullBalanceFromDynamics
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain
        initialConditionOrCosmologicalMeasure
        cmbStructureGravitationalWaveCompatibility) := by
  exact
    ⟨hgate1,
      microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed G,
      gate3_exactRecoveryCertificate_closed
        (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
          G.gate3),
      microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed_of_suppliedData
        G hhorizon hnull,
      gate5_qftStandardModelIR_closed_of_finiteCarrierCover
        fA fB hA hB F H heffective hpropagators hgauge hparameters,
      gate6_cosmologyBlackHole_closed_of_finiteAudits hinitial hcmb,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-- Strongest current full-TOE target with the finite Gate 1 branch package
also harvested.  Gate 1 is reduced to signed atlas fiber-sum noncancellation
and order-data coupling selection. -/
noncomputable def microscopicTOEClosureTargetsWithFiniteGate1Gate4DataFiniteGate5Gate6Audits
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F H : ProjectiveQubitCarrierField site)
    (couplingSelectedFromOrderData : Prop)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop)
    (initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets :=
  microscopicTOEClosureTargetsWithGate4DataFiniteGate5Gate6Audits
    G fA fB F H
    (gate1MicroscopicLawTargetsOfFiniteBranch
      couplingSelectedFromOrderData)
    horizonEstimatorConvergence nullBalanceFromDynamics
    effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
    gaugeFieldsAndRenormalization standardModelParameterChain
    initialConditionOrCosmologicalMeasure
    cmbStructureGravitationalWaveCompatibility

/-- Strongest current full-closure theorem after trying to close every
remaining field with existing finite/audit machinery.  What remains explicit
is the irreducible external target list: signed atlas fiber-sum
noncancellation, order-data coupling selection, Gate 4 horizon estimator and
null balance, four Gate 5 IR/QFT inputs, and two Gate 6 cosmology inputs. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4DataFiniteGate5Gate6Audits_closed
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F H : ProjectiveQubitCarrierField site)
    {couplingSelectedFromOrderData : Prop}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    {initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hcmb : cmbStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4DataFiniteGate5Gate6Audits
        G fA fB F H couplingSelectedFromOrderData
        horizonEstimatorConvergence nullBalanceFromDynamics
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain
        initialConditionOrCosmologicalMeasure
        cmbStructureGravitationalWaveCompatibility) := by
  exact
    microscopicTOEClosureTargetsWithGate4DataFiniteGate5Gate6Audits_closed
      G fA fB hA hB F H
      (gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
        hSum hcoupling)
      hhorizon hnull heffective hpropagators hgauge hparameters
      hinitial hcmb

/-- Strongest current full-TOE target with the finite Gate 1 branch, the
finite horizon-hit Gate 4 estimator, the Dorau-Much/Araki/BH null-balance
audit, finite Gate 5 carrier covers, finite Gate 6 audits, and the Gate 7
pre-registration ledger all wired into one target record. -/
noncomputable def microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiFiniteGate5Gate6Audits
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    {AQFT : HorizonAQFTModel} (phi : AQFT.Excitation)
    (couplingSelectedFromOrderData : Prop)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop)
    (initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets where
  gate1Targets :=
    gate1MicroscopicLawTargetsOfFiniteBranch
      couplingSelectedFromOrderData
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery :=
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        G.gate3)
  gate4Targets :=
    microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargetsOfEstimatorArakiBalance
      G Hest arakiFlux phi
  gate5Targets :=
    gate5QFTStandardModelIRTargetsOfFiniteCarrierCover
      fA fB F K effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain
  gate6Targets :=
    gate6CosmologyBlackHoleTargetsOfFiniteAudits
      initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Current sharpest full-closure theorem.  Existing finite/audit machinery
closes Gate 2, Gate 3, Gate 4's scheduled-density/kernel/interface fields,
Gate 4's estimator and null-balance fields once their concrete estimator/AQFT
inputs are supplied, Gate 5 carrier cover-independence, Gate 6 finite audit
fields, and Gate 7's protocol layer. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiFiniteGate5Gate6Audits_closed
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    {AQFT : HorizonAQFTModel} {alpha : ℝ} {phi : AQFT.Excitation}
    {couplingSelectedFromOrderData : Prop}
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    {initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hAraki : arakiFlux = Hest.continuumFlux)
    (hFlux : HorizonArakiRelativeEntropyFlux_Target AQFT)
    (hArea : RelativeEntropyAreaVariation_Target AQFT alpha)
    (hRay : RaychaudhuriAreaVariation_Target AQFT)
    (hBH : BekensteinHawkingEntropyArea_Target AQFT)
    (hS : AQFT.Srel phi ≠ 0)
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hcmb : cmbStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiFiniteGate5Gate6Audits
        G fA fB F K Hest arakiFlux phi couplingSelectedFromOrderData
        effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
        gaugeFieldsAndRenormalization standardModelParameterChain
        initialConditionOrCosmologicalMeasure
        cmbStructureGravitationalWaveCompatibility) := by
  exact
    ⟨gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
        hSum hcoupling,
      microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed G,
      gate3_exactRecoveryCertificate_closed
        (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
          G.gate3),
      microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed_of_estimatorArakiBalance
        G Hest arakiFlux hAraki hFlux hArea hRay hBH hS,
      gate5_qftStandardModelIR_closed_of_finiteCarrierCover
        fA fB hA hB F K heffective hpropagators hgauge hparameters,
      gate6_cosmologyBlackHole_closed_of_finiteAudits hinitial hcmb,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-- Sharpest current full-TOE target after harvesting the finite SM/QM audits
inside Gate 5 and the inflation/CMB tensor audit inside Gate 6.  The remaining
Gate 5 inputs are the three genuine constructive-QFT lifts, and the remaining
Gate 6 inputs are the cosmological measure/initial condition plus the
late-time structure/GW bridge. -/
noncomputable def microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6InflationAudits
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    {AQFT : HorizonAQFTModel} (phi : AQFT.Excitation)
    (couplingSelectedFromOrderData : Prop)
    (constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop)
    (initialConditionOrCosmologicalMeasure
      lateStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets where
  gate1Targets :=
    gate1MicroscopicLawTargetsOfFiniteBranch
      couplingSelectedFromOrderData
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery :=
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        G.gate3)
  gate4Targets :=
    microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargetsOfEstimatorArakiBalance
      G Hest arakiFlux phi
  gate5Targets :=
    gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
      fA fB F K constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift
  gate6Targets :=
    gate6CosmologyBlackHoleTargetsOfFiniteAuditsAndInflationCompatibility
      initialConditionOrCosmologicalMeasure
      lateStructureGravitationalWaveCompatibility
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Current sharpest full-closure theorem.  It closes every finite/audit layer
currently present in the repo and leaves only the remaining nontrivial physics
lifts explicit: Gate 1 signed-fiber and coupling selection, Gate 4
estimator/AQFT horizon inputs, the continuum/Haag-Ruelle/renormalization Gate
5 lifts, and two Gate 6 cosmology/structure inputs. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6InflationAudits_closed
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    {AQFT : HorizonAQFTModel} {alpha : ℝ} {phi : AQFT.Excitation}
    {couplingSelectedFromOrderData : Prop}
    {constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop}
    {initialConditionOrCosmologicalMeasure
      lateStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hAraki : arakiFlux = Hest.continuumFlux)
    (hFlux : HorizonArakiRelativeEntropyFlux_Target AQFT)
    (hArea : RelativeEntropyAreaVariation_Target AQFT alpha)
    (hRay : RaychaudhuriAreaVariation_Target AQFT)
    (hBH : BekensteinHawkingEntropyArea_Target AQFT)
    (hS : AQFT.Srel phi ≠ 0)
    (hHilbert : constructiveHilbertQFTLimit)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6InflationAudits
        G fA fB F K Hest arakiFlux phi couplingSelectedFromOrderData
        constructiveHilbertQFTLimit qftSpinStatisticsLift
        qftGaugeRenormalizationLift initialConditionOrCosmologicalMeasure
        lateStructureGravitationalWaveCompatibility) := by
  exact
    ⟨gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
        hSum hcoupling,
      microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed G,
      gate3_exactRecoveryCertificate_closed
        (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
          G.gate3),
      microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed_of_estimatorArakiBalance
        G Hest arakiFlux hAraki hFlux hArea hRay hBH hS,
      gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
        fA fB hA hB F K hHilbert hSpinStatistics hGaugeRenorm,
      gate6_cosmologyBlackHole_closed_of_finiteAuditsAndInflationCompatibility
        hinitial hlate,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-- Full-TOE target using the stricter Gate 6 audit envelope.  It harvests the
finite Gate 6 audits, inflation, Hayden-Preskill, AMPS, QQG conditional
cosmology, and physical-information-limit audits, while leaving the remaining
microscopic scrambling/decoupling/recovery evaporation dynamics explicit as a
genuine physics input. -/
noncomputable def microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    (S : QQGScenario)
    {AQFT : HorizonAQFTModel} (phi : AQFT.Excitation)
    (couplingSelectedFromOrderData : Prop)
    (constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop)
    (initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop) :
    TOEClosureTargets where
  gate1Targets :=
    gate1MicroscopicLawTargetsOfFiniteBranch
      couplingSelectedFromOrderData
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery :=
    Gate3ExactRecoveryCertificateClosed
      (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
        G.gate3)
  gate4Targets :=
    microscopicGate4ScheduledKernelData_toGate4HorizonEinsteinAnalyticTargetsOfEstimatorArakiBalance
      G Hest arakiFlux phi
  gate5Targets :=
    gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
      fA fB F K constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift
  gate6Targets :=
    gate6CosmologyBlackHoleTargetsOfFiniteAuditsInflationQQGAndInformationEnvelope
      S initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Current strict full-closure theorem.  Compared with the lighter inflation
Gate 6 theorem, this also harvests the Gate 5 Lorentzian-Wightman/chamber
mass-gap audits plus Hayden-Preskill, AMPS, QQG, and physical-information-limit
audits, and keeps microscopic evaporation dynamics as an explicit remaining
input. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope_closed
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    (S : QQGScenario)
    {AQFT : HorizonAQFTModel} {alpha : ℝ} {phi : AQFT.Excitation}
    {couplingSelectedFromOrderData : Prop}
    {constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop}
    {initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hAraki : arakiFlux = Hest.continuumFlux)
    (hFlux : HorizonArakiRelativeEntropyFlux_Target AQFT)
    (hArea : RelativeEntropyAreaVariation_Target AQFT alpha)
    (hRay : RaychaudhuriAreaVariation_Target AQFT)
    (hBH : BekensteinHawkingEntropyArea_Target AQFT)
    (hS : AQFT.Srel phi ≠ 0)
    (hHilbert : constructiveHilbertQFTLimit)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hevap : microscopicBlackHoleEvaporationDynamics)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope
        G fA fB F K Hest arakiFlux S phi couplingSelectedFromOrderData
        constructiveHilbertQFTLimit qftSpinStatisticsLift
        qftGaugeRenormalizationLift initialConditionOrCosmologicalMeasure
        microscopicBlackHoleEvaporationDynamics
        lateStructureGravitationalWaveCompatibility) := by
  exact
    ⟨gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
        hSum hcoupling,
      microscopicGate4ScheduledKernelData_gate2HauptvermutungSemantic_closed G,
      gate3_exactRecoveryCertificate_closed
        (microscopicGate3QuantizedConvergenceData_exactRecoveryCertificate
          G.gate3),
      microscopicGate4ScheduledKernelData_horizonEinsteinAnalytic_closed_of_estimatorArakiBalance
        G Hest arakiFlux hAraki hFlux hArea hRay hBH hS,
      gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
        fA fB hA hB F K hHilbert hSpinStatistics hGaugeRenorm,
      gate6_cosmologyBlackHole_closed_of_finiteAuditsInflationQQGAndInformationEnvelope
        S hinitial hevap hlate,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-- Strict full-closure specialization in which the Gate 5 continuum
Hilbert/QFT input is supplied by the named conditional octonion/S6 complex
geometry bridge.  This replaces the anonymous `constructiveHilbertQFTLimit`
assumption with the bridge record's explicit external-stability and
compatibility obligations. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5OctonionS6BridgeGate6QQGInformationEnvelope_closed
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    (S : QQGScenario)
    (T : Gate5OctonionS6ComplexGeometryBridgeTargets)
    {AQFT : HorizonAQFTModel} {alpha : ℝ} {phi : AQFT.Excitation}
    {couplingSelectedFromOrderData : Prop}
    {qftSpinStatisticsLift qftGaugeRenormalizationLift : Prop}
    {initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hAraki : arakiFlux = Hest.continuumFlux)
    (hFlux : HorizonArakiRelativeEntropyFlux_Target AQFT)
    (hArea : RelativeEntropyAreaVariation_Target AQFT alpha)
    (hRay : RaychaudhuriAreaVariation_Target AQFT)
    (hBH : BekensteinHawkingEntropyArea_Target AQFT)
    (hS : AQFT.Srel phi ≠ 0)
    (hGate5Bridge : Gate5OctonionS6ComplexGeometryBridgeClosed T)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hevap : microscopicBlackHoleEvaporationDynamics)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope
        G fA fB F K Hest arakiFlux S phi couplingSelectedFromOrderData
        T.complexGeometryFeedsConstructiveQFTLimit qftSpinStatisticsLift
        qftGaugeRenormalizationLift initialConditionOrCosmologicalMeasure
        microscopicBlackHoleEvaporationDynamics
        lateStructureGravitationalWaveCompatibility) := by
  exact
    microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope_closed
      G fA fB hA hB F K Hest arakiFlux S
      hSum hcoupling hAraki hFlux hArea hRay hBH hS
      hGate5Bridge.complexGeometryFeedsConstructiveQFTLimit
      hSpinStatistics hGaugeRenorm hinitial hevap hlate

/-- Strict full-closure specialization in which every remaining Gate 5 lift is
carried by a named bridge record: octonion/S6 for the Hilbert/QFT slot,
Haag-Ruelle/spin-statistics for the propagator slot, and
Yang-Mills/Higgs/renormalization for the gauge slot. -/
theorem microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiNamedGate5BridgesGate6QQGInformationEnvelope_closed
    {η ι X Y chart : Type*} [Fintype η] [Fintype ι]
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
    {C : UnifiedTheory.LayerA.CausalFoundation.CausalSet}
    [Fintype C.Event]
    (G : MicroscopicGate4ScheduledKernelData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      stepFloor weightBase sourceBase countGap curvatureGap spectralGap
      chartCertificate fixedScale densityBase densityStep coord chartOfCell
      sampleEvent phiAtPoint curvaturePhi operatorKernelData errorScale)
    {coverA coverB site : Type*}
    {probeA : coverA → Type*} {probeB : coverB → Type*}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F K : ProjectiveQubitCarrierField site)
    (Hest : HorizonHitSourceEstimator η) (arakiFlux : ℝ)
    (S : QQGScenario)
    (Scat : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ScatteringConstruction C)
    (THilbert : Gate5OctonionS6ComplexGeometryBridgeTargets)
    (TSpin : Gate5HaagRuelleSpinStatisticsBridgeTargets)
    (TGauge : Gate5YangMillsHiggsRenormalizationBridgeTargets)
    {AQFT : HorizonAQFTModel} {alpha : ℝ} {phi : AQFT.Excitation}
    {couplingSelectedFromOrderData : Prop}
    {initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData)
    (hAraki : arakiFlux = Hest.continuumFlux)
    (hFlux : HorizonArakiRelativeEntropyFlux_Target AQFT)
    (hArea : RelativeEntropyAreaVariation_Target AQFT alpha)
    (hRay : RaychaudhuriAreaVariation_Target AQFT)
    (hBH : BekensteinHawkingEntropyArea_Target AQFT)
    (hS : AQFT.Srel phi ≠ 0)
    (hHilbertBridge : Gate5OctonionS6ComplexGeometryBridgeClosed THilbert)
    (hSpinBridge : Gate5HaagRuelleSpinStatisticsBridgeClosed Scat TSpin)
    (hGaugeBridge : Gate5YangMillsHiggsRenormalizationBridgeClosed TGauge)
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hevap : microscopicBlackHoleEvaporationDynamics)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    TOEClosureClosed
      (microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope
        G fA fB F K Hest arakiFlux S phi couplingSelectedFromOrderData
        THilbert.complexGeometryFeedsConstructiveQFTLimit
        TSpin.qftSpinStatisticsLift
        TGauge.qftGaugeRenormalizationLift initialConditionOrCosmologicalMeasure
        microscopicBlackHoleEvaporationDynamics
        lateStructureGravitationalWaveCompatibility) := by
  exact
    microscopicTOEClosureTargetsWithFiniteGate1Gate4EstimatorArakiGate5SMAuditsGate6QQGInformationEnvelope_closed
      G fA fB hA hB F K Hest arakiFlux S
      hSum hcoupling hAraki hFlux hArea hRay hBH hS
      hHilbertBridge.complexGeometryFeedsConstructiveQFTLimit
      hSpinBridge.qftSpinStatisticsLift
      hGaugeBridge.qftGaugeRenormalizationLift
      hinitial hevap hlate

end UnifiedTheory.Audit.KFTOEFullClosureTarget
