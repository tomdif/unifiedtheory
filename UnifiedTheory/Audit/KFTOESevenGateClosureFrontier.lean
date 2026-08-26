/-
  Audit/KFTOESevenGateClosureFrontier.lean

  HONEST SEVEN-GATE CLOSURE FRONTIER

  This module combines the strongest compileable finite/formal results from
  the current Gate 1--7 audits.  The resulting proved package is deliberately
  smaller than physical TOE closure:

  * Gate 1 has exact finite support through the displayed rank-140 atlas.
  * Gate 2 has exact local equations on the recovered zero-window chart.
  * Gate 3 has the source-driven finite-rank construction.
  * Gate 4 has finite recovery and its actual kernel limit; nonzero physical
    target identification remains typed input.
  * Gate 5 has the finite local-net bridge and, conditional on its explicit
    incidence-equivariant readout, the finite many-body closure.  Continuum
    QFT/Standard-Model closure remains typed input.
  * Gate 6 has the causal-growth measure and sharp negative boundary audits;
    the repaired cosmological/Hayden--Preskill completion remains typed input.
  * Gate 7 has exact typed five-row protocol metadata and an explicitly
    incomplete external-result ledger with no freeze provenance.

  No inhabitant of an outstanding physical or external input is constructed.
  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
import UnifiedTheory.Audit.KFCausalCSpecHauptvermutungZeroWindowExact
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornNonzeroBDGFrontier
import UnifiedTheory.Audit.KFTOEAllAttacksCapstone
import UnifiedTheory.Audit.KFTOESharedHarmonicMicroscopicModel
import UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornPhysicalFrontier
import UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger
import UnifiedTheory.Audit.KFGate6PhysicalBoundaryAudit
import UnifiedTheory.Audit.KFGate7ProtocolIntegrity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOESevenGateClosureFrontier

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornIncidenceEquivariance
open UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungZeroWindowExact
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornNonzeroBDGFrontier
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornPhysicalFrontier
open UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout
open UnifiedTheory.Audit.KFGate6PhysicalBoundaryAudit
open UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger
open UnifiedTheory.Audit.KFGate7ProtocolIntegrity
open UnifiedTheory.Audit.KFTOEAllAttacksCapstone
open UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
open UnifiedTheory.Audit.KFTOESharedHarmonicMicroscopicModel
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Cosmology.QQG

universe u v w z

/-! ## 1. Gate 1 exact finite support -/

/-- Exact support of the canonical harmonic Born transition on every physical
and nonphysical step in the finite range used by the displayed atlas. -/
def Gate1FiniteExactSupportClosed : Prop :=
  ∀ (chirality : Fin 2) {n : ℕ} (hRank : n < 140)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n),
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
      IsPhysicalCausalGrowthStep n pathPrefix child

theorem gate1FiniteExactSupport_closed : Gate1FiniteExactSupportClosed := by
  intro chirality n hRank pathPrefix child
  exact canonicalHarmonicBornShellTransition_ne_zero_iff_physical_below_140
    chirality hRank pathPrefix child

/-! ## 2. Gate 3 source-driven finite-rank input package -/

/-- The ordinary mathematical data from which the source-driven Gate-3 audit
constructs its decreasing finite defect rank.  These are model parameters,
not empirical evidence. -/
structure SourceDrivenGate3FormalInputs
    (ι : Type u) [Fintype ι] where
  chirality : Fin 2
  parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n
  observe : (n : ℕ) → CausalSetGrowthBranch n → ι
  countGap : ℝ
  curvatureGap : ℝ
  spectralGap : ℝ
  countGap_pos : 0 < countGap
  curvatureGap_pos : 0 < curvatureGap
  spectralGap_pos : 0 < spectralGap
  scale : ℕ → ℝ
  c : ℕ → ℝ
  edge : ι → E4
  initial : QuantizedGate3State ι

namespace SourceDrivenGate3FormalInputs

variable {ι : Type u} [Fintype ι]

/-- The concrete Gate-3 record generated from the source-driven inputs. -/
def toGate3Data (G : SourceDrivenGate3FormalInputs ι) :=
  sourceDrivenHarmonicBornProtectedWellFoundedGate3Data
    G.chirality G.parentSchedule G.observe
    G.countGap G.curvatureGap G.spectralGap
    G.countGap_pos G.curvatureGap_pos G.spectralGap_pos
    G.scale G.c G.edge G.initial

/-- The source-driven rank theorem supplies the complete Gate-3 interface;
there is no separately assumed rank-decrease field. -/
theorem closed (G : SourceDrivenGate3FormalInputs ι) :
    G.toGate3Data.Closed := by
  exact sourceDrivenHarmonicBornProtectedWellFoundedGate3_closed
    G.chirality G.parentSchedule G.observe
    G.countGap G.curvatureGap G.spectralGap
    G.countGap_pos G.curvatureGap_pos G.spectralGap_pos
    G.scale G.c G.edge G.initial

end SourceDrivenGate3FormalInputs

/-- Universal statement of the constructive Gate-3 rank result. -/
def Gate3SourceDrivenConstructionClosed : Prop :=
  ∀ (ι : Type u) [Fintype ι] (G : SourceDrivenGate3FormalInputs ι),
    G.toGate3Data.Closed

theorem gate3SourceDrivenConstruction_closed :
    Gate3SourceDrivenConstructionClosed := by
  intro ι _ G
  exact G.closed

/-! ## 3. Gates 2--4 on one recovered harmonic handoff -/

variable {ι X Y chart : Type*} [Fintype ι] [Nonempty ι]
variable [AddCommGroup Y] [Module ℝ Y]
variable [Fintype chart] [Nonempty chart]
variable {chirality : Fin 2}
variable
  {parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable
  {J countWindow curvatureBias spectralLocality corrector : ℕ → ι → ℝ}
variable {scale c total correctorCoeff : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

variable
  (H : HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c total correctorCoeff edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

/-- Exact local equations forced by the actual chart certificate at the
finite recovery bound of `H`. -/
def ExactRecoveredChartGeometry : Prop :=
  (∀ i x x', x ≠ x' →
    (H.chartCertificate H.recoveryBound).count i x x' =
      (H.chartCertificate H.recoveryBound).density *
        (H.chartCertificate H.recoveryBound).volume i x x') ∧
  (∀ i x x', x ≠ x' →
    (H.chartCertificate H.recoveryBound).volume i x x' =
      (Real.pi / 24) *
        ((H.chartCertificate H.recoveryBound).G x x') ^ 2) ∧
  (∀ i j x x', x ≠ x' →
    (H.chartCertificate H.recoveryBound).B
        (((H.chartCertificate H.recoveryBound).chart i x -
            (H.chartCertificate H.recoveryBound).chart i x') -
          ((H.chartCertificate H.recoveryBound).chart j x -
            (H.chartCertificate H.recoveryBound).chart j x'))
        (((H.chartCertificate H.recoveryBound).chart i x -
            (H.chartCertificate H.recoveryBound).chart i x') -
          ((H.chartCertificate H.recoveryBound).chart j x -
            (H.chartCertificate H.recoveryBound).chart j x')) = 0)

/-- Gate 3 makes all three chart windows zero at its finite rank bound, and
the Gate-2 zero-window audit converts those bounds to exact local geometry. -/
theorem exactRecoveredChartGeometry_closed :
    ExactRecoveredChartGeometry H := by
  rcases H.chartResiduals_zero_after_recoveryBound
      H.recoveryBound le_rfl with ⟨hCount, hCurvature, hPair⟩
  exact exact_local_geometry_of_zero_windows
    (H.chartCertificate H.recoveryBound) hCount hCurvature hPair

/-! ## 4. One microscopic harmonic law for three measurable readouts -/

/-- Every three-way measurable readout of one fixed-chirality harmonic causal
history has a normalized joint pushforward whose marginals are exactly its
three component pushforwards.  This statement is formal and does not identify
any component with a physical Gate-4, Gate-5, or Gate-6 observable. -/
def Gate456SharedHarmonicReadoutClosed : Prop :=
  ∀ (sharedChirality : Fin 2)
    (Gate4State : Type u) (Gate5State : Type v) (Gate6State : Type w)
    [MeasurableSpace Gate4State] [MeasurableSpace Gate5State]
    [MeasurableSpace Gate6State]
    (sharedReadout : HarmonicGate456Readout sharedChirality
      Gate4State Gate5State Gate6State),
    sharedReadout.Closed

/-- The unconditional shared-law readout theorem, uniformly over all three
measurable target spaces and readout maps. -/
theorem gate456SharedHarmonicReadout_closed :
    Gate456SharedHarmonicReadoutClosed := by
  intro sharedChirality Gate4State Gate5State Gate6State
    _ _ _ sharedReadout
  exact sharedReadout.closed

/-! ## 5. The proved finite/formal closure ledger -/

/-- Every field in this record is a proved consequence relative to the
supplied formal handoff `H` and the displayed ordinary model inputs.  The
record does not claim that `H` itself has been physically identified, and it
contains no physical-target, continuum-QFT, black-hole-dynamics, or external
result witness.  Its Gate-4--6 structural fields do not identify the concrete
`H`, `R`, and `S` as component readouts of the shared-law theorem. -/
structure ProvedFiniteFormalClosures (errorScale : ℝ) : Prop where
  gate1FiniteExactSupport : Gate1FiniteExactSupportClosed
  gate1DisplayedAtlas :
    ∀ chirality : Fin 2,
      Gate1HarmonicBornShellAtlasRealizationClosed chirality
  gate3SourceDrivenConstruction : Gate3SourceDrivenConstructionClosed
  gate3HandoffClosed : H.gate3.Closed
  gate2ExactRecoveredChartGeometry : ExactRecoveredChartGeometry H
  gate4FiniteRecoveryAndKernelLimit : H.Closed errorScale
  gate4NonzeroTargetConditionalReduction :
    HasNonzeroBDG4DTarget H.operatorKernelData →
      H.Closed errorScale ∧
        HasNonzeroBDG4DTarget H.operatorKernelData
  gate4CurvatureConventionBoundary :
    ∀ boxPhi curvaturePhi : ℝ,
      boxPhi + (1 / 2 : ℝ) * curvaturePhi =
          boxPhi - (1 / 2 : ℝ) * curvaturePhi ↔
        curvaturePhi = 0
  gate45FiniteLocalNet :
    ∀ R : HarmonicSingleGenerationReadout ι,
      HarmonicGate45FiniteBridgeClosed H R
  gate45FiniteEquivariantManyBody :
    ∀ (R : HarmonicSingleGenerationReadout ι)
      (E : IncidenceEquivariantHarmonicReadout chirality
        (candidate H.recoveryBound) R),
      HarmonicGate45FiniteEquivariantManyBodyClosed H R E
  gate456FiniteStructural :
    ∀ (R : HarmonicSingleGenerationReadout ι)
      (S : QQGScenario),
      HarmonicGate456FiniteStructuralClosed H R S errorScale
  gate456SharedHarmonicReadout : Gate456SharedHarmonicReadoutClosed
  gate6CausalGrowthProbabilityMeasure :
    Gate6ActionSelectedHarmonicBornCausalGrowthMeasureCertificate
  gate6LegacyAllSetupsHaydenGapUninhabited :
    ¬ Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed
  gate6BinaryLowOutsideDeclaredWindow :
    ¬ QQGScenarioInDeclaredViabilityWindow binaryQQGLowScenario
  gate6BinaryHighOutsideDeclaredWindow :
    ¬ QQGScenarioInDeclaredViabilityWindow binaryQQGHighScenario
  gate7TypedProtocolLength : typedPreRegistrationLedger.length = 5
  gate7TypedProtocolKeysUnique :
    (typedPreRegistrationLedger.map
      TypedPreRegistration.predictionId).Nodup
  gate7TypedProtocolKeysCover :
    ∀ id : PredictionId,
      id ∈ typedPreRegistrationLedger.map
        TypedPreRegistration.predictionId
  gate7PredictionEntriesExact :
    typedPreRegistrationLedger.map TypedPreRegistration.entry =
      UnifiedTheory.LayerB.PreRegistrationLedger.preRegisteredEntries
  gate7FalsificationRowsExact :
    typedPreRegistrationLedger.map
        TypedPreRegistration.falsificationRow =
      UnifiedTheory.LayerB.PreRegistrationLedger.falsificationTable
  gate7CurrentExternalResultsDoNotCover :
    ¬ ExternalResultLedgerCovers currentExternalResultLedger
  gate7CurrentExternalResultsExactlyEmpty :
    currentExternalResultLedger = []
  gate7EveryPredictionCurrentlyPending :
    ∀ id : PredictionId, id ∈ currentPendingPredictionIds
  gate7CurrentFreezeProvenanceAbsent : currentFreezeProvenance = none

/-- Constructor for the entire genuinely proved finite/formal ledger. -/
theorem provedFiniteFormalClosures_closed (errorScale : ℝ) :
    ProvedFiniteFormalClosures H errorScale where
  gate1FiniteExactSupport := gate1FiniteExactSupport_closed
  gate1DisplayedAtlas := gate1HarmonicBornShellAtlasRealization_closed
  gate3SourceDrivenConstruction := gate3SourceDrivenConstruction_closed
  gate3HandoffClosed := H.gate3.closed
  gate2ExactRecoveredChartGeometry := exactRecoveredChartGeometry_closed H
  gate4FiniteRecoveryAndKernelLimit := H.closed errorScale
  gate4NonzeroTargetConditionalReduction :=
    closed_and_hasNonzeroBDG4DTarget H errorScale
  gate4CurvatureConventionBoundary := plusHalfTarget_eq_minusHalfTarget_iff
  gate45FiniteLocalNet := harmonicGate45FiniteBridge_closed H
  gate45FiniteEquivariantManyBody :=
    harmonicGate45FiniteEquivariantManyBody_closed H
  gate456FiniteStructural := fun R S =>
    harmonicGate456FiniteStructural_closed H R S errorScale
  gate456SharedHarmonicReadout := gate456SharedHarmonicReadout_closed
  gate6CausalGrowthProbabilityMeasure :=
    gate6_actionSelectedHarmonicBornCausalGrowthMeasureCertificate_closed
  gate6LegacyAllSetupsHaydenGapUninhabited :=
    gate6_haydenPreskillMicroscopicEvaporationBridgeClosed_uninhabited
  gate6BinaryLowOutsideDeclaredWindow :=
    binaryQQGLowScenario_not_in_declared_viability_window
  gate6BinaryHighOutsideDeclaredWindow :=
    binaryQQGHighScenario_not_in_declared_viability_window
  gate7TypedProtocolLength := typedPreRegistrationLedger_length
  gate7TypedProtocolKeysUnique := typedPreRegistrationLedger_keys_nodup
  gate7TypedProtocolKeysCover := typedPreRegistrationLedger_covers
  gate7PredictionEntriesExact := typedPreRegistrationLedger_entries_exact
  gate7FalsificationRowsExact := typedPreRegistrationLedger_rows_exact
  gate7CurrentExternalResultsDoNotCover :=
    currentExternalResultLedger_not_covers
  gate7CurrentExternalResultsExactlyEmpty :=
    currentExternalResultLedger_empty
  gate7EveryPredictionCurrentlyPending :=
    every_prediction_currently_pending
  gate7CurrentFreezeProvenanceAbsent := currentFreezeProvenance_absent

/-! ## 6. Explicitly typed outstanding physical/external inputs -/

/-- Physical interpretation of a shared three-way harmonic readout is a
separate input.  The caller fixes the three interpretation predicates and
must establish each one for the corresponding component; the formal shared
law theorem above does not infer these fields from an arbitrary Gate-4
handoff or Gate-5 readout.  Since the predicates are caller-defined, this
record names the semantic obligation; it is not itself an H/R/B linkage
theorem. -/
structure Gate456ReadoutPhysicalIdentificationInput
    {sharedChirality : Fin 2}
    {Gate4State : Type u} {Gate5State : Type v} {Gate6State : Type w}
    [MeasurableSpace Gate4State] [MeasurableSpace Gate5State]
    [MeasurableSpace Gate6State]
    (sharedReadout : HarmonicGate456Readout sharedChirality
      Gate4State Gate5State Gate6State)
    (IdentifiesPhysicalGate4Readout :
      (HarmonicCausalHistory → Gate4State) → Prop)
    (IdentifiesPhysicalGate5Readout :
      (HarmonicCausalHistory → Gate5State) → Prop)
    (IdentifiesPhysicalGate6Readout :
      (HarmonicCausalHistory → Gate6State) → Prop) : Prop where
  gate4Identified :
    IdentifiesPhysicalGate4Readout sharedReadout.gate4Readout
  gate5Identified :
    IdentifiesPhysicalGate5Readout sharedReadout.gate5Readout
  gate6Identified :
    IdentifiesPhysicalGate6Readout sharedReadout.gate6Readout

/-- Gates 2 and 4 still require a physical Lorentzian chart/field dictionary
identifying the target of the actual kernel in `H`.  This is an alias for the
existing frontier type; no value is defined here. -/
abbrev Gate24PhysicalTargetInput
    (PhysicalChart PhysicalField : Type*)
    (IsLorentzianChart : PhysicalChart → Prop)
    (CertificateSequenceGeneratesChart :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart → Prop)
    (ChartGeneratesField : PhysicalChart → PhysicalField → Prop)
    (physicalBDGTarget : PhysicalChart → PhysicalField → ℝ) :=
  PhysicalBDGTargetIdentification H
    PhysicalChart PhysicalField IsLorentzianChart
    CertificateSequenceGeneratesChart ChartGeneratesField
    physicalBDGTarget

/-- Gate 5 remains the closure proposition for one fixed, independently
specified continuum QFT/Standard-Model target.  No target or proof is chosen. -/
abbrev Gate5ContinuumPhysicalInput
    (targets : Gate5QFTStandardModelIRTargets) :=
  Gate5QFTStandardModelIRClosed targets

/-- Gate 6 requires one fixed-semantic preregistration/result pair, empirical
evidence satisfying those exact semantics, a scenario inside the declared
viability window, and the repaired physical completion for those same fixed
claims.  No preregistration, result, evidence, or completion is constructed. -/
structure Gate6PhysicalCompletionInput
    (P : QQGFixedSemanticPreregistration)
    (results : QQGFixedSemanticProtocolResults)
    (S : QQGScenario)
    {gate6Chirality : Fin 2}
    {CosmologicalInitialState : Type v}
    [MeasurableSpace CosmologicalInitialState]
    {physicallyAdmissible : Set CosmologicalInitialState}
    {Dynamics : Type w} {RecoveryChannel : Type z}
    {scrambles : Dynamics →
      UnifiedTheory.LayerC.HaydenPreskill.HPSetup → Prop}
    {traceNormDecouples : Dynamics →
      UnifiedTheory.LayerC.HaydenPreskill.HPSetup → Prop}
    {isCPTP : RecoveryChannel → Prop}
    {recovers : RecoveryChannel → Dynamics →
      UnifiedTheory.LayerC.HaydenPreskill.HPSetup → Prop}
    (B : Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge
      gate6Chirality CosmologicalInitialState physicallyAdmissible)
    (HP : Gate6PhysicalHaydenPreskillFrontier Dynamics RecoveryChannel
      scrambles traceNormDecouples isCPTP recovers)
    (lateStructureFormation gravitationalWaveCompatibility : Prop)
    (blackHoleClaims : Gate6MicroscopicBlackHoleDynamicsClaims) : Prop where
  fixedSemanticEmpiricalEvidence :
    QQGFixedSemanticEmpiricalEvidence P results
  scenarioInDeclaredViabilityWindow :
    QQGScenarioInDeclaredViabilityWindow S
  physicalCompletion :
    Gate6ActionSelectedHarmonicBornPhysicalCompletionClosed
      (fixedSemanticQQGEmergenceClaims P results) S B HP
      lateStructureFormation gravitationalWaveCompatibility blackHoleClaims

/-- Gate 7 external completion requires a unique provenance-bearing result
for every typed prediction and caller-supplied validation semantics for data
authentication, temporal ordering, and application of the registered test.
The structure requires those validations but supplies none of their meanings
or witnesses. -/
structure Gate7ExternalCompletionInput
    (DigestAuthenticated : DatasetSource → DatasetDigest → Prop)
    (FreezePrecedesObservation :
      FreezeProvenance → ObservationTimestamp → Prop)
    (RegisteredTestValidated :
      TypedPreRegistration → ExternalResultEntry → Prop) where
  results : List ExternalResultEntry
  resultsCoverAllPredictions : ExternalResultLedgerCovers results
  resultPredictionIdsUnique :
    (results.map ExternalResultEntry.predictionId).Nodup
  freezeProvenance : FreezeProvenance
  everyDigestAuthenticated :
    ∀ result ∈ results,
      DigestAuthenticated result.datasetSource result.datasetDigest
  freezePrecedesEveryObservation :
    ∀ result ∈ results,
      FreezePrecedesObservation freezeProvenance result.observedAt
  everyRegisteredTestValidated :
    ∀ result ∈ results,
      RegisteredTestValidated
        (typedPreRegistration result.predictionId) result

/-- The explicit current empty ledger cannot underlie a Gate-7 external
completion input. -/
theorem noGate7ExternalCompletionFromCurrentLedger :
    ∀ (DigestAuthenticated : DatasetSource → DatasetDigest → Prop)
      (FreezePrecedesObservation :
        FreezeProvenance → ObservationTimestamp → Prop)
      (RegisteredTestValidated :
        TypedPreRegistration → ExternalResultEntry → Prop),
    ¬ ∃ E : Gate7ExternalCompletionInput DigestAuthenticated
        FreezePrecedesObservation RegisteredTestValidated,
      E.results = currentExternalResultLedger := by
  intro DigestAuthenticated FreezePrecedesObservation
    RegisteredTestValidated
  rintro ⟨E, hCurrent⟩
  apply currentExternalResultLedger_not_covers
  simpa [hCurrent] using E.resultsCoverAllPredictions

#print axioms gate1FiniteExactSupport_closed
#print axioms SourceDrivenGate3FormalInputs.closed
#print axioms exactRecoveredChartGeometry_closed
#print axioms gate456SharedHarmonicReadout_closed
#print axioms provedFiniteFormalClosures_closed
#print axioms noGate7ExternalCompletionFromCurrentLedger

end

end UnifiedTheory.Audit.KFTOESevenGateClosureFrontier
