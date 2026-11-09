/-
  Audit/KFTOESevenGateStrengthening.lean

  SEVEN-GATE FORMAL STRENGTHENING

  This module closes several avoidable formal gaps left visible by the honest
  seven-gate frontier:

  * Gate 1 packages the action-selected all-rank law with the phase-safe
    all-rank exact-support alternative.
  * Gate 2 promotes exact recovered-chart equations from one rank to the
    entire tail after the recovery bound.
  * Gate 3 exposes the initial defect rank as an explicit finite deadline.
  * Gate 4 proves rigidity of every physical target identification attached
    to the same actual kernel.
  * Gate 5 proves microcausality for arbitrary observables in disjoint finite
    regional star algebras.
  * Gate 6 replaces the old N = 1 binary example by a measurable,
    nonconstant readout whose two scenarios lie in the declared viability
    window.
  * Gate 7 proves that every unique covering result ledger has exactly five
    entries, one per typed prediction.

  These are formal closures and interface strengthenings.  In particular,
  they do not construct a Lorentzian continuum identification, a continuum
  QFT/Standard-Model limit, QQG emergence evidence, black-hole dynamics, or
  external experimental results.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOESevenGateClosureFrontier
import UnifiedTheory.Audit.KFCausalSetPhaseSafeHarmonicBornShell
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornManyBodyNet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOESevenGateStrengthening

noncomputable section

open scoped BigOperators
open Set MeasureTheory
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalSetPhaseSafeHarmonicBornShell
open UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungZeroWindowExact
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornSourceDrivenRank
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornNonzeroBDGFrontier
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornManyBodyNet
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
open UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout
open UnifiedTheory.Audit.KFGate6PhysicalBoundaryAudit
open UnifiedTheory.Audit.KFGate7ProtocolIntegrity
open UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
open UnifiedTheory.Audit.KFTOESevenGateClosureFrontier
open UnifiedTheory.Cosmology.QQG

universe u

/-! ## Gate 1: all-rank law package -/

/-- The strongest honest all-rank Gate-1 package.  The action-selected law
has exact raw physical support, while the phase-safe alternative additionally
has exact support after normalization.  The latter uses its explicitly added
full-support phase convention. -/
structure Gate1AllRankStrengthened (chirality : Fin 2) : Prop where
  actionSelectedLaw : Gate1HarmonicBornShellLawClosed chirality
  phaseSafeAllRank :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child, (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
        n pathPrefix child = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      finiteComplexBornMass
        ((phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix) = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
        IsPhysicalCausalGrowthStep n pathPrefix child) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      star ((phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix child) =
        (phaseSafeHarmonicBornShellGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
            n pathPrefix child) ∧
    finiteRankedPathAmplitude
        (phaseSafeHarmonicBornShellGrowthLaw chirality) 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0

theorem gate1AllRankStrengthened_closed (chirality : Fin 2) :
    Gate1AllRankStrengthened chirality :=
  ⟨gate1HarmonicBornShellLaw_closed chirality,
    phaseSafeHarmonicBornShell_global_capstone chirality⟩

/-! ## Gates 2--4: stronger consequences of one recovered handoff -/

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

/-- Gate-2 exact local geometry holds at every rank after the actual recovery
bound, not only at the first recovered rank. -/
def ExactRecoveredChartGeometryTail : Prop :=
  ∀ n, H.recoveryBound ≤ n →
    (∀ i x x', x ≠ x' →
      (H.chartCertificate n).count i x x' =
        (H.chartCertificate n).density *
          (H.chartCertificate n).volume i x x') ∧
    (∀ i x x', x ≠ x' →
      (H.chartCertificate n).volume i x x' =
        (Real.pi / 24) * ((H.chartCertificate n).G x x') ^ 2) ∧
    (∀ i j x x', x ≠ x' →
      (H.chartCertificate n).B
          (((H.chartCertificate n).chart i x -
              (H.chartCertificate n).chart i x') -
            ((H.chartCertificate n).chart j x -
              (H.chartCertificate n).chart j x'))
          (((H.chartCertificate n).chart i x -
              (H.chartCertificate n).chart i x') -
            ((H.chartCertificate n).chart j x -
              (H.chartCertificate n).chart j x')) = 0)

theorem exactRecoveredChartGeometryTail_closed :
    ExactRecoveredChartGeometryTail H := by
  intro n hn
  rcases H.chartResiduals_zero_after_recoveryBound n hn with
    ⟨hCount, hCurvature, hPair⟩
  exact exact_local_geometry_of_zero_windows
    (H.chartCertificate n) hCount hCurvature hPair

/-- The Gate-3 construction reaches exact zero no later than the concrete
natural number `defectRank 0` computed from its supplied initial state. -/
def Gate3ExplicitFiniteDeadlineClosed : Prop :=
  ∀ (ι : Type u) [Fintype ι]
    (G : SourceDrivenGate3FormalInputs ι),
    ∀ n, G.toGate3Data.defectRank 0 ≤ n →
      sourceDrivenTotal G.countGap G.curvatureGap G.spectralGap
          G.scale G.edge G.initial n = 0 ∧
        (∀ i, sourceDrivenCountWindow
          G.countGap G.curvatureGap G.spectralGap
          G.scale G.edge G.initial n i = 0) ∧
          (∀ i, sourceDrivenCurvatureBias
            G.countGap G.curvatureGap G.spectralGap
            G.scale G.edge G.initial n i = 0) ∧
            (∀ i, sourceDrivenSpectralLocality
              G.countGap G.curvatureGap G.spectralGap
              G.scale G.edge G.initial n i = 0) ∧
              sourceDrivenCandidate
                  G.countGap G.curvatureGap G.spectralGap
                  G.scale G.edge G.initial n =
                canonicalCSpecBridgeCandidate G.edge

theorem gate3ExplicitFiniteDeadline_closed :
    Gate3ExplicitFiniteDeadlineClosed := by
  intro _ _ G n hn
  exact G.toGate3Data.exact_zero_after_initial_defectRank n hn

/-- Two physical dictionaries attached to the same actual Gate-4 kernel
cannot assign different selected target values, even if their chart, field,
and interpretation types differ. -/
theorem gate4_sameKernel_physicalTarget_unique
    {PhysicalChart₁ PhysicalField₁ PhysicalChart₂ PhysicalField₂ : Type*}
    {IsLorentzianChart₁ : PhysicalChart₁ → Prop}
    {IsLorentzianChart₂ : PhysicalChart₂ → Prop}
    {CertificateSequenceGeneratesChart₁ :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart₁ → Prop}
    {CertificateSequenceGeneratesChart₂ :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart₂ → Prop}
    {ChartGeneratesField₁ : PhysicalChart₁ → PhysicalField₁ → Prop}
    {ChartGeneratesField₂ : PhysicalChart₂ → PhysicalField₂ → Prop}
    {physicalBDGTarget₁ : PhysicalChart₁ → PhysicalField₁ → ℝ}
    {physicalBDGTarget₂ : PhysicalChart₂ → PhysicalField₂ → ℝ}
    (P : PhysicalBDGTargetIdentification H
      PhysicalChart₁ PhysicalField₁ IsLorentzianChart₁
      CertificateSequenceGeneratesChart₁ ChartGeneratesField₁
      physicalBDGTarget₁)
    (Q : PhysicalBDGTargetIdentification H
      PhysicalChart₂ PhysicalField₂ IsLorentzianChart₂
      CertificateSequenceGeneratesChart₂ ChartGeneratesField₂
      physicalBDGTarget₂) :
    physicalBDGTarget₁ P.physicalChart P.physicalField =
      physicalBDGTarget₂ Q.physicalChart Q.physicalField :=
  P.target_identification.symm.trans Q.target_identification

/-! ## Gate 5: arbitrary regional microcausality -/

/-- Universal finite regional microcausality for the many-body net. -/
def Gate5FiniteRegionalMicrocausalityClosed : Prop :=
  ∀ (site : Type u) [Fintype site] [Nonempty site] [DecidableEq site]
    (first second : Finset site), Disjoint first second →
    ∀ (A B : ManyBodyObservable site),
      A ∈ manyBodyLocalObservableAlgebra first →
      B ∈ manyBodyLocalObservableAlgebra second →
      Commute A B

theorem gate5FiniteRegionalMicrocausality_closed :
    Gate5FiniteRegionalMicrocausalityClosed := by
  intro _ _ _ _ first second hDisjoint A B hA hB
  exact manyBodyLocalObservableAlgebra_commute_of_disjoint
    hDisjoint hA hB

/-! ## Gate 6: a nonconstant readout inside the declared window -/

local instance qqgScenarioMeasurableSpace : MeasurableSpace QQGScenario := ⊤

/-- A canonical point in the already-declared QQG viability window. -/
def canonicalQQGViabilityWitness : QQGViableParameters where
  lam_tH := 1
  N_matter := 100000
  lam_tH_pos := by norm_num
  lam_tH_le_one := by norm_num
  lam_tH_ge_tenth := by norm_num
  N_matter_lower := by norm_num
  N_matter_upper := by norm_num

/-- Low-e-fold viable scenario with λ_tH = 1 and N = 10^5. -/
def viableQQGLowScenario : QQGScenario where
  lam₀ := (4 * Real.pi) ^ 2 / 100000
  μ₀ := 1
  N := 100000
  N_e := 50
  lam₀_pos := by positivity
  μ₀_pos := by norm_num
  N_pos := by norm_num
  N_e_pos := by norm_num

/-- High-e-fold viable scenario with the same viable couplings. -/
def viableQQGHighScenario : QQGScenario where
  lam₀ := (4 * Real.pi) ^ 2 / 100000
  μ₀ := 1
  N := 100000
  N_e := 60
  lam₀_pos := by positivity
  μ₀_pos := by norm_num
  N_pos := by norm_num
  N_e_pos := by norm_num

theorem viableQQGLowScenario_lam_tH :
    viableQQGLowScenario.lam_tH = 1 := by
  unfold QQGScenario.lam_tH tHooft viableQQGLowScenario
  have hpi : (4 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

theorem viableQQGHighScenario_lam_tH :
    viableQQGHighScenario.lam_tH = 1 := by
  unfold QQGScenario.lam_tH tHooft viableQQGHighScenario
  have hpi : (4 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

theorem viableQQGLowScenario_in_declared_window :
    QQGScenarioInDeclaredViabilityWindow viableQQGLowScenario := by
  refine ⟨canonicalQQGViabilityWitness, ?_, rfl⟩
  simpa [canonicalQQGViabilityWitness] using viableQQGLowScenario_lam_tH.symm

theorem viableQQGHighScenario_in_declared_window :
    QQGScenarioInDeclaredViabilityWindow viableQQGHighScenario := by
  refine ⟨canonicalQQGViabilityWitness, ?_, rfl⟩
  simpa [canonicalQQGViabilityWitness] using viableQQGHighScenario_lam_tH.symm

theorem viableQQGScenarios_ne :
    viableQQGLowScenario ≠ viableQQGHighScenario := by
  intro h
  have hN := congrArg QQGScenario.N_e h
  norm_num [viableQQGLowScenario, viableQQGHighScenario] at hN

def harmonicRankOneViableQQGReadout
    (trajectory : ∀ n : ℕ, CausalSetGrowthBranch n) : QQGScenario :=
  if trajectory 1 = rankOneGregariousChild then viableQQGLowScenario
  else viableQQGHighScenario

theorem harmonicRankOneViableQQGReadout_measurable :
    Measurable harmonicRankOneViableQQGReadout := by
  apply (measurable_of_finite
    (fun child : CausalSetGrowthBranch 1 =>
      if child = rankOneGregariousChild then viableQQGLowScenario
      else viableQQGHighScenario)).comp
  exact measurable_pi_apply 1

def viableQQGAdmissibleSector : Set QQGScenario :=
  {scenario | QQGScenarioInDeclaredViabilityWindow scenario}

theorem viableQQGAdmissibleSector_measurable :
    MeasurableSet viableQQGAdmissibleSector :=
  MeasurableSet.of_discrete

theorem harmonicRankOneViableQQGReadout_mem_admissible
    (trajectory : ∀ n : ℕ, CausalSetGrowthBranch n) :
    harmonicRankOneViableQQGReadout trajectory ∈
      viableQQGAdmissibleSector := by
  by_cases h : trajectory 1 = rankOneGregariousChild
  · simpa [harmonicRankOneViableQQGReadout,
      viableQQGAdmissibleSector, h] using
        viableQQGLowScenario_in_declared_window
  · simpa [harmonicRankOneViableQQGReadout,
      viableQQGAdmissibleSector, h] using
        viableQQGHighScenario_in_declared_window

def harmonicViableQQGCosmologicalReadoutBridge (chirality : Fin 2) :
    Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      QQGScenario viableQQGAdmissibleSector where
  readout := harmonicRankOneViableQQGReadout
  readoutMeasurable := harmonicRankOneViableQQGReadout_measurable
  admissibleMeasurable := viableQQGAdmissibleSector_measurable
  almostEveryTrajectoryAdmissible :=
    Filter.Eventually.of_forall
      harmonicRankOneViableQQGReadout_mem_admissible

theorem harmonicRankOneViableQQGReadout_nonconstant :
    ∃ first second : ∀ n : ℕ, CausalSetGrowthBranch n,
      harmonicRankOneViableQQGReadout first ≠
        harmonicRankOneViableQQGReadout second := by
  refine ⟨trajectoryWithRankOneChild rankOneGregariousChild,
    trajectoryWithRankOneChild rankOneTimidChild, ?_⟩
  have h : rankOneTimidChild ≠ rankOneGregariousChild :=
    Ne.symm rankOne_children_ne
  simpa [harmonicRankOneViableQQGReadout, h] using
    viableQQGScenarios_ne

/-- Gate 6's bare measurable-readout, nonconstancy, and declared-window
obligations are simultaneously inhabited.  Physical coarse graining and
emergence claims remain separate. -/
def Gate6ViableWindowReadoutClosed : Prop :=
  (∀ trajectory : ∀ n : ℕ, CausalSetGrowthBranch n,
    harmonicRankOneViableQQGReadout trajectory ∈
      viableQQGAdmissibleSector) ∧
  (∃ first second : ∀ n : ℕ, CausalSetGrowthBranch n,
    harmonicRankOneViableQQGReadout first ≠
      harmonicRankOneViableQQGReadout second)

theorem gate6ViableWindowReadout_closed :
    Gate6ViableWindowReadoutClosed :=
  ⟨harmonicRankOneViableQQGReadout_mem_admissible,
    harmonicRankOneViableQQGReadout_nonconstant⟩

/-! ## Gate 7: exact completed-ledger cardinality -/

namespace Gate7ExternalCompletionInput

variable
  {DigestAuthenticated : DatasetSource → DatasetDigest → Prop}
  {FreezePrecedesObservation :
    FreezeProvenance → ObservationTimestamp → Prop}
  {RegisteredTestValidated :
    TypedPreRegistration → ExternalResultEntry → Prop}

/-- Coverage plus unique typed identifiers forces a completed external ledger
to contain exactly the five registered results. -/
theorem results_length_eq_five
    (E : Gate7ExternalCompletionInput DigestAuthenticated
      FreezePrecedesObservation RegisteredTestValidated) :
    E.results.length = 5 := by
  have hPermutation :
      List.Perm
        (E.results.map ExternalResultEntry.predictionId) predictionIds := by
    apply (List.perm_ext_iff_of_nodup
      E.resultPredictionIdsUnique predictionIds_nodup).2
    intro id
    constructor
    · intro _
      exact predictionIds_complete id
    · intro _
      rcases E.resultsCoverAllPredictions id with ⟨result, hResult, hId⟩
      exact List.mem_map.mpr ⟨result, hResult, hId⟩
  simpa [predictionIds] using hPermutation.length_eq

/-- Every registered identifier occurs exactly once in a completed ledger. -/
theorem resultPredictionId_count_eq_one
    (E : Gate7ExternalCompletionInput DigestAuthenticated
      FreezePrecedesObservation RegisteredTestValidated)
    (id : PredictionId) :
    (E.results.map ExternalResultEntry.predictionId).count id = 1 := by
  apply List.count_eq_one_of_mem E.resultPredictionIdsUnique
  rcases E.resultsCoverAllPredictions id with ⟨result, hResult, hId⟩
  exact List.mem_map.mpr ⟨result, hResult, hId⟩

end Gate7ExternalCompletionInput

/-- Any future valid Gate-7 completion is structurally forced to contain one
and only one external result for each of the five frozen prediction IDs. -/
def Gate7ExactCompletedLedgerShapeClosed : Prop :=
  ∀ (DigestAuthenticated : DatasetSource → DatasetDigest → Prop)
    (FreezePrecedesObservation :
      FreezeProvenance → ObservationTimestamp → Prop)
    (RegisteredTestValidated :
      TypedPreRegistration → ExternalResultEntry → Prop)
    (E : Gate7ExternalCompletionInput DigestAuthenticated
      FreezePrecedesObservation RegisteredTestValidated),
    E.results.length = 5 ∧
      ∀ id : PredictionId,
        (E.results.map ExternalResultEntry.predictionId).count id = 1

theorem gate7ExactCompletedLedgerShape_closed :
    Gate7ExactCompletedLedgerShapeClosed := by
  intro _ _ _ E
  exact ⟨Gate7ExternalCompletionInput.results_length_eq_five E,
    Gate7ExternalCompletionInput.resultPredictionId_count_eq_one E⟩

/-! ## Combined strengthened formal ledger -/

/-- One constructor gathers all seven proved strengthenings.  Its Gate-2
field is relative to the supplied recovered handoff `H`; its other fields are
universal or use the explicit constructions above. -/
structure SevenGateFormalStrengthenings : Prop where
  gate1 : ∀ chirality : Fin 2, Gate1AllRankStrengthened chirality
  gate2 : ExactRecoveredChartGeometryTail H
  gate3 : Gate3ExplicitFiniteDeadlineClosed
  gate4 : ∀
    {PhysicalChart₁ PhysicalField₁ PhysicalChart₂ PhysicalField₂ : Type*}
    {IsLorentzianChart₁ : PhysicalChart₁ → Prop}
    {IsLorentzianChart₂ : PhysicalChart₂ → Prop}
    {CertificateSequenceGeneratesChart₁ :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart₁ → Prop}
    {CertificateSequenceGeneratesChart₂ :
      (ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart) →
        PhysicalChart₂ → Prop}
    {ChartGeneratesField₁ : PhysicalChart₁ → PhysicalField₁ → Prop}
    {ChartGeneratesField₂ : PhysicalChart₂ → PhysicalField₂ → Prop}
    {physicalBDGTarget₁ : PhysicalChart₁ → PhysicalField₁ → ℝ}
    {physicalBDGTarget₂ : PhysicalChart₂ → PhysicalField₂ → ℝ}
    (P : PhysicalBDGTargetIdentification H
      PhysicalChart₁ PhysicalField₁ IsLorentzianChart₁
      CertificateSequenceGeneratesChart₁ ChartGeneratesField₁
      physicalBDGTarget₁)
    (Q : PhysicalBDGTargetIdentification H
      PhysicalChart₂ PhysicalField₂ IsLorentzianChart₂
      CertificateSequenceGeneratesChart₂ ChartGeneratesField₂
      physicalBDGTarget₂),
    physicalBDGTarget₁ P.physicalChart P.physicalField =
      physicalBDGTarget₂ Q.physicalChart Q.physicalField
  gate5 : Gate5FiniteRegionalMicrocausalityClosed
  gate6 : Gate6ViableWindowReadoutClosed
  gate7 : Gate7ExactCompletedLedgerShapeClosed

theorem sevenGateFormalStrengthenings_closed :
    SevenGateFormalStrengthenings H where
  gate1 := gate1AllRankStrengthened_closed
  gate2 := exactRecoveredChartGeometryTail_closed H
  gate3 := gate3ExplicitFiniteDeadline_closed
  gate4 := gate4_sameKernel_physicalTarget_unique H
  gate5 := gate5FiniteRegionalMicrocausality_closed
  gate6 := gate6ViableWindowReadout_closed
  gate7 := gate7ExactCompletedLedgerShape_closed

#print axioms gate1AllRankStrengthened_closed
#print axioms exactRecoveredChartGeometryTail_closed
#print axioms gate3ExplicitFiniteDeadline_closed
#print axioms gate4_sameKernel_physicalTarget_unique
#print axioms gate5FiniteRegionalMicrocausality_closed
#print axioms gate6ViableWindowReadout_closed
#print axioms gate7ExactCompletedLedgerShape_closed
#print axioms sevenGateFormalStrengthenings_closed

end

end UnifiedTheory.Audit.KFTOESevenGateStrengthening
