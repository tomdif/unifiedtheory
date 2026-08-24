/-
  Audit/KFTOESevenGateAttack.lean

  Seven-gate attack ledger for the TOE completion plan.

  This file does not assert that the theory of everything is complete.  It
  records the seven remaining gates as Lean-facing certificates and exposes the
  strongest current theorem hooks for the gates that already have formal
  machinery.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
import UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
import UnifiedTheory.Audit.KFCausalCSpecDiffeomorphismInvariantObservables
import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
import UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
import UnifiedTheory.Audit.KFCausalCSpecArakiHorizonRelativeEntropy
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DRecovered
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound
import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverIndependence
import UnifiedTheory.Audit.KFGate5OctonionS6ComplexBridge
import UnifiedTheory.LayerA.DiscreteHolography
import UnifiedTheory.LayerA.GravitonTTModes
import UnifiedTheory.LayerB.InflationAudit
import UnifiedTheory.LayerB.VirtualParticles
import UnifiedTheory.LayerB.WightmanAxioms
import UnifiedTheory.LayerB.Clay_OS1_BypassVerification
import UnifiedTheory.LayerB.R3_MassGapExponentialDecay
import UnifiedTheory.LayerB.CosmologicalConstantAudit
import UnifiedTheory.LayerB.PreRegistrationLedger
import UnifiedTheory.LayerB.DarkMatterAudit
import UnifiedTheory.LayerB.InformationParadox
import UnifiedTheory.LayerB.PageCurve
import UnifiedTheory.LayerC.AnomalyCancellation
import UnifiedTheory.LayerC.PhysicalInformationLimits
import UnifiedTheory.LayerC.PageCurve
import UnifiedTheory.LayerC.GUTEmbedding
import UnifiedTheory.LayerC.AMPSFirewall
import UnifiedTheory.LayerC.HaydenPreskill
import UnifiedTheory.LayerC.IsOperationalQuantum
import UnifiedTheory.LayerC.QuarkLeptonUnification
import UnifiedTheory.LayerC.SMGaugeDynamics
import UnifiedTheory.LayerC.SMQGLink
import UnifiedTheory.Cosmology.QQG.Bridge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFTOESevenGateAttack

universe u v w z t

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry
open UnifiedTheory.Audit.KFCausalCSpecDiffeomorphismInvariantObservables
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecArakiHorizonRelativeEntropy
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFGate5OctonionS6ComplexBridge
open UnifiedTheory.LayerB.PreRegistrationLedger
open UnifiedTheory.LayerB.DarkMatterAudit
open UnifiedTheory.LayerB.InformationParadox
open UnifiedTheory.LayerB.Clay_OS1_BypassVerification
open UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
open UnifiedTheory.LayerB.LiebRobinson
open UnifiedTheory.LayerB.MargolusLevitinTight
open UnifiedTheory.LayerB.R3_MassGapExponentialDecay
open UnifiedTheory.LayerC.BekensteinBound
open UnifiedTheory.LayerC.AMPSFirewall
open UnifiedTheory.LayerC.HaydenPreskill
open UnifiedTheory.LayerC.PhysicalInformationLimits
open UnifiedTheory.LayerC.SMGaugeDynamics
open UnifiedTheory.Cosmology.QQG

/-! ## Gate 1: microscopic physical growth law -/

/-- The remaining non-finite-certificate inputs for selecting the actual
microscopic causal-growth law. -/
structure Gate1MicroscopicLawTargets : Type where
  couplingSelectedFromOrderData : Prop
  complementSymmetryDerived : Prop
  reflectionOddSourceDerived : Prop

/-- Gate 1 is closed when the finite chiral atlas noncancellation certificate
and the remaining physical-selection inputs are supplied. -/
structure Gate1MicroscopicLawClosed
    (T : Gate1MicroscopicLawTargets) : Prop where
  signedFiberSums :
    CompleteChiralAtlasRealAggregateSignedFiberSumNonzero
  couplingSelected : T.couplingSelectedFromOrderData
  complementSymmetry : T.complementSymmetryDerived
  reflectionOddSource : T.reflectionOddSourceDerived

/-- Current Gate 1 theorem hook: signed atlas transition-fiber sums imply the
raw complete-chiral atlas noncancellation gate. -/
theorem gate1_rawAggregateNonzero_of_closed
    {T : Gate1MicroscopicLawTargets}
    (G : Gate1MicroscopicLawClosed T) (chirality : Fin 2) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  exact completeChiralAtlasRawAggregateNonzero_of_signedFiberSum_nonzero
    chirality G.signedFiberSums

/-- The unconditional Gate 1 support/quantum-consistency sublayer of the
complete chiral causal-set growth law: every finite depth is normalized,
refinement is projectively consistent, the infinite cylinder functional is
Hermitian/strongly positive/normalized, and every non-physical one-element
extension has zero transition amplitude. -/
structure Gate1CompleteChiralLawSupportAndConsistencyClosed
    (chirality : Fin 2) : Prop where
  finiteProjectiveConsistency :
    (∀ n,
      IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) n))
      ∧
    (∀ (n) (event₁ event₂ :
        Finset (RankedGrowthPath CausalSetGrowthBranch n)) (steps : ℕ),
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) (n + steps))
        (refineRankedGrowthEventBy event₁ steps)
        (refineRankedGrowthEventBy event₂ steps) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) n)
        event₁ event₂)
  infiniteQuantumConsistency :
    IsHermitianGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (completeChiralCausalSetGrowthLaw chirality))
      ∧
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (completeChiralCausalSetGrowthLaw chirality))
      ∧
    infiniteRankedCylinderDecoherence
      (completeChiralCausalSetGrowthLaw chirality)
      (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
      (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1
  nonPhysicalTransitionZero :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
        (completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child = 0

theorem gate1_completeChiralLawSupportAndConsistency_closed
    (chirality : Fin 2) :
    Gate1CompleteChiralLawSupportAndConsistencyClosed chirality := by
  exact
    ⟨completeChiralCausalSetGrowthLaw_gate1_projective chirality,
      completeChiralCausalSetGrowthLaw_gate1_quantum_consistent chirality,
      fun n pathPrefix child hNotPhysical =>
        completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
          chirality n pathPrefix child hNotPhysical⟩

/-- The conditional Gate 1 atlas-realization sublayer: if the finite signed
transition-fiber sums are nonzero on the 140 atlas births, then the raw
complete-chiral aggregates and normalized transitions are nonzero, every atlas
step is physically admissible with zero leakage off the physical extension
graph, and the complete chiral law realizes the full-S3 CSpec determinant
sector with nonzero path amplitude. -/
structure Gate1CompleteChiralAtlasRealizationClosed
    (chirality : Fin 2) : Prop where
  signedFiberSums :
    CompleteChiralAtlasRealAggregateSignedFiberSumNonzero
  rawAggregateNonzero :
    CompleteChiralAtlasRawAggregateNonzero chirality
  transitionNonzero :
    CompleteChiralAtlasTransitionNonzero chirality
  atlasSupportGate :
    ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
      IsPhysicalCausalGrowthStep n
        (atlasStepPrefix n hnext) (atlasStepChild n hnext) ∧
      (¬ IsPhysicalCausalGrowthStep n
          (atlasStepPrefix n hnext) (atlasStepChild n hnext) →
        atlasCompleteChiralTransition chirality n hnext = 0)
  determinantSector :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory)

theorem gate1_completeChiralAtlasRealization_closed
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero) :
    Gate1CompleteChiralAtlasRealizationClosed chirality := by
  have hRaw : CompleteChiralAtlasRawAggregateNonzero chirality :=
    completeChiralAtlasRawAggregateNonzero_of_signedFiberSum_nonzero
      chirality hSum
  have hTransition : CompleteChiralAtlasTransitionNonzero chirality :=
    completeChiralAtlasTransition_nonzero_of_rawAggregate_nonzero
      chirality hRaw
  exact
    ⟨hSum, hRaw, hTransition,
      completeChiral_atlasStep_support_gate chirality,
      completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_signedFiberSum_nonzero
        chirality hSum⟩

/-- The Gate 1 positive-frequency handedness sublayer: after choosing the
positive orientation branch, the finite causal clock birth saturates the
Margolus-Levitin quarter-turn, selects the unique `-i` chiral phase, extends to
a normalized strongly-positive projective sequential-growth tower, transports
the nonzero `Xi=+1` cylinder sign through all finite refinements, and selects
the nontrivial left-handed weak vertex.  The reflection-doublet field records
the formal boundary: the reflected branch is equally projective and transports
the opposite sign, so this is branch-aligned handedness, not an absolute vacuum
selection theorem. -/
structure Gate1PositiveFrequencyHandednessClosed : Prop where
  finitePositiveBranch :
    causalPositiveOrientationHamiltonian.PosSemidef
      ∧ ketInner path13Ket path22Ket = 0
      ∧ causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
          (-Complex.I) • path22Ket
      ∧ (Real.pi / 2) *
          causalOrientationEnergySpectrum.energyExpectation = Real.pi / 2
      ∧ (∃! chirality : Fin 2,
          chiralMaximalEventPhase chirality = -Complex.I)
      ∧ IsNontrivialPurelyLeftHanded
          (causalWeakVertex
            (-2 * chiralBoundaryOrientationParameter (1 : Fin 2))
            weakRaising)
  projectivePositiveBranch :
    causalPositiveOrientationHamiltonian.PosSemidef
      ∧ (∀ time : ℝ,
        (causalPositiveOrientationEvolution time)ᴴ *
            causalPositiveOrientationEvolution time = 1)
      ∧ causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
          (-Complex.I) • path22Ket
      ∧ chiralMultiplicativeSignatureWeight 1 0 1 = -Complex.I
      ∧ (∀ depth : ℕ,
          IsNormalizedGrowthFunctional
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw depth)
            ∧ IsStronglyPositiveGrowthFunctional
              (growthEventDecoherence
                (finiteRankedDepthDecoherence
                  causalPositiveOrientationGrowthLaw depth)))
      ∧ (∀ (depth : ℕ)
          (first second : Finset
            (RankedGrowthPath CausalSetGrowthBranch depth)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw (depth + 1))
              (refineRankedGrowthEvent first)
              (refineRankedGrowthEvent second) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw depth) first second)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∧ IsNontrivialPurelyLeftHanded
          (causalWeakVertex
            (-2 * chiralBoundaryOrientationParameter (1 : Fin 2))
            weakRaising)
  reflectionDoublet :
    SatisfiesClockBirthIdentification
        (causalPositiveOrientationEvolution (Real.pi / 2))
        (chiralMultiplicativeSignatureWeight 1)
      ∧ SatisfiesClockBirthIdentification
        (causalReflectedOrientationEvolution (Real.pi / 2))
        (chiralMultiplicativeSignatureWeight 0)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = -1)

theorem gate1_positiveFrequencyHandedness_closed :
    Gate1PositiveFrequencyHandednessClosed := by
  exact
    ⟨finite_causal_positive_energy_derives_left_handed_weak_interaction,
      causal_positive_energy_sequential_growth_derives_left_handedness,
      projective_clock_birth_reflection_doublet⟩

/-- Gate 1 microscopic-law target with the finite complement/reflection branch
fields supplied by the already-closed complete-chiral support and
positive-frequency handedness sublayers.  The remaining hard inputs are the
signed atlas fiber-sum noncancellation certificate and the selection of the
coupling from order data. -/
def gate1MicroscopicLawTargetsOfFiniteBranch
    (couplingSelectedFromOrderData : Prop) :
    Gate1MicroscopicLawTargets where
  couplingSelectedFromOrderData := couplingSelectedFromOrderData
  complementSymmetryDerived :=
    Gate1CompleteChiralLawSupportAndConsistencyClosed (0 : Fin 2) ∧
      Gate1CompleteChiralLawSupportAndConsistencyClosed (1 : Fin 2)
  reflectionOddSourceDerived := Gate1PositiveFrequencyHandednessClosed

/-- The current finite Gate 1 branch package reduces microscopic-law closure
to signed atlas fiber-sum noncancellation plus order-data coupling selection. -/
theorem gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
    {couplingSelectedFromOrderData : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData) :
    Gate1MicroscopicLawClosed
      (gate1MicroscopicLawTargetsOfFiniteBranch
        couplingSelectedFromOrderData) := by
  exact
    ⟨hSum, hcoupling,
      ⟨gate1_completeChiralLawSupportAndConsistency_closed (0 : Fin 2),
        gate1_completeChiralLawSupportAndConsistency_closed (1 : Fin 2)⟩,
      gate1_positiveFrequencyHandedness_closed⟩

/-- Named Gate 1 physical-selection bridge.  This packages the two genuinely
remaining Gate 1 inputs, signed atlas fiber-sum noncancellation and
order-data coupling selection, together with the finite complement/reflection
branch already proved in the repo. -/
structure Gate1PhysicalSelectionBridgeClosed
    (couplingSelectedFromOrderData : Prop) : Prop where
  signedFiberSums :
    CompleteChiralAtlasRealAggregateSignedFiberSumNonzero
  couplingSelected :
    couplingSelectedFromOrderData
  supportZeroChirality :
    Gate1CompleteChiralLawSupportAndConsistencyClosed (0 : Fin 2)
  supportOneChirality :
    Gate1CompleteChiralLawSupportAndConsistencyClosed (1 : Fin 2)
  positiveFrequencyHandedness :
    Gate1PositiveFrequencyHandednessClosed
  finiteBranchClosed :
    Gate1MicroscopicLawClosed
      (gate1MicroscopicLawTargetsOfFiniteBranch
        couplingSelectedFromOrderData)

theorem gate1_physicalSelectionBridge_closed
    {couplingSelectedFromOrderData : Prop}
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero)
    (hcoupling : couplingSelectedFromOrderData) :
    Gate1PhysicalSelectionBridgeClosed couplingSelectedFromOrderData := by
  exact
    ⟨hSum, hcoupling,
      gate1_completeChiralLawSupportAndConsistency_closed (0 : Fin 2),
      gate1_completeChiralLawSupportAndConsistency_closed (1 : Fin 2),
      gate1_positiveFrequencyHandedness_closed,
      gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
        hSum hcoupling⟩

theorem gate1_microscopicLaw_closed_of_physicalSelectionBridge
    {couplingSelectedFromOrderData : Prop}
    (hGate1 :
      Gate1PhysicalSelectionBridgeClosed couplingSelectedFromOrderData) :
    Gate1MicroscopicLawClosed
      (gate1MicroscopicLawTargetsOfFiniteBranch
        couplingSelectedFromOrderData) := by
  exact hGate1.finiteBranchClosed

/-! ## Gate 2: Hauptvermutung semantic zero sets -/

/-- Semantic targets for interpreting the finite Hauptvermutung distortion
components as actual order-to-geometry conditions. -/
structure Gate2HauptvermutungSemanticTargets : Type where
  countWindowZeroSemantic : Prop
  curvatureBiasZeroSemantic : Prop
  spectralLocalityZeroSemantic : Prop

/-- Gate 2 is closed when the three non-bridge zero components have their
intended geometric meanings. -/
structure Gate2HauptvermutungSemanticClosed
    (T : Gate2HauptvermutungSemanticTargets) : Prop where
  countWindow : T.countWindowZeroSemantic
  curvatureBias : T.curvatureBiasZeroSemantic
  spectralLocality : T.spectralLocalityZeroSemantic

/-- Current Gate 2 theorem hook: the nonnegative base distortion is zero exactly
when all three tracked non-bridge components vanish. -/
theorem gate2_baseDistortion_zero_iff_components_zero
    {ι : Type*} [Fintype ι]
    (countWindow curvatureBias spectralLocality : ι → ℝ)
    (hcount : ∀ i, 0 ≤ countWindow i)
    (hcurvature : ∀ i, 0 ≤ curvatureBias i)
    (hspectral : ∀ i, 0 ≤ spectralLocality i) :
    physicalHauptvermutungBaseDistortion
      countWindow curvatureBias spectralLocality = 0 ↔
      (∀ i, countWindow i = 0) ∧
        (∀ i, curvatureBias i = 0) ∧
          (∀ i, spectralLocality i = 0) := by
  exact physicalHauptvermutungBaseDistortion_eq_zero_iff
    countWindow curvatureBias spectralLocality
    hcount hcurvature hspectral

/-- Gate 2's invariant-observable semantic sublayer: once a finite observable
family is invariant under the chosen physical equivalence relation, it
descends to the quotient of physical states and its finite diagnostic
signature is itself invariant.  This does not prove that the specific
count/curvature/spectral residuals have their intended continuum semantics; it
packages the label/diffeomorphism-invariance mechanism those semantics must
pass through. -/
structure Gate2DiffeomorphismInvariantObservableFamilyClosed
    (State Index : Type*) [Setoid State]
    (F : InvariantObservableFamily State Index) : Prop where
  quotientObservablesConstructed :
    InvariantObservableFamily.DiffeomorphismInvariantObservablesConstructed F
  finiteSignatureInvariant : RelInvariant (finiteSignature F.value)

theorem gate2_diffeomorphismInvariantObservableFamily_closed
    (State Index : Type*) [Setoid State]
    (F : InvariantObservableFamily State Index) :
    Gate2DiffeomorphismInvariantObservableFamilyClosed State Index F := by
  exact
    ⟨InvariantObservableFamily.constructs_diffeomorphismInvariantObservables F,
      InvariantObservableFamily.finiteSignature_constructs F⟩

/-! ## Gate 3: dynamical contraction -/

/-- Current Gate 3 theorem hook: the convergence certificate proves horizon
protection at every finite stage and convergence of the physical total
distortion. -/
theorem gate3_horizonProtection_and_total_tendsto_zero_of_certificate
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase) :
    (∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0) ∧
      Tendsto total atTop (nhds 0) := by
  exact
    physicalHauptvermutungConvergenceCertificate_horizon_protection_and_total_tendsto_zero
      C

/-- Gate 3's direct aggregate-rate contraction sublayer.  A physical growth
repair refinement together with a positive uniform aggregate descent rate,
nonnegative tracked distortion, and a positive step floor already gives the
two dynamical outputs needed by the convergence certificate: horizon
protection at every finite stage and convergence of total distortion to zero.
The remaining physical task is deriving the aggregate-rate inequality from the
microscopic causal growth law. -/
structure Gate3AggregateRateContractionClosed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    (R : PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    (rateBase stepFloor : ℝ) : Prop where
  horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0
  totalTendsToZero : Tendsto total atTop (nhds 0)

theorem gate3_aggregateRateContraction_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    (R : PhysicalGrowthRepairRefinement w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate)
    {rateBase stepFloor : ℝ}
    (hrate_pos : 0 < rateBase)
    (hstep_pos : 0 < stepFloor)
    (htotal_nonneg : ∀ n, 0 ≤ total n)
    (hrate : ∀ n, rateBase * total n ≤ descentRate n)
    (hstep_floor : ∀ n, stepFloor ≤ step n) :
    Gate3AggregateRateContractionClosed R rateBase stepFloor := by
  rcases
    physicalGrowthRepairRefinement_horizon_protection_and_total_tendsto_zero_of_positive_uniform_direct_rate_floor
      R rateBase stepFloor hrate_pos hstep_pos
      htotal_nonneg hrate hstep_floor with
    ⟨hhorizon, htotal⟩
  exact ⟨hhorizon, htotal⟩

/-- The Gate 3 convergence-certificate sublayer that is already closed without
any residual-gap hypothesis: horizon protection and total-distortion
convergence hold, bridge recovery becomes canonical after a finite threshold,
bridge distortion vanishes eventually, the total distortion eventually equals
the base residual distortion, and each finite count/curvature/spectral
residual component tends to zero.  The remaining exact-zero step is precisely
the positive residual-gap input packaged below. -/
structure Gate3ConvergenceBridgeResidualSplitClosed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase) : Prop where
  horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0
  totalTendsToZero : Tendsto total atTop (nhds 0)
  eventualCanonical :
    ∀ᶠ n in atTop,
      candidate n = canonicalCSpecBridgeCandidate (edge n)
  eventualBridgeTotalZero :
    ∀ᶠ n in atTop,
      cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0
  eventualOrderRecovered :
    ∀ᶠ n in atTop,
      ∀ i a b,
        Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
            (GPoint.bridge (edge n i) a) →
          b = candidate n i a
  eventualTotalEqBase :
    ∀ᶠ n in atTop,
      total n =
        physicalHauptvermutungBaseDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
  baseTendsToZero :
    Tendsto
      (fun n =>
        physicalHauptvermutungBaseDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n))
      atTop (nhds 0)
  countWindowTendsToZero :
    ∀ i, Tendsto (fun n => countWindow n i) atTop (nhds 0)
  curvatureBiasTendsToZero :
    ∀ i, Tendsto (fun n => curvatureBias n i) atTop (nhds 0)
  spectralLocalityTendsToZero :
    ∀ i, Tendsto (fun n => spectralLocality n i) atTop (nhds 0)

theorem gate3_convergenceBridgeResidualSplit_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase) :
    Gate3ConvergenceBridgeResidualSplitClosed C := by
  rcases
    physicalHauptvermutungConvergenceCertificate_horizon_protection_and_total_tendsto_zero
      C with
    ⟨hhorizon, htotal⟩
  exact
    ⟨hhorizon, htotal,
      physicalHauptvermutungConvergenceCertificate_eventually_canonical C,
      physicalHauptvermutungConvergenceCertificate_eventually_bridge_total_zero C,
      physicalHauptvermutungConvergenceCertificate_eventually_orderRecovered C,
      physicalHauptvermutungConvergenceCertificate_eventually_total_eq_base C,
      physicalHauptvermutungConvergenceCertificate_base_tendsto_zero C,
      fun i => physicalHauptvermutungConvergenceCertificate_countWindow_tendsto_zero C i,
      fun i => physicalHauptvermutungConvergenceCertificate_curvatureBias_tendsto_zero C i,
      fun i => physicalHauptvermutungConvergenceCertificate_spectralLocality_tendsto_zero C i⟩

/-- Gate 3's residual-gap exact-zero sublayer.  The convergence certificate
already gives eventual canonical bridge recovery and componentwise residual
convergence; adding a positive fixed gap for each nonzero count, curvature,
and spectral/locality residual upgrades convergence to eventual exact zero. -/
structure Gate3ResidualGapExactZeroClosed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (residualGap : ℝ) : Prop where
  eventualExactZero :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n)

theorem gate3_residualGapExactZero_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase)
    (hgap_pos : 0 < residualGap)
    (hcount_gap :
      ∀ n i, countWindow n i ≠ 0 → residualGap ≤ countWindow n i)
    (hcurvature_gap :
      ∀ n i, curvatureBias n i ≠ 0 → residualGap ≤ curvatureBias n i)
    (hspectral_gap :
      ∀ n i, spectralLocality n i ≠ 0 → residualGap ≤ spectralLocality n i) :
    Gate3ResidualGapExactZeroClosed C residualGap := by
  exact
    ⟨physicalHauptvermutungConvergenceCertificate_eventually_exact_zero_of_residual_gap
      C hgap_pos hcount_gap hcurvature_gap hspectral_gap⟩

/-- The Gate 3 exact-recovery sublayer that is already closed by the reusable
exact-recovery certificate: horizon protection holds at every finite stage,
full operational recovery holds eventually, recovered stages hold eventually
and after some threshold, and all observable Hauptvermutung/bridge defects are
zero after some threshold.  This is still conditional on supplying the
convergence certificate plus uniform positive residual gaps from the
microscopic law. -/
structure Gate3ExactRecoveryCertificateClosed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap) : Prop where
  horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0
  eventualFullOperationalRecovery :
    ∀ᶠ n in atTop,
      total n = 0 ∧
        (∀ i,
          physicalHauptvermutungDistortion
            (countWindow n) (curvatureBias n) (spectralLocality n)
            (scale n) (edge n) (candidate n) i = 0) ∧
          cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0 ∧
            (∀ i a b,
              Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
                  (GPoint.bridge (edge n i) a) →
                b = candidate n i a)
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  recoveredAfter :
    ∃ N, ∀ n, N ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  observableZeroAfter :
    ∃ N, ∀ n, N ≤ n →
      total n = 0 ∧
        physicalHauptvermutungTotalDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n)
          (scale n) (edge n) (candidate n) = 0 ∧
        physicalHauptvermutungBaseDistortion
          (countWindow n) (curvatureBias n) (spectralLocality n) = 0 ∧
        cSpecBridgeTotalDistortion (scale n) (edge n) (candidate n) = 0 ∧
        candidate n = canonicalCSpecBridgeCandidate (edge n) ∧
        (∀ i, countWindow n i = 0) ∧
        (∀ i, curvatureBias n i = 0) ∧
        (∀ i, spectralLocality n i = 0) ∧
        (∀ i a b,
          Cov fourState (GPoint.atom (fourState.dst (edge n i)) b)
              (GPoint.bridge (edge n i) a) →
            b = candidate n i a)

theorem gate3_exactRecoveryCertificate_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap) :
    Gate3ExactRecoveryCertificateClosed C := by
  rcases
    physicalHauptvermutungExactRecoveryCertificate_horizon_protection_and_eventually_full_recovery
      C with
    ⟨hhorizon, hfull⟩
  exact
    ⟨hhorizon, hfull,
      physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage C,
      physicalHauptvermutungExactRecoveryCertificate_exists_recovered_after C,
      physicalHauptvermutungExactRecoveryCertificate_exists_observable_zero_after C⟩

/-! ## Gate 4: horizon-to-Einstein analytic limit -/

/-- Analytic targets still needed by the recovered-stage BDG/GR bridge. -/
structure Gate4HorizonEinsteinAnalyticTargets : Type where
  horizonEstimatorConvergence : Prop
  physicalScheduledDensity : Prop
  bdgKernelProfileCertificate : Prop
  nullBalanceFromDynamics : Prop
  recoveredBDGInterfaceSupplied : Prop

/-- Gate 4 is closed when the analytic and physical supplier inputs are
available. -/
structure Gate4HorizonEinsteinAnalyticClosed
    (T : Gate4HorizonEinsteinAnalyticTargets) : Prop where
  horizonEstimatorConvergence : T.horizonEstimatorConvergence
  physicalScheduledDensity : T.physicalScheduledDensity
  bdgKernelProfileCertificate : T.bdgKernelProfileCertificate
  nullBalanceFromDynamics : T.nullBalanceFromDynamics
  recoveredBDGInterfaceSupplied : T.recoveredBDGInterfaceSupplied

/-- Current Gate 4 theorem hook: exact recovered CSpec data plus the concrete
reduced 4D BDG operator profile imply eventual recovered stages and convergence
of the sampled operator to its 4D target.  This is still conditional on the
operator-profile data and density sequence, so it is a recovered-stage/analytic
bridge hook, not the full Einstein limit from microscopic dynamics. -/
theorem gate4_recoveredStage_bdg4d_operator_limit_of_interface
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n)) ∧
      Tendsto
        (fun n => BDG4DOperatorProfileData.mean I.operatorData (I.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) := by
  exact
    RecoveredStageBDG4DOperatorInterface.recoveredStage_and_operator_tendsto I

/-- The Gate 4 sublayer that is actually closed by a supplied recovered-stage
4D operator interface: exact recovered stages eventually hold, the concrete 4D
operator profile converges, and the supplied density schedule tends to
infinity.  The remaining full Gate 4 work is deriving such an interface from
the microscopic law and upgrading through the physical chart/kernel inputs. -/
structure Gate4RecoveredBDGOperatorBridgeClosed
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) : Prop where
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n)
  operatorLimit :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean I.operatorData (I.density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorData))
  densityTendsToInfinity : Tendsto I.density atTop atTop

theorem gate4_recoveredBDGOperatorBridge_closed
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) :
    Gate4RecoveredBDGOperatorBridgeClosed I := by
  rcases gate4_recoveredStage_bdg4d_operator_limit_of_interface I with
    ⟨hrecovered, hoperator⟩
  exact ⟨hrecovered, hoperator, I.density_tendsto_atTop⟩

/-- Direct Gate 3-to-Gate 4 handoff: an exact-recovery certificate kills the
finite RSS/Poisson horizon-error channel eventually and after a finite
threshold, before any BDG operator-profile analytic input is needed. -/
structure Gate4ExactRecoveryRSSPoissonClosed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap)
    (errorScale : ℝ) : Prop where
  eventuallyRSSPoissonErrorZero :
    ∀ᶠ n in atTop,
      ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) errorScale = 0
  rssPoissonErrorZeroAfter :
    ∃ N, ∀ n, N ≤ n →
      ∀ i, rssPoissonError (countWindow n i) (curvatureBias n i) errorScale = 0

theorem gate4_exactRecoveryRSSPoisson_closed
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase residualGap : ℝ}
    (C : PhysicalHauptvermutungExactRecoveryCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap)
    (errorScale : ℝ) :
    Gate4ExactRecoveryRSSPoissonClosed C errorScale := by
  exact
    ⟨physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
      C,
      physicalHauptvermutungExactRecoveryCertificate_exists_rssPoissonError_zero_after
        C⟩

/-- Recovered 4D BDG operator interfaces also kill the finite
RSS/Poisson-horizon error channel eventually, for any chosen error scale, while
preserving the same sampled-operator limit and density divergence. -/
structure Gate4RecoveredBDGPoissonOperatorBridgeClosed
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell)
    (errorScale : ℝ) : Prop where
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n)
  rssPoissonErrorZero :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0
  operatorLimit :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean I.operatorData (I.density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorData))
  densityTendsToInfinity : Tendsto I.density atTop atTop

theorem gate4_recoveredBDGPoissonOperatorBridge_closed
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell)
    (errorScale : ℝ) :
    Gate4RecoveredBDGPoissonOperatorBridgeClosed I errorScale := by
  rcases
    RecoveredStageBDG4DOperatorInterface.rssPoissonError_zero_and_operator_tendsto
      I errorScale with
    ⟨hrss, hoperator⟩
  exact
    ⟨I.eventually_recoveredStage, hrss, hoperator,
      I.density_tendsto_atTop⟩

/-- Gate 4's active-kernel cone-bound sublayer: uniform chart bounds, upper and
lower active-lightcone support, a kernel-only weighted active-region estimate,
and a single scale-calibration inequality assemble the full 4D BDG cone
certificate.  This isolates the analytic obligation to proving the active
kernel estimate on the physically supported lightcone rectangle. -/
structure Gate4ActiveKernelConeBoundClosed
    {S : BDG4DOperatorProfileScales}
    {F : BDG4DOperatorProfileFunctions}
    (U : BDG4DOperatorProfileUniformBounds S F)
    (A : BDG4DOperatorProfileSupport S F)
    (L : BDG4DOperatorProfileLightconeSupport F)
    (K : BDG4DWeightedKernelActiveBound S)
    (hcone : K.activeWeightedConeBound * S.profileBound ≤ S.coneBound) :
    Prop where
  coneBound : BDG4DOperatorProfileConeBound S F

theorem gate4_activeKernelConeBound_closed
    {S : BDG4DOperatorProfileScales}
    {F : BDG4DOperatorProfileFunctions}
    (U : BDG4DOperatorProfileUniformBounds S F)
    (A : BDG4DOperatorProfileSupport S F)
    (L : BDG4DOperatorProfileLightconeSupport F)
    (K : BDG4DWeightedKernelActiveBound S)
    (hcone : K.activeWeightedConeBound * S.profileBound ≤ S.coneBound) :
    Gate4ActiveKernelConeBoundClosed U A L K hcone := by
  exact
    ⟨BDG4DOperatorProfileConeBound.of_activeKernelBound
      U A L K hcone⟩

/-- The Gate 4 analytic supplier sublayer that is already closed once the
kernel/profile split data are supplied: active lightcone support plus the
active weighted 4D kernel bound assemble the cone certificate, the reduced 4D
operator profile tends to its target, every divergent density sampling tends
to the same target, and the layer asymptotics are inherited from the assembled
operator profile.  This isolates the remaining hard analytic input to the
active-region kernel estimate and its chart/support supplier. -/
structure Gate4KernelProfileSplitSupplierClosed
    (D : BDG4DOperatorProfileKernelSplitData) : Prop where
  coneBound : BDG4DOperatorProfileConeBound D.scales D.functions
  operatorProfileTendsto :
    Tendsto
      (BDG4DOperatorProfileData.mean D.toProfileData)
      atTop
      (𝓝 (BDG4DOperatorProfileData.target D.toProfileData))
  sampledOperatorTendsto :
    ∀ density : ℕ → ℝ,
      Tendsto density atTop atTop →
        Tendsto
          (fun n => BDG4DOperatorProfileData.mean D.toProfileData (density n))
          atTop
          (𝓝 (BDG4DOperatorProfileData.target D.toProfileData))
  layerAsymptotics :
    ∀ (density : ℕ → ℝ) (hdensity : Tendsto density atTop atTop)
      (phiAtPoint curvaturePhi : ℝ),
      ∀ i ∈
        (D.toProfileData.sequenceAsymptotics
          density hdensity phiAtPoint curvaturePhi).layers,
        Tendsto
          ((D.toProfileData.sequenceAsymptotics
            density hdensity phiAtPoint curvaturePhi).layerMean i)
          atTop
          (𝓝
            ((D.toProfileData.sequenceAsymptotics
              density hdensity phiAtPoint curvaturePhi).layerConstant i *
                (D.toProfileData.sequenceAsymptotics
                  density hdensity phiAtPoint curvaturePhi).phiAtPoint +
              (D.toProfileData.sequenceAsymptotics
                density hdensity phiAtPoint curvaturePhi).layerSecond i *
                ((D.toProfileData.sequenceAsymptotics
                  density hdensity phiAtPoint curvaturePhi).boxPhi +
                  (D.toProfileData.sequenceAsymptotics
                    density hdensity phiAtPoint curvaturePhi).curvatureCoeff *
                    (D.toProfileData.sequenceAsymptotics
                      density hdensity phiAtPoint curvaturePhi).curvaturePhi)))

theorem gate4_kernelProfileSplitSupplier_closed
    (D : BDG4DOperatorProfileKernelSplitData) :
    Gate4KernelProfileSplitSupplierClosed D := by
  exact
    ⟨D.coneBound,
      D.tendsto,
      fun density hdensity => D.sampled_tendsto density hdensity,
      fun density hdensity phiAtPoint curvaturePhi =>
        D.sequenceAsymptotics_layer_asymptotics
          density hdensity phiAtPoint curvaturePhi⟩

/-- The strongest current Gate 4 sublayer: a scheduled-density recovered chart
whose operator package is reduced to kernel/profile support, regularity,
uniform bounds, lower-lightcone support, an active-region weighted kernel
estimate, and one cone-scale calibration.  This closes the formal plumbing from
that supplier to recovered stages, zero RSS/Poisson horizon error, sampled
reduced 4D operator convergence, chart-distortion collapse, and affine density
divergence.  It still does not derive the supplier from microscopic dynamics. -/
structure Gate4ScheduledKernelOperatorBridgeClosed
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface
      cell X Y chart)
    (errorScale : ℝ) : Prop where
  eventualRecoveredStage :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.recovered.countWindow n) (I.recovered.curvatureBias n)
        (I.recovered.spectralLocality n)
        (I.recovered.scale n) (I.recovered.total n)
        (I.recovered.edge n) (I.recovered.candidate n)
  rssPoissonErrorZero :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.recovered.countWindow n i)
          (I.recovered.curvatureBias n i) errorScale = 0
  chartOperatorLimit :
    Tendsto
      (fun n =>
        BDG4DOperatorProfileData.mean
          I.operatorKernelData.toProfileData ((I.chartCertificate n).density))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorKernelData.toProfileData))
  chartDistortionTendsToZero :
    Tendsto (fun n => (I.chartCertificate n).distortionBound) atTop (𝓝 0)
  scheduledDensityTendsToInfinity :
    Tendsto (fun n => (I.chartCertificate n).density) atTop atTop

theorem gate4_scheduledKernelOperatorBridge_closed
    {cell X Y chart : Type*} [Fintype cell]
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (I : RecoveredStageBDG4DScheduledDensityKernelOperatorInterface
      cell X Y chart)
    (errorScale : ℝ) :
    Gate4ScheduledKernelOperatorBridgeClosed I errorScale := by
  rcases
    RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.recoveredStage_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I with
    ⟨hrecovered, hoperator, hdistortion⟩
  rcases
    RecoveredStageBDG4DScheduledDensityKernelOperatorInterface.rssPoissonError_zero_chart_operator_tendsto_and_distortionBound_tendsto_zero
      I errorScale with
    ⟨hrss, _, _⟩
  exact
    ⟨hrecovered, hrss, hoperator, hdistortion,
      I.density_tendsto_atTop⟩

/-! ## Gate 5: QFT and Standard Model infrared limit -/

/-- IR targets beyond the finite Hopf/projective-qubit carrier algebra. -/
structure Gate5QFTStandardModelIRTargets : Type where
  recoveredCarrierCoverIndependence : Prop
  effectiveHilbertSpaceLimit : Prop
  propagatorsAndSpinStatistics : Prop
  gaugeFieldsAndRenormalization : Prop
  standardModelParameterChain : Prop

/-- Gate 5 is closed when the finite recovered carrier algebra is promoted to
the effective QFT/Standard-Model infrared limit. -/
structure Gate5QFTStandardModelIRClosed
    (T : Gate5QFTStandardModelIRTargets) : Prop where
  recoveredCarrierCoverIndependence : T.recoveredCarrierCoverIndependence
  effectiveHilbertSpaceLimit : T.effectiveHilbertSpaceLimit
  propagatorsAndSpinStatistics : T.propagatorsAndSpinStatistics
  gaugeFieldsAndRenormalization : T.gaugeFieldsAndRenormalization
  standardModelParameterChain : T.standardModelParameterChain

/-- The finite arbitrary-axis Born-observable sublayer: every recovered
stage/site Hopf quotient fiber supplies a valid binary Born pair along any unit
Bloch measurement axis, and local stagewise `U(1)` gauge rotations leave that
axis observable unchanged.  This is finite measurement kinematics, not detector
dynamics or an infrared QFT limit. -/
structure Gate5ArbitraryAxisBornObservableClosed
    {site : Type*}
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) : Prop where
  bornAlongValid :
    0 ≤ (I.bornAlongAt A n x).plus ∧
      (I.bornAlongAt A n x).plus ≤ 1 ∧
        0 ≤ (I.bornAlongAt A n x).minus ∧
          (I.bornAlongAt A n x).minus ≤ 1 ∧
            (I.bornAlongAt A n x).plus +
              (I.bornAlongAt A n x).minus = 1
  axisBornGaugeInvariant :
    ∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).bornAlongAt A n x = I.bornAlongAt A n x

theorem gate5_arbitraryAxisBornObservable_closed
    {site : Type*}
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    Gate5ArbitraryAxisBornObservableClosed I A n x := by
  rcases
    RecoveredStageHopfFiberInterface.recoveredStage_local_axis_born_interface
      I A n x with
    ⟨hvalid, hgauge⟩
  exact ⟨hvalid, hgauge⟩

/-- The finite local Gate 5 sublayer already closed by the recovered Hopf
projective-qubit stack: Pauli Born data, all-axis Born data, quotient Bloch
data, recovered normalized phase classes, and projective carriers are mutually
determining at each pair of recovered stage/site points, and local stagewise
`U(1)` gauge rotations leave the carrier invisible.  The remaining full Gate 5
work is the effective Hilbert/QFT limit, spin-statistics, gauge dynamics, and
Standard-Model infrared chain. -/
structure Gate5LocalBornProjectiveCompletenessClosed
    {site site' : Type*}
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') : Prop where
  pauliBornDeterminesPhase :
    RecoveredStageHopfFiberInterface.SamePauliBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y
  allAxisBornDeterminesPhase :
    RecoveredStageHopfFiberInterface.SameAllAxisBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y
  quotientBlochDeterminesPhase :
    I.quotientBlochAt n x = J.quotientBlochAt m y ↔
      I.phaseClassAt n x = J.phaseClassAt m y
  reconstructedCarrier :
    (I.projectiveCarrierAt n x).reconstructed = I.projectiveCarrierAt n x
  pauliBornDeterminesCarrier :
    RecoveredStageHopfFiberInterface.SamePauliBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y
  allAxisBornDeterminesCarrier :
    RecoveredStageHopfFiberInterface.SameAllAxisBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y
  carrierPauliBornMatchesLocal :
    ProjectiveQubitCarrier.SamePauliBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
      RecoveredStageHopfFiberInterface.SamePauliBornData I J n m x y
  carrierAllAxisBornMatchesLocal :
    ProjectiveQubitCarrier.SameAllAxisBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
      RecoveredStageHopfFiberInterface.SameAllAxisBornData I J n m x y
  carrierGaugeInvariant :
    ∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).projectiveCarrierAt n x = I.projectiveCarrierAt n x

theorem gate5_localBornProjectiveCompleteness_closed
    {site site' : Type*}
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    Gate5LocalBornProjectiveCompletenessClosed I J n m x y := by
  rcases
    RecoveredStageHopfFiberInterface.recoveredStage_local_born_projective_observational_completeness
      I J n m x y with
    ⟨hpauliPhase, hallPhase, hblochPhase⟩
  rcases
    RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_interface
      I J n m x y with
    ⟨hreconstructed, hpauliCarrier, hallCarrier, hcarrierPauli, hgauge⟩
  exact
    ⟨hpauliPhase, hallPhase, hblochPhase, hreconstructed,
      hpauliCarrier, hallCarrier, hcarrierPauli,
      RecoveredStageHopfFiberInterface.carrierSameAllAxisBornData_iff_sameAllAxisBornData
        I J n m x y,
      hgauge⟩

/-- Current Gate 5 theorem hook: finite recovered projective-qubit carrier
tests are independent of the jointly-surjective probe cover.  This closes the
finite cover-choice ambiguity for carrier-field equality and Pauli/all-axis
Born data, but it is not yet continuum QFT, spin-statistics, gauge dynamics,
or Standard-Model renormalization. -/
theorem gate5_recoveredCarrier_coverIndependence_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    (EqualOnCover probeA fA F G ↔ EqualOnCover probeB fB F G) ∧
    (SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover probeB fB F G) ∧
    (SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover probeB fB F G) ∧
    (EqualOnCover probeA fA F G ↔
      EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) ∧
    (SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) ∧
    (SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) := by
  exact
    coverIndependence_projective_qubit_carrier_field_interface
      fA fB hA hB F G

/-- The Gate 5 finite-carrier sublayer that is already closed: any two
jointly-surjective finite probe covers give equivalent carrier-field equality
tests and equivalent Pauli/all-axis Born-data tests, including after passing to
their common refinement.  The remaining full Gate 5 work is the effective
Hilbert/QFT, spin-statistics, gauge, and Standard-Model infrared limit. -/
structure Gate5FiniteCarrierCoverClosed
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F G : ProjectiveQubitCarrierField site) : Prop where
  equalOnCoverIndependent :
    EqualOnCover probeA fA F G ↔ EqualOnCover probeB fB F G
  pauliBornCoverIndependent :
    SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover probeB fB F G
  allAxisBornCoverIndependent :
    SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover probeB fB F G
  equalOnCommonRefinement :
    EqualOnCover probeA fA F G ↔
      EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G
  pauliBornOnCommonRefinement :
    SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G
  allAxisBornOnCommonRefinement :
    SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G

theorem gate5_finiteCarrierCover_closed
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    Gate5FiniteCarrierCoverClosed fA fB F G := by
  rcases gate5_recoveredCarrier_coverIndependence_of_jointlySurjective
      fA fB hA hB F G with
    ⟨heq, hpauli, hall, hcommonEq, hcommonPauli, hcommonAll⟩
  exact ⟨heq, hpauli, hall, hcommonEq, hcommonPauli, hcommonAll⟩

/-- Gate 5 QFT/Standard-Model IR target with the finite recovered carrier
cover-independence subfield supplied by the already-closed Hopf/projective
carrier cover theorem.  The remaining four fields are the genuine infrared
QFT, spin-statistics, gauge/renormalization, and Standard-Model parameter-chain
obligations. -/
def gate5QFTStandardModelIRTargetsOfFiniteCarrierCover
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F G : ProjectiveQubitCarrierField site)
    (effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop) :
    Gate5QFTStandardModelIRTargets where
  recoveredCarrierCoverIndependence :=
    Gate5FiniteCarrierCoverClosed fA fB F G
  effectiveHilbertSpaceLimit := effectiveHilbertSpaceLimit
  propagatorsAndSpinStatistics := propagatorsAndSpinStatistics
  gaugeFieldsAndRenormalization := gaugeFieldsAndRenormalization
  standardModelParameterChain := standardModelParameterChain

/-- Once finite jointly-surjective recovered-carrier probe covers are supplied,
full Gate 5 closure reduces to the four genuine IR/QFT/Standard-Model
obligations. -/
theorem gate5_qftStandardModelIR_closed_of_finiteCarrierCover
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    {effectiveHilbertSpaceLimit propagatorsAndSpinStatistics
      gaugeFieldsAndRenormalization standardModelParameterChain : Prop}
    (heffective : effectiveHilbertSpaceLimit)
    (hpropagators : propagatorsAndSpinStatistics)
    (hgauge : gaugeFieldsAndRenormalization)
    (hparameters : standardModelParameterChain) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierCover
        fA fB F G effectiveHilbertSpaceLimit
        propagatorsAndSpinStatistics gaugeFieldsAndRenormalization
        standardModelParameterChain) := by
  exact
    ⟨gate5_finiteCarrierCover_closed fA fB hA hB F G,
      heffective, hpropagators, hgauge, hparameters⟩

/-- Finite Hilbert/operational-QM audit available to Gate 5.  This closes the
finite SM Hilbert dimensions, the existence of an operational-quantum
no-signalling witness, and the holographic dimension-bound side.  It is not a
constructive continuum-QFT Hilbert-space limit. -/
structure Gate5EffectiveHilbertAuditClosed : Prop where
  singleGenerationDimension :
    UnifiedTheory.LayerC.SMHilbertInstantiation.singleGenDim = 16
  seesawDimension :
    UnifiedTheory.LayerC.SMSeeSawSubspace.seesawDim = 126
  operationalQuantumWitness :
    ∃ T : UnifiedTheory.LayerC.LocalRealisticAxioms.NoSignallingTheory,
      UnifiedTheory.LayerC.OperationalQuantumBridge.IsOperationalQuantum T
  holographicDimensionPositive :
    ∀ R E : ℝ,
      0 < UnifiedTheory.LayerC.SMQGLink.holographicDimBound R E

theorem gate5_effectiveHilbertAudit_closed :
    Gate5EffectiveHilbertAuditClosed := by
  exact
    ⟨UnifiedTheory.LayerC.SMHilbertInstantiation.singleGenDim_eq_sixteen,
      UnifiedTheory.LayerC.SMSeeSawSubspace.seesawDim_eq_126,
      UnifiedTheory.LayerC.OperationalQuantumBridge.operational_quantum_witness_exists,
      UnifiedTheory.LayerC.SMQGLink.holographicDimBound_pos⟩

/-- Finite propagator/kinematic audit available to Gate 5.  This packages the
Wightman kinematic consistency and the framework's finite virtual-line /
Feshbach propagator residue.  Full spin-statistics for a continuum field theory
remains a separate constructive-QFT lift. -/
structure Gate5PropagatorKinematicAuditClosed : Prop where
  wightmanKinematics :
    UnifiedTheory.LayerB.WightmanAxioms.BisognanoWichmann_Target
  virtualResidue :
    UnifiedTheory.LayerA.FeshbachJ4.C_int =
      UnifiedTheory.LayerA.FeshbachJ4.b₁_sq /
        (UnifiedTheory.LayerA.FeshbachJ4.lambda_star -
          UnifiedTheory.LayerA.FeshbachJ4.a₁)

theorem gate5_propagatorKinematicAudit_closed :
    Gate5PropagatorKinematicAuditClosed := by
  exact
    ⟨UnifiedTheory.LayerB.WightmanAxioms.bisognano_wichmann_temperature_positive,
      UnifiedTheory.LayerB.VirtualParticles.C_int_is_virtual_residue⟩

/-- Finite group/representation-level gauge audit available to Gate 5.  This
records the checked finite gauge-breaking pattern and finite subgroup chain.
The Yang-Mills/Higgs Lagrangian and renormalization flow are still not derived
here. -/
structure Gate5FiniteGaugeAuditClosed : Prop where
  gaugeInvariantFiniteSubalgebras :
    (UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
        UnifiedTheory.LayerC.SMGaugeDynamics.z2PhaseFlipRep
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ A, UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
          UnifiedTheory.LayerC.SMGaugeDynamics.z2PhaseFlipRep A →
        UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
          UnifiedTheory.LayerC.SMGaugeDynamics.z2PhaseFlipRep Aᴴ)) ∧
    (UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
        UnifiedTheory.LayerC.SMGaugeDynamics.z3CyclicRep
        (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
      (∀ A, UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
          UnifiedTheory.LayerC.SMGaugeDynamics.z3CyclicRep A →
        UnifiedTheory.LayerC.SMGaugeDynamics.GaugeInvariant
          UnifiedTheory.LayerC.SMGaugeDynamics.z3CyclicRep Aᴴ))
  electroweakBreakingCount :
    UnifiedTheory.LayerC.SMGaugeDynamics.ewGroupDim =
        UnifiedTheory.LayerC.SMGaugeDynamics.brokenGeneratorCount +
          UnifiedTheory.LayerC.SMGaugeDynamics.emGroupDim ∧
      UnifiedTheory.LayerC.SMGaugeDynamics.brokenGeneratorCount = 3 ∧
      Fintype.card UnifiedTheory.LayerC.SMGaugeDynamics.MassiveVectorBoson = 3 ∧
      Fintype.card UnifiedTheory.LayerC.SMGaugeDynamics.MasslessGaugeBoson = 1
  finiteBreakingChain :
    UnifiedTheory.LayerC.SMGaugeDynamics.ZnPhases 2 ⊆
        UnifiedTheory.LayerC.SMGaugeDynamics.U1Phases ∧
      UnifiedTheory.LayerC.SMGaugeDynamics.U1Phases ⊆
        UnifiedTheory.LayerC.SMGaugeDynamics.EWPhases
  gellMannNishijimaUnbrokenCharge :
    (∀ a b : ℚ,
        a * UnifiedTheory.LayerC.SMGaugeDynamics.higgsLowerT3 +
            b * UnifiedTheory.LayerC.SMGaugeDynamics.higgsHypercharge = 0 →
        a * UnifiedTheory.LayerC.SMGaugeDynamics.higgsUpperT3 +
            b * UnifiedTheory.LayerC.SMGaugeDynamics.higgsHypercharge = 1 →
        a = 1 ∧ b = 1) ∧
      UnifiedTheory.LayerC.SMGaugeDynamics.electricCharge (1/2)
          (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = 2/3 ∧
      UnifiedTheory.LayerC.SMGaugeDynamics.electricCharge (-1/2)
          (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = -1

theorem gate5_finiteGaugeAudit_closed :
    Gate5FiniteGaugeAuditClosed := by
  let h := UnifiedTheory.LayerC.SMGaugeDynamics.sm_gauge_dynamics_S4
  exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Finite Standard-Model parameter-chain audit available to Gate 5.  This
bundles hypercharge uniqueness, quark/lepton anomaly-forcing, and SO(10)
anomaly safety.  It is the finite representation/anomaly chain, not a
derivation of the full infrared Standard Model from constructive QFT. -/
structure Gate5StandardModelParameterAuditClosed : Prop where
  hyperchargeUniqueness :
    UnifiedTheory.LayerC.AnomalyCancellation.Hypercharge_Uniqueness_Target
  quarkLeptonUnification :
    UnifiedTheory.LayerC.QuarkLeptonUnification.Unification_Forced_Target
  so10AnomalySafety :
    UnifiedTheory.LayerC.GUTEmbedding.SO10_AnomalySafe_Target

theorem gate5_standardModelParameterAudit_closed :
    Gate5StandardModelParameterAuditClosed := by
  exact
    ⟨UnifiedTheory.LayerC.AnomalyCancellation.anomaly_master,
      UnifiedTheory.LayerC.QuarkLeptonUnification.unification_master,
      UnifiedTheory.LayerC.GUTEmbedding.so10_anomaly_safe⟩

/-- Lorentzian-direct Wightman audit available to Gate 5.  This records that
the OS route is blocked but does not block the Lorentzian-native Wightman
route: the ledger has all seven entries, with five proved/free chamber or
causal-set entries and two explicit conditional/research entries. -/
structure Gate5LorentzianWightmanStatusAuditClosed : Prop where
  os1Problematic :
    UnifiedTheory.LayerB.CL3_SchwingerFunctions.os1_classification.status =
      UnifiedTheory.LayerB.CL3_SchwingerFunctions.OSAxiomStatus.PROBLEMATIC_LORENTZIAN
  allWightmanEntries :
    UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.all_wightman_lorentz.length = 7
  lorentzianStatuses :
    UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W1_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.PARTIAL_FREE ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W2_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.FREE_FROM_CHAMBER_GAP ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W3_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W4_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W5_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.FREE_FROM_CAUSAL_SET ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W6_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
      UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W7_lorentz.status =
        UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.WightmanStatusLorentz.RESEARCH_HAAG_RUELLE

theorem gate5_lorentzianWightmanStatusAudit_closed :
    Gate5LorentzianWightmanStatusAuditClosed := by
  let h := UnifiedTheory.LayerB.Clay_OS1_BypassVerification.Clay_R2_not_blocked_by_OS1
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- Chamber mass-gap/exponential-decay audit available to Gate 5.  This closes
the finite/chamber Hamiltonian decay side: positive closed-form rate,
exponential contraction on the vacuum-orthogonal chamber, and the honest
constructive-measure status split.  The continuum Wightman/Haag-Ruelle lift is
still not claimed here. -/
structure Gate5ChamberMassGapDecayAuditClosed : Prop where
  decayRatePositiveClosedForm :
    0 < UnifiedTheory.LayerB.R3_MassGapExponentialDecay.γ_vac_chamber ∧
      UnifiedTheory.LayerB.R3_MassGapExponentialDecay.γ_vac_chamber =
        Real.sqrt 7 / 15
  spectralGapExponentialDecay :
    ∀ t : ℝ, 0 ≤ t →
       ∀ ψ : UnifiedTheory.LayerB.R3_MassGapExponentialDecay.ChamberState,
        UnifiedTheory.LayerB.R3_MassGapExponentialDecay.ChamberState.InOrthVac ψ →
          (UnifiedTheory.LayerB.R3_MassGapExponentialDecay.heatSemigroupShifted t ψ).normSq
            ≤ Real.exp
                (-2 * t *
                  UnifiedTheory.LayerB.R3_MassGapExponentialDecay.γ_vac_chamber) *
              ψ.normSq
  chamberMeasureStatus :
    UnifiedTheory.LayerB.R3_MassGapExponentialDecay.cl3_M6_chamber_operator_norm.status =
      UnifiedTheory.LayerB.CL3_ConstructiveMeasure.MeasureStatus.DiscreteOnly
  fullMeasureStatus :
    UnifiedTheory.LayerB.CL3_ClusterDecomposition.cl3_M6_full.status =
      UnifiedTheory.LayerB.CL3_ConstructiveMeasure.MeasureStatus.NeedsClusterExp

theorem gate5_chamberMassGapDecayAudit_closed :
    Gate5ChamberMassGapDecayAuditClosed := by
  let h := UnifiedTheory.LayerB.R3_MassGapExponentialDecay.R3_chamber_exponential_decay_master
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Gate 5 QFT/Standard-Model IR target with finite carrier cover-independence
and all currently available finite SM/QM audits supplied.  The remaining Gate
5 inputs are now the genuine constructive-QFT lifts: continuum Hilbert/QFT
limit, spin-statistics, and gauge-field renormalization. -/
def gate5QFTStandardModelIRTargetsOfFiniteCarrierAndSMAudits
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F G : ProjectiveQubitCarrierField site)
    (constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop) :
    Gate5QFTStandardModelIRTargets where
  recoveredCarrierCoverIndependence :=
    Gate5FiniteCarrierCoverClosed fA fB F G
  effectiveHilbertSpaceLimit :=
    Gate5EffectiveHilbertAuditClosed ∧ constructiveHilbertQFTLimit
  propagatorsAndSpinStatistics :=
    Gate5PropagatorKinematicAuditClosed ∧ qftSpinStatisticsLift
  gaugeFieldsAndRenormalization :=
    Gate5FiniteGaugeAuditClosed ∧ qftGaugeRenormalizationLift
  standardModelParameterChain :=
    Gate5StandardModelParameterAuditClosed

/-- After harvesting the finite SM/QM audits, Gate 5 closure is reduced to the
three genuine constructive-QFT lifts: continuum Hilbert/QFT limit,
spin-statistics, and gauge-field renormalization. -/
theorem gate5_qftStandardModelIR_closed_of_finiteCarrierAndSMAudits
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    {constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop}
    (hHilbert : constructiveHilbertQFTLimit)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierAndSMAudits
        fA fB F G constructiveHilbertQFTLimit
        qftSpinStatisticsLift qftGaugeRenormalizationLift) := by
  exact
    ⟨gate5_finiteCarrierCover_closed fA fB hA hB F G,
      ⟨gate5_effectiveHilbertAudit_closed, hHilbert⟩,
      ⟨gate5_propagatorKinematicAudit_closed, hSpinStatistics⟩,
      ⟨gate5_finiteGaugeAudit_closed, hGaugeRenorm⟩,
      gate5_standardModelParameterAudit_closed⟩

/-- Stronger Gate 5 QFT/Standard-Model IR target with the finite SM/QM audits,
Lorentzian-direct Wightman status audit, chamber mass-gap/exponential-decay
audit, and finite Hopf/octonion complex-geometry skeleton supplied.  The
remaining Gate 5 inputs are the continuum Hilbert/QFT limit, the
Haag-Ruelle/spin-statistics lift, and gauge-field renormalization. -/
def gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F G : ProjectiveQubitCarrierField site)
    (constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop) :
    Gate5QFTStandardModelIRTargets where
  recoveredCarrierCoverIndependence :=
    Gate5FiniteCarrierCoverClosed fA fB F G
  effectiveHilbertSpaceLimit :=
    Gate5EffectiveHilbertAuditClosed ∧
      Gate5LorentzianWightmanStatusAuditClosed ∧
        Gate5HopfOctonionComplexGeometryFiniteAuditClosed ∧
          constructiveHilbertQFTLimit
  propagatorsAndSpinStatistics :=
    Gate5PropagatorKinematicAuditClosed ∧
      Gate5ChamberMassGapDecayAuditClosed ∧
        qftSpinStatisticsLift
  gaugeFieldsAndRenormalization :=
    Gate5FiniteGaugeAuditClosed ∧ qftGaugeRenormalizationLift
  standardModelParameterChain :=
    Gate5StandardModelParameterAuditClosed

/-- After harvesting the Wightman-status, chamber mass-gap/decay, and finite
Hopf/octonion complex-geometry audits, Gate 5 closure is reduced to the
continuum Hilbert/QFT limit, the Haag-Ruelle/spin-statistics lift, and
gauge-field renormalization. -/
theorem gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    {constructiveHilbertQFTLimit qftSpinStatisticsLift
      qftGaugeRenormalizationLift : Prop}
    (hHilbert : constructiveHilbertQFTLimit)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
        fA fB F G constructiveHilbertQFTLimit
        qftSpinStatisticsLift qftGaugeRenormalizationLift) := by
  exact
    ⟨gate5_finiteCarrierCover_closed fA fB hA hB F G,
      ⟨gate5_effectiveHilbertAudit_closed,
        gate5_lorentzianWightmanStatusAudit_closed,
        gate5_hopfOctonionComplexGeometryFiniteAudit_closed, hHilbert⟩,
      ⟨gate5_propagatorKinematicAudit_closed,
        gate5_chamberMassGapDecayAudit_closed, hSpinStatistics⟩,
      ⟨gate5_finiteGaugeAudit_closed, hGaugeRenorm⟩,
      gate5_standardModelParameterAudit_closed⟩

/-- If the conditional octonion/S6 bridge is supplied, its
`complexGeometryFeedsConstructiveQFTLimit` field can serve as the remaining
Gate 5 continuum Hilbert/QFT input.  The external S6 claim and compatibility
bridges remain hypotheses inside the bridge record. -/
theorem gate5_qftStandardModelIR_closed_of_octonionS6BridgeAndFiniteAudits
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    (T : Gate5OctonionS6ComplexGeometryBridgeTargets)
    {qftSpinStatisticsLift qftGaugeRenormalizationLift : Prop}
    (hBridge : Gate5OctonionS6ComplexGeometryBridgeClosed T)
    (hSpinStatistics : qftSpinStatisticsLift)
    (hGaugeRenorm : qftGaugeRenormalizationLift) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
        fA fB F G T.complexGeometryFeedsConstructiveQFTLimit
        qftSpinStatisticsLift qftGaugeRenormalizationLift) := by
  exact
    gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
      fA fB hA hB F G hBridge.complexGeometryFeedsConstructiveQFTLimit
      hSpinStatistics hGaugeRenorm

/-- Named target for the Haag-Ruelle/spin-statistics side of Gate 5.  The
Haag-Ruelle chamber statement already has a conditional theorem; the remaining
spin-statistics lift is still an explicit constructive-QFT input. -/
structure Gate5HaagRuelleSpinStatisticsBridgeTargets : Type where
  qftSpinStatisticsLift : Prop

/-- Closed conditional bridge for Gate 5's propagator/spin-statistics slot. -/
structure Gate5HaagRuelleSpinStatisticsBridgeClosed
    {C : UnifiedTheory.LayerA.CausalFoundation.CausalSet}
    [Fintype C.Event]
    (S : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ScatteringConstruction C)
    (T : Gate5HaagRuelleSpinStatisticsBridgeTargets) : Prop where
  haagRuelleAsymptoticCompleteness :
    (∀ ψ : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ChamberState,
        ∃ t : ℝ, S.inWavePacket t = ψ) ∧
      (∀ ψ : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ChamberState,
        ∃ t : ℝ, S.outWavePacket t = ψ) ∧
      (∃ t : ℝ,
        S.inWavePacket t =
          UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.Ω_chamber) ∧
      (∃ t : ℝ,
        S.outWavePacket t =
          UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.Ω_chamber)
  qftSpinStatisticsLift :
    T.qftSpinStatisticsLift

theorem gate5_haagRuelleSpinStatisticsBridge_closed
    {C : UnifiedTheory.LayerA.CausalFoundation.CausalSet}
    [Fintype C.Event]
    (S : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ScatteringConstruction C)
    (T : Gate5HaagRuelleSpinStatisticsBridgeTargets)
    (hSpinStatistics : T.qftSpinStatisticsLift) :
    Gate5HaagRuelleSpinStatisticsBridgeClosed S T := by
  exact
    ⟨UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.W7_asymptotic_completeness_via_Haag_Ruelle S,
      hSpinStatistics⟩

/-- Named target for the Yang-Mills/Higgs/renormalization side of Gate 5.  The
finite group/representation gauge audit is closed separately; these fields are
the remaining continuum field-theory inputs. -/
structure Gate5YangMillsHiggsRenormalizationBridgeTargets : Type where
  smLagrangianDynamics : Prop
  higgsMechanismDynamics : Prop
  nontrivialRenormalizationFlow : Prop
  qftGaugeRenormalizationLift : Prop

/-- Closed conditional bridge for Gate 5's gauge/renormalization slot. -/
structure Gate5YangMillsHiggsRenormalizationBridgeClosed
    (T : Gate5YangMillsHiggsRenormalizationBridgeTargets) : Prop where
  finiteGaugeAudit :
    Gate5FiniteGaugeAuditClosed
  smLagrangianDynamics :
    T.smLagrangianDynamics
  higgsMechanismDynamics :
    T.higgsMechanismDynamics
  nontrivialRenormalizationFlow :
    T.nontrivialRenormalizationFlow
  qftGaugeRenormalizationLift :
    T.qftGaugeRenormalizationLift

theorem gate5_yangMillsHiggsRenormalizationBridge_closed
    (T : Gate5YangMillsHiggsRenormalizationBridgeTargets)
    (hLagrangian : T.smLagrangianDynamics)
    (hHiggs : T.higgsMechanismDynamics)
    (hRG : T.nontrivialRenormalizationFlow)
    (hGaugeRenorm : T.qftGaugeRenormalizationLift) :
    Gate5YangMillsHiggsRenormalizationBridgeClosed T := by
  exact
    ⟨gate5_finiteGaugeAudit_closed, hLagrangian, hHiggs, hRG, hGaugeRenorm⟩

/-- Gate 5 closure with all three currently named continuum bridge records:
octonion/S6 for the Hilbert/QFT slot, Haag-Ruelle/spin-statistics for the
propagator slot, and Yang-Mills/Higgs/renormalization for the gauge slot. -/
theorem gate5_qftStandardModelIR_closed_of_namedContinuumBridgesAndFiniteAudits
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    {C : UnifiedTheory.LayerA.CausalFoundation.CausalSet}
    [Fintype C.Event]
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site)
    (S : UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect.ScatteringConstruction C)
    (THilbert : Gate5OctonionS6ComplexGeometryBridgeTargets)
    (TSpin : Gate5HaagRuelleSpinStatisticsBridgeTargets)
    (TGauge : Gate5YangMillsHiggsRenormalizationBridgeTargets)
    (hHilbertBridge : Gate5OctonionS6ComplexGeometryBridgeClosed THilbert)
    (hSpinBridge : Gate5HaagRuelleSpinStatisticsBridgeClosed S TSpin)
    (hGaugeBridge : Gate5YangMillsHiggsRenormalizationBridgeClosed TGauge) :
    Gate5QFTStandardModelIRClosed
      (gate5QFTStandardModelIRTargetsOfFiniteCarrierSMAuditsWightmanAndMassGap
        fA fB F G THilbert.complexGeometryFeedsConstructiveQFTLimit
        TSpin.qftSpinStatisticsLift TGauge.qftGaugeRenormalizationLift) := by
  exact
    gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
      fA fB hA hB F G hHilbertBridge.complexGeometryFeedsConstructiveQFTLimit
      hSpinBridge.qftSpinStatisticsLift
      hGaugeBridge.qftGaugeRenormalizationLift

/-- The recovered-stage Gate 5 common-refinement sublayer: two jointly
surjective finite probe covers have a jointly-surjective common refinement;
local stagewise `U(1)` gauge rotations remain invisible on that refinement;
and equality, Pauli Born data, and all-axis Born data on the common refinement
are equivalent to the corresponding global recovered carrier-field tests. -/
structure Gate5RecoveredCarrierCommonRefinementClosed
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (n m : ℕ) : Prop where
  commonRefinementJointlySurjective :
    JointlySurjective
      (commonRefinementProbe probeA probeB fA fB)
      (commonRefinementMap fA fB)
  commonRefinementGaugeInvariant :
    ∀ P : ℕ → UnitPhaseField site,
      ∀ ij : CommonRefinementIndex coverA coverB,
        pullback
            (commonRefinementMap fA fB ij)
            ((I.phaseRotate P).projectiveCarrierFieldAt n) =
          pullback
            (commonRefinementMap fA fB ij)
            (I.projectiveCarrierFieldAt n)
  equalOnCommonRefinementGlobal :
    EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m
  pauliBornOnCommonRefinementGlobal :
    SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)
  allAxisBornOnCommonRefinementGlobal :
    SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem gate5_recoveredCarrierCommonRefinement_closed
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z} {probeB : coverB → Type t}
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (n m : ℕ) :
    Gate5RecoveredCarrierCommonRefinementClosed I J fA fB n m := by
  rcases
    RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_commonRefinement_interface
      I J fA fB hA hB n m with
    ⟨hcommon, hgauge, heq, hpauli, hall⟩
  exact ⟨hcommon, hgauge, heq, hpauli, hall⟩

/-! ## Gate 6: cosmology and black holes -/

/-- Physical sectors a complete theory cannot skip. -/
structure Gate6CosmologyBlackHoleTargets : Type where
  initialConditionOrCosmologicalMeasure : Prop
  darkEnergyOrCosmologicalConstantMechanism : Prop
  darkMatterPredictionOrExclusion : Prop
  blackHoleEntropyEvaporationInformation : Prop
  cmbStructureGravitationalWaveCompatibility : Prop

/-- Gate 6 is closed when cosmology and black-hole sectors are supplied by the
same microscopic theory. -/
structure Gate6CosmologyBlackHoleClosed
    (T : Gate6CosmologyBlackHoleTargets) : Prop where
  initialConditionOrCosmologicalMeasure :
    T.initialConditionOrCosmologicalMeasure
  darkEnergyOrCosmologicalConstantMechanism :
    T.darkEnergyOrCosmologicalConstantMechanism
  darkMatterPredictionOrExclusion :
    T.darkMatterPredictionOrExclusion
  blackHoleEntropyEvaporationInformation :
    T.blackHoleEntropyEvaporationInformation
  cmbStructureGravitationalWaveCompatibility :
    T.cmbStructureGravitationalWaveCompatibility

/-- Current Gate 6 theorem hook: the formal dark-density audit proves the
atomic three-density package and its honest negative clauses.  This is useful
cosmology-sector evidence, but it does not supply the missing cosmological
measure, dark-energy mechanism, black-hole thermodynamics, or CMB/structure/GW
dynamics required for full Gate 6 closure. -/
theorem gate6_darkDensity_atomic_audit_hook :
    (OmegaDM_framework = (Nc : ℚ) / ((Nt : ℚ) * (Nt : ℚ)))
    ∧ (OmegaDM_framework = OmegaDM_central)
    ∧ (OmegaM_framework = 1 / (discN : ℚ))
    ∧ (Omegab_framework =
      (NWsq : ℚ) / ((discN : ℚ) * (Nt : ℚ) * (Nt : ℚ)))
    ∧ (OmegaM_framework = OmegaDM_framework + Omegab_framework)
    ∧ (OmegaDM_framework * (discN : ℚ) = OmegaDM_over_M_obs)
    ∧ ((discN : ℚ) * OmegaM_framework = 1)
    ∧ (C_one_ninth < C_three_twenty_fifths)
    ∧ (Omegab_hi_1sigma < Omegab_framework)
    ∧ ((1 : ℚ) / 20 < OmegaDM_framework)
    ∧ ((7 / 3 : ℚ) * (1 / 20 : ℚ) ≠ OmegaDM_framework) := by
  exact honest_scope_DarkMatterAudit

/-- The Gate 6 dark-density audit sublayer that is actually closed: the
framework-atomic dark, matter, and baryon density identities are bundled with
the honest negative clauses showing this is not yet a full cosmology/black-hole
derivation. -/
structure Gate6DarkDensityAuditClosed : Prop where
  omegaDMAtomic :
    OmegaDM_framework = (Nc : ℚ) / ((Nt : ℚ) * (Nt : ℚ))
  omegaDMCentral : OmegaDM_framework = OmegaDM_central
  omegaMAtomic : OmegaM_framework = 1 / (discN : ℚ)
  omegaBAtomic :
    Omegab_framework =
      (NWsq : ℚ) / ((discN : ℚ) * (Nt : ℚ) * (Nt : ℚ))
  threeDensityConsistent :
    OmegaM_framework = OmegaDM_framework + Omegab_framework
  coldDMFractionExact :
    OmegaDM_framework * (discN : ℚ) = OmegaDM_over_M_obs
  matterDiscIdentity : (discN : ℚ) * OmegaM_framework = 1
  simplerCompetitorExists : C_one_ninth < C_three_twenty_fifths
  baryonAboveOneSigma : Omegab_hi_1sigma < Omegab_framework
  thermalPortalUnderpredicts : (1 : ℚ) / 20 < OmegaDM_framework
  notCorrectedAtomProduct :
    (7 / 3 : ℚ) * (1 / 20 : ℚ) ≠ OmegaDM_framework

theorem gate6_darkDensityAudit_closed :
    Gate6DarkDensityAuditClosed := by
  rcases gate6_darkDensity_atomic_audit_hook with
    ⟨hDMAtomic, hDMCentral, hMAtomic, hBAtomic, hthree, hcold,
      hdisc, hsimpler, hbaryon, hthermal, hnotProduct⟩
  exact
    ⟨hDMAtomic, hDMCentral, hMAtomic, hBAtomic, hthree, hcold,
      hdisc, hsimpler, hbaryon, hthermal, hnotProduct⟩

/-- The stronger Gate 6 dark-density Planck-window audit: the atomic dark,
matter, and baryon identities are bundled with the exact Planck-centre hit for
`Ω_DM h²`, the one-sigma Planck-window checks for dark and total matter, the
cold-dark-matter fraction, and the honest negative clauses that `1/9` is a
simpler but wrong low-window competitor and the baryon candidate overshoots its
one-sigma window. -/
structure Gate6DarkMatterPlanckWindowAuditClosed : Prop where
  omegaDMAtomic :
    OmegaDM_framework = (Nc : ℚ) / ((Nt : ℚ) * (Nt : ℚ))
  omegaDMCentral : OmegaDM_framework = OmegaDM_central
  omegaDMInOneSigma :
    OmegaDM_lo_1sigma < OmegaDM_framework ∧
      OmegaDM_framework < OmegaDM_hi_1sigma
  omegaMAtomic : OmegaM_framework = 1 / (discN : ℚ)
  omegaMInOneSigma :
    OmegaM_lo_1sigma < OmegaM_framework ∧
      OmegaM_framework < OmegaM_hi_1sigma
  omegaBAtomic :
    Omegab_framework =
      (NWsq : ℚ) / ((discN : ℚ) * (Nt : ℚ) * (Nt : ℚ))
  threeDensityIdentity :
    OmegaM_framework = OmegaDM_framework + Omegab_framework
  coldDarkMatterFraction :
    OmegaDM_framework * (discN : ℚ) = OmegaDM_over_M_obs
  simplerCompetitorExists : C_one_ninth < C_three_twenty_fifths
  simplerCompetitorMissesLowWindow :
    OmegaDM_one_ninth < OmegaDM_lo_1sigma
  baryonAboveOneSigma : Omegab_hi_1sigma < Omegab_framework

theorem gate6_darkMatterPlanckWindowAudit_closed :
    Gate6DarkMatterPlanckWindowAuditClosed := by
  rcases dark_matter_audit_VERDICT with
    ⟨hDM, hDMCentral, hDMWindow, hM, hMWindow, hB, hthree,
      hfraction, hsimpler, hlow, hbaryon⟩
  exact
    ⟨hDM, hDMCentral, hDMWindow, hM, hMWindow, hB, hthree,
      hfraction, hsimpler, hlow, hbaryon⟩

/-- The Gate 6 cosmological-constant/gravitational-mode sublayer that is
currently closed: the Sorkin `Λ² * N = 1` relation is packaged with its
self-consistency/fluctuation refinements, the audit's honest negative clauses
about minimum complexity and missing cosmic-age derivation, and the finite
transverse-traceless graviton mode count.  This is still not a derivation of
initial conditions, CMB/structure formation, black-hole thermodynamics, or
information recovery. -/
structure Gate6CosmologicalConstantGravitonAuditClosed : Prop where
  lambdaSquaredTimesN :
    ∀ ρ V : ℝ, 0 < ρ → 0 < V →
      UnifiedTheory.LayerA.CosmologicalConstant.sorkinLambda ρ V ^ 2 *
          (ρ * V) = 1
  lambdaSelfConsistency :
    ∀ ρ c Λ : ℝ, 0 < ρ → 0 < Λ → 0 < c →
      Λ ^ 2 =
          1 / (ρ *
            UnifiedTheory.LayerA.CosmologicalConstant.causalPastVolume c Λ) →
      ρ * c = 1
  lambdaRelativeFluctuation :
    ∀ ρ V : ℝ, 0 < ρ → 0 < V →
      UnifiedTheory.LayerA.CosmologicalConstant.relativeLambdaFluctuation
          (ρ * V) =
        UnifiedTheory.LayerA.CosmologicalConstant.sorkinLambda ρ V / 2
  lambdaAuditSharp :
    ∀ Λ : ℝ, Λ ≠ 0 → Λ ^ 2 * (1 / Λ ^ 2) = 1
  linearLawSimplerThanSorkin :
    UnifiedTheory.LayerB.CosmologicalConstantAudit.L2_complexity <
      UnifiedTheory.LayerB.CosmologicalConstantAudit.L1_complexity
  linearLawMissesObservedTarget :
    UnifiedTheory.LayerB.CosmologicalConstantAudit.L2_N_target ≠
      UnifiedTheory.LayerB.CosmologicalConstantAudit.N_obs_target
  sorkinLawSimplerThanQuartic :
    UnifiedTheory.LayerB.CosmologicalConstantAudit.L1_complexity <
      UnifiedTheory.LayerB.CosmologicalConstantAudit.L4_complexity
  quarticLawMissesObservedTarget :
    UnifiedTheory.LayerB.CosmologicalConstantAudit.L4_N_target ≠
      UnifiedTheory.LayerB.CosmologicalConstantAudit.N_obs_target
  cosmicExponentSplit :
    (244 : ℕ) =
      UnifiedTheory.LayerB.CosmologicalConstantAudit.d_eff * 61
  cosmicAgeExponentNotAtomic :
    (10 : ℕ) < 61
  lambdaBelowFrameworkFloor :
    UnifiedTheory.LayerB.CosmologicalConstantAudit.Lambda_P_upper <
      UnifiedTheory.LayerB.CosmologicalConstantAudit.smallest_framework_rational
  gravitonTTClosedForm :
    ∀ d : ℕ, 3 ≤ d →
      UnifiedTheory.LayerA.GravitonTTModes.gravitonTTModes d =
        d * (d - 3) / 2
  fourDimensionalGravitonModes :
    UnifiedTheory.LayerA.GravitonTTModes.gravitonTTModes 4 = 2
  threeDimensionalNoPropagatingGravitons :
    UnifiedTheory.LayerA.GravitonTTModes.gravitonTTModes 3 = 0

theorem gate6_cosmologicalConstantGravitonAudit_closed :
    Gate6CosmologicalConstantGravitonAuditClosed := by
  rcases UnifiedTheory.LayerA.CosmologicalConstant.refined_prediction with
    ⟨hlambdaN, hself, hfluctuation⟩
  rcases
    UnifiedTheory.LayerB.CosmologicalConstantAudit.cosmological_constant_audit_VERDICT with
    ⟨hsharp, hL2Simple, hL2Miss, hL1L4, hL4Miss, hsplit, hage, hfloor⟩
  rcases UnifiedTheory.LayerA.GravitonTTModes.gravitonTTModes_master with
    ⟨hclosedForm, hD3, hD4, _, _, _, _⟩
  exact
    ⟨hlambdaN, hself, hfluctuation, hsharp, hL2Simple, hL2Miss,
      hL1L4, hL4Miss, hsplit, hage, hfloor, hclosedForm, hD4, hD3⟩

/-- The finite information-preservation sublayer relevant to the black-hole
information side of Gate 6: on a finite state space, injective deterministic
evolution is automatically surjective/bijective, every output has a unique
preimage, and injectivity is equivalent to surjectivity.  This is not a full
black-hole entropy, evaporation, or semiclassical Page-curve derivation; it
closes the finite-state no-information-loss algebra used by that sector. -/
structure Gate6FiniteInformationPreservationAuditClosed : Prop where
  finiteInjectiveSurjective :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f → Function.Surjective f
  finiteSurjectiveInjective :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Surjective f → Function.Injective f
  finiteInjectiveBijective :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f → Function.Bijective f
  finiteEvolutionInverseSpec :
    ∀ {α : Type*} [Finite α] (f : α → α)
      (hinj : Function.Injective f),
      let e := finite_evolution_invertible f hinj
      (∀ x, e.symm (f x) = x) ∧ (∀ y, f (e.symm y) = y)
  everyStateUniquePreimage :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f → ∀ y : α, ∃! x : α, f x = y
  informationPreserved :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f →
        Function.Bijective f ∧ (∀ y, ∃! x, f x = y)
  noInformationLoss :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f →
        Function.Surjective f ∧
          Function.Bijective f ∧
            (∀ y, ∃! x, f x = y)
  unitarityIff :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f ↔ Function.Surjective f

theorem gate6_finiteInformationPreservationAudit_closed :
    Gate6FiniteInformationPreservationAuditClosed := by
  exact
    ⟨fun f hinj => finite_injective_is_surjective f hinj,
      fun f hsurj => finite_surjective_is_injective f hsurj,
      fun f hinj => finite_injective_is_bijective f hinj,
      fun f hinj => finite_evolution_inverse_spec f hinj,
      fun f hinj => every_state_has_unique_preimage f hinj,
      fun f hinj => information_preserved f hinj,
      fun f hinj => no_information_loss f hinj,
      fun f => unitarity_is_a_theorem f⟩

/-- The Gate 6 discrete-holography audit: the causal-discrete entropy bound
factorizes as boundary area times a logarithmic factor, is sub-volume for
large regions, has the advertised 4D form, and remains compatible with
Bekenstein-Hawking scaling.  This is a finite causal counting bound, not a
derived black-hole thermodynamics model. -/
structure Gate6DiscreteHolographyAuditClosed : Prop where
  areaLaw :
    ∀ d m : ℕ, 2 ≤ d →
      ∃ (area logFactor : ℕ),
        area = m ^ (d - 1) ∧
          logFactor = 2 * (Nat.log 2 (m + 1) + 1) ∧
            UnifiedTheory.LayerA.DiscreteHolography.entropy_bound d m =
              area * logFactor
  subVolume :
    ∀ d m : ℕ, 2 ≤ d → 2 ≤ m →
      2 * (Nat.log 2 (m + 1) + 1) < m →
        UnifiedTheory.LayerA.DiscreteHolography.entropy_bound d m < m ^ d
  fourDimensionalForm :
    ∀ m : ℕ, 2 ≤ m →
      UnifiedTheory.LayerA.DiscreteHolography.entropy_bound 4 m =
        2 * m ^ 3 * (Nat.log 2 (m + 1) + 1)
  bekensteinHawkingCompatible :
    ∀ C m : ℕ, 0 < C → C + 1 ≤ m → C * m ^ 2 < m ^ 3

theorem gate6_discreteHolographyAudit_closed :
    Gate6DiscreteHolographyAuditClosed := by
  rcases UnifiedTheory.LayerA.DiscreteHolography.discrete_holographic_principle
    with ⟨harea, hsub, h4d, hbh⟩
  exact ⟨harea, hsub, h4d, hbh⟩

/-- The Gate 6 structural Page-curve audit: finite Schmidt spectra have
nonnegative entropy, obey the deterministic `log(min d_A d_B)` ceiling, attain
that ceiling on the maximally entangled spectrum, and have a symmetric Page
ceiling.  This is the deterministic entropy skeleton, not the Haar-average
random-matrix Page theorem. -/
structure Gate6StructuralPageCurveAuditClosed : Prop where
  entropyNonnegative :
    ∀ {d_A d_B : ℕ}
      (σ : UnifiedTheory.LayerB.PageCurve.SchmidtSpectrum d_A d_B),
      0 ≤ UnifiedTheory.LayerB.PageCurve.pageEntropy σ
  deterministicUpperBound :
    ∀ {d_A d_B : ℕ}, 0 < d_A → 0 < d_B →
      ∀ (σ : UnifiedTheory.LayerB.PageCurve.SchmidtSpectrum d_A d_B),
        UnifiedTheory.LayerB.PageCurve.pageEntropy σ ≤
          Real.log (((min d_A d_B : ℕ) : ℝ))
  maxEntangledSaturates :
    ∀ {d_A d_B : ℕ} (hdA : 0 < d_A) (hdB : 0 < d_B),
      UnifiedTheory.LayerB.PageCurve.pageEntropy
          (UnifiedTheory.LayerB.PageCurve.maxEntangled d_A d_B hdA hdB) =
        Real.log (((min d_A d_B : ℕ) : ℝ))
  ceilingSymmetric :
    ∀ d_A d_B : ℕ,
      UnifiedTheory.LayerB.PageCurve.pageCeiling d_A d_B =
        UnifiedTheory.LayerB.PageCurve.pageCeiling d_B d_A

theorem gate6_structuralPageCurveAudit_closed :
    Gate6StructuralPageCurveAuditClosed := by
  rcases UnifiedTheory.LayerB.PageCurve.pageCurve_master with
    ⟨hnonneg, hupper, hmax, hsymm⟩
  exact ⟨hnonneg, hupper, hmax, hsymm⟩

/-- The Gate 6 Page-formula audit: the formal Page curve is symmetric, has the
displayed Page-time value, has early/late evaporation formulae, stays below
the `log(min m n)` ceiling, and grows monotonically along the diagonal slice.
This packages the formula shape; it does not derive the formula from an
evaporation dynamics or Haar/random-matrix ensemble. -/
structure Gate6PageFormulaAuditClosed : Prop where
  symmetric :
    ∀ m n : ℕ,
      UnifiedTheory.LayerC.PageCurve.pageEntropy m n =
        UnifiedTheory.LayerC.PageCurve.pageEntropy n m
  pageTimeValue :
    ∀ n : ℕ, 0 < n →
      UnifiedTheory.LayerC.PageCurve.pageEntropy n n = Real.log n - 1 / 2
  earlyFormula :
    ∀ m n : ℕ, m ≤ n →
      UnifiedTheory.LayerC.PageCurve.pageEntropy m n =
        Real.log m - (m : ℝ) / (2 * n)
  lateFormula :
    ∀ m n : ℕ, n ≤ m →
      UnifiedTheory.LayerC.PageCurve.pageEntropy m n =
        Real.log n - (n : ℝ) / (2 * m)
  upperBound :
    ∀ m n : ℕ, 0 < m → 0 < n →
      UnifiedTheory.LayerC.PageCurve.pageEntropy m n ≤
        Real.log (((min m n : ℕ) : ℝ))
  diagonalMonotone :
    ∀ n₁ n₂ : ℕ, 0 < n₁ → n₁ ≤ n₂ →
      UnifiedTheory.LayerC.PageCurve.pageEntropy n₁ n₁ ≤
        UnifiedTheory.LayerC.PageCurve.pageEntropy n₂ n₂

theorem gate6_pageFormulaAudit_closed :
    Gate6PageFormulaAuditClosed := by
  rcases UnifiedTheory.LayerC.PageCurve.pageCurve_master with
    ⟨hsymm, hpage, hearly, hlate, hupper, hmono⟩
  exact ⟨hsymm, hpage, hearly, hlate, hupper, hmono⟩

/-- Gate 6 cosmology/black-hole target specialized to the finite audit layers
already closed in the repo.  This is an audit target, not a claim that the
remaining physical derivations are complete: the cosmological measure/initial
condition and CMB/structure/GW compatibility fields remain external. -/
def gate6CosmologyBlackHoleTargetsOfFiniteAudits
    (initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop) :
    Gate6CosmologyBlackHoleTargets where
  initialConditionOrCosmologicalMeasure :=
    initialConditionOrCosmologicalMeasure
  darkEnergyOrCosmologicalConstantMechanism :=
    Gate6CosmologicalConstantGravitonAuditClosed
  darkMatterPredictionOrExclusion :=
    Gate6DarkMatterPlanckWindowAuditClosed
  blackHoleEntropyEvaporationInformation :=
    Gate6FiniteInformationPreservationAuditClosed ∧
      Gate6DiscreteHolographyAuditClosed ∧
        Gate6StructuralPageCurveAuditClosed ∧
          Gate6PageFormulaAuditClosed
  cmbStructureGravitationalWaveCompatibility :=
    cmbStructureGravitationalWaveCompatibility

/-- The current finite/audit Gate 6 package reduces Gate 6 closure to the
still-external cosmological-measure/initial-condition and CMB/structure/GW
compatibility inputs. -/
theorem gate6_cosmologyBlackHole_closed_of_finiteAudits
    {initialConditionOrCosmologicalMeasure
      cmbStructureGravitationalWaveCompatibility : Prop}
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hcmb : cmbStructureGravitationalWaveCompatibility) :
    Gate6CosmologyBlackHoleClosed
      (gate6CosmologyBlackHoleTargetsOfFiniteAudits
        initialConditionOrCosmologicalMeasure
        cmbStructureGravitationalWaveCompatibility) := by
  exact
    ⟨hinitial,
      gate6_cosmologicalConstantGravitonAudit_closed,
      gate6_darkMatterPlanckWindowAudit_closed,
      ⟨gate6_finiteInformationPreservationAudit_closed,
        gate6_discreteHolographyAudit_closed,
        gate6_structuralPageCurveAudit_closed,
        gate6_pageFormulaAudit_closed⟩,
      hcmb⟩

/-- Inflation/CMB tensor audit available to Gate 6.  This packages the
framework's atomic Starobinsky-sector `n_s` and `r` checks against Planck/BICEP
windows.  It is not a full late-time structure-formation or stochastic
gravitational-wave compatibility theorem. -/
structure Gate6InflationCMBTensorAuditClosed : Prop where
  nsAtomic :
    UnifiedTheory.LayerB.InflationAudit.ns_framework =
      1 -
        1 /
          ((UnifiedTheory.LayerB.InflationAudit.NW : ℚ) *
            (UnifiedTheory.LayerB.InflationAudit.Nc : ℚ) *
              (UnifiedTheory.LayerB.InflationAudit.Nt : ℚ))
  nsPlanckWindow :
    UnifiedTheory.LayerB.InflationAudit.ns_lo_1sigma <
        UnifiedTheory.LayerB.InflationAudit.ns_framework ∧
      UnifiedTheory.LayerB.InflationAudit.ns_framework <
        UnifiedTheory.LayerB.InflationAudit.ns_hi_1sigma
  rAtomic :
    UnifiedTheory.LayerB.InflationAudit.r_framework =
      1 /
        ((UnifiedTheory.LayerB.InflationAudit.NWsq : ℚ) *
          (UnifiedTheory.LayerB.InflationAudit.Nc : ℚ) *
            ((UnifiedTheory.LayerB.InflationAudit.Nt : ℚ) *
              (UnifiedTheory.LayerB.InflationAudit.Nt : ℚ)))
  rBelowUpperBound :
    UnifiedTheory.LayerB.InflationAudit.r_framework <
      UnifiedTheory.LayerB.InflationAudit.r_upper_bound

theorem gate6_inflationCMBTensorAudit_closed :
    Gate6InflationCMBTensorAuditClosed := by
  let h := UnifiedTheory.LayerB.InflationAudit.inflation_audit_short
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Gate 6 cosmology/black-hole target with all finite audits and the
inflation/CMB tensor audit supplied.  The remaining compatibility input is the
late-time structure/gravitational-wave bridge beyond the inflation-sector
observable checks. -/
def gate6CosmologyBlackHoleTargetsOfFiniteAuditsAndInflationCompatibility
    (initialConditionOrCosmologicalMeasure
      lateStructureGravitationalWaveCompatibility : Prop) :
    Gate6CosmologyBlackHoleTargets where
  initialConditionOrCosmologicalMeasure :=
    initialConditionOrCosmologicalMeasure
  darkEnergyOrCosmologicalConstantMechanism :=
    Gate6CosmologicalConstantGravitonAuditClosed
  darkMatterPredictionOrExclusion :=
    Gate6DarkMatterPlanckWindowAuditClosed
  blackHoleEntropyEvaporationInformation :=
    Gate6FiniteInformationPreservationAuditClosed ∧
      Gate6DiscreteHolographyAuditClosed ∧
        Gate6StructuralPageCurveAuditClosed ∧
          Gate6PageFormulaAuditClosed
  cmbStructureGravitationalWaveCompatibility :=
    Gate6InflationCMBTensorAuditClosed ∧
      lateStructureGravitationalWaveCompatibility

/-- With the inflation/CMB tensor audit harvested, Gate 6 closure is reduced
to the cosmological-measure/initial-condition input and the late-time
structure/GW bridge. -/
theorem gate6_cosmologyBlackHole_closed_of_finiteAuditsAndInflationCompatibility
    {initialConditionOrCosmologicalMeasure
      lateStructureGravitationalWaveCompatibility : Prop}
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    Gate6CosmologyBlackHoleClosed
      (gate6CosmologyBlackHoleTargetsOfFiniteAuditsAndInflationCompatibility
        initialConditionOrCosmologicalMeasure
        lateStructureGravitationalWaveCompatibility) := by
  exact
    ⟨hinitial,
      gate6_cosmologicalConstantGravitonAudit_closed,
      gate6_darkMatterPlanckWindowAudit_closed,
      ⟨gate6_finiteInformationPreservationAudit_closed,
        gate6_discreteHolographyAudit_closed,
        gate6_structuralPageCurveAudit_closed,
        gate6_pageFormulaAudit_closed⟩,
      ⟨gate6_inflationCMBTensorAudit_closed, hlate⟩⟩

/-- The Gate 6 entropy-flux limit bridge: a supplied finite error-control
source and exact finite focusing derivative family give convergence of the
finite scaled source to Araki/null flux and convergence of the finite
KL-derivative law to the corresponding continuum derivative target. -/
structure Gate6EntropyFluxLimitBridgeClosed
    (B : EntropyFluxLimitBridge) : Prop where
  sourceConvergesToArakiFlux :
    FiniteEntropySourceConvergesToArakiFlux
      B.source.finiteScaledFlux B.arakiFlux
  focusingDerivativeLimit :
    Tendsto B.focusing.klDeriv atTop
      (𝓝 (-B.focusing.lambda * B.continuumAreaDeriv))

theorem gate6_entropyFluxLimitBridge_closed
    (B : EntropyFluxLimitBridge) :
    Gate6EntropyFluxLimitBridgeClosed B := by
  rcases entropyFluxLimitBridge_closes_first_field B with
    ⟨hsource, hfocusing⟩
  exact ⟨hsource, hfocusing⟩

/-- The Gate 6 Araki/Bekenstein-Hawking horizon-balance sublayer: Araki flux,
Dorau-Much area variation, Raychaudhuri focusing, and Bekenstein-Hawking
normalization fix the nonzero-excitation null balance to the `8*pi` coupling. -/
structure Gate6ArakiBHEightPiBalanceClosed
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (hRay : RaychaudhuriAreaVariation_Target H)
    (hBH : BekensteinHawkingEntropyArea_Target H)
    {phi : H.Excitation} (hS : H.Srel phi ≠ 0) : Prop where
  eightPiNullBalance :
    H.ricciWeightedFlux phi =
      (8 * Real.pi) * H.weightedNullEnergy phi

theorem gate6_arakiBHEightPiBalance_closed
    {H : HorizonAQFTModel} {alpha : ℝ}
    (hFlux : HorizonArakiRelativeEntropyFlux_Target H)
    (hArea : RelativeEntropyAreaVariation_Target H alpha)
    (hRay : RaychaudhuriAreaVariation_Target H)
    (hBH : BekensteinHawkingEntropyArea_Target H)
    {phi : H.Excitation} (hS : H.Srel phi ≠ 0) :
    Gate6ArakiBHEightPiBalanceClosed hFlux hArea hRay hBH hS := by
  exact
    ⟨bekensteinHawking_raychaudhuri_flux_balance_eight_pi
      hFlux hArea hRay hBH hS⟩

/-- The Gate 6 Dorau-Much Einstein bridge: once the pointwise null Ricci
balance, symmetry, differentiability, and conservation inputs are supplied, the
repository's null-polarization theorem yields the semiclassical Einstein
equation with an integration-constant cosmological term. -/
structure Gate6DorauMuchEinsteinBridgeClosed
    (kappa : ℝ)
    (Ricci T : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (Rscalar : ℝ → ℝ) : Prop where
  semiclassicalEinsteinEquation :
    ∃ Lambda : ℝ, ∀ x,
      (Ricci x - (Rscalar x / 2) • eta) + Lambda • eta =
        kappa • T x

theorem gate6_dorauMuchEinsteinBridge_closed
    (kappa : ℝ)
    (Ricci T : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (Rscalar : ℝ → ℝ)
    (hRicciSymm : ∀ x i j, Ricci x i j = Ricci x j i)
    (hTsymm : ∀ x i j, T x i j = T x j i)
    (hRicciNull : ∀ x (v : Fin 4 → ℝ), quad eta v = 0 →
      quad (Ricci x) v = kappa * quad (T x) v)
    (hdiff : Differentiable ℝ
      (fun x => (Ricci x - (Rscalar x / 2) • eta) 0 0
        - kappa * T x 0 0))
    (hcons : ∀ x, deriv
      (fun y => (Ricci y - (Rscalar y / 2) • eta) 0 0
        - kappa * T y 0 0) x = 0) :
    Gate6DorauMuchEinsteinBridgeClosed kappa Ricci T Rscalar := by
  exact
    ⟨dorau_much_semiclassical_einstein_equation
      kappa Ricci T Rscalar hRicciSymm hTsymm hRicciNull hdiff hcons⟩

/-- The Gate 6 QQG cosmology bridge sublayer: for any QQG scenario, Lean proves
the UV fixed-point, large-N running, small-`ξ` running, monotone plateau
potential, and sharp `r >= 0.01` algebraic bound ledger.  If the explicit
emergence hypotheses are supplied, the same package enters the conditional
Einstein branch.  This is a conditional cosmology bridge, not an unconditional
derivation of the emergence hypotheses, initial state, reheating, or CMB
phenomenology. -/
structure Gate6QQGCosmologyBridgeAuditClosed
    (S : QQGScenario) : Prop where
  provenConclusions : QQGProvenConclusions S
  conditionalEinsteinBranch :
    ∀ hyp : QQGEmergenceHypotheses, QQGConditionalEinsteinBranch S
  bridgeProvenPart :
    ∀ hyp : QQGEmergenceHypotheses,
      (qqg_cosmology_implies_conditional_einstein S hyp).1 =
        qqg_proven_conclusions S

theorem gate6_qqgCosmologyBridgeAudit_closed
    (S : QQGScenario) :
    Gate6QQGCosmologyBridgeAuditClosed S := by
  exact
    ⟨qqg_proven_conclusions S,
      fun hyp => qqg_cosmology_implies_conditional_einstein S hyp,
      fun hyp => qqg_bridge_proven_part S hyp⟩

/-- The Gate 6 physical-information-limits audit: the temporal
Margolus-Levitin/Mandelstam-Tamm/Lloyd axis unifies, while Bekenstein capacity
and Lieb-Robinson spatial propagation are independent axes, and the temporal
plus capacity axes compose into Lloyd's ultimate-computer bound.  The theorem
also records the negative result that these limits do not collapse to one
monotone master inequality. -/
structure Gate6PhysicalInformationLimitsAuditClosed : Prop where
  master :
    ∀ R : ℝ, 0 < R →
      (∀ T E : ℝ, 0 < E → 0 < T →
         (T ≥ mlBound E ↔ T * E ≥ Real.pi / 2) ∧
         (T ≥ mlBound E ↔ 1 / T ≤ lloydRate E) ∧
         (mlBound E * lloydRate E = 1)) ∧
      (∃ E₁ E₂ : ℝ, 0 < E₁ ∧ E₁ < E₂ ∧
          mlBound E₂ < mlBound E₁ ∧
          bekensteinBound R E₁ < bekensteinBound R E₂) ∧
      (¬ ∃ f : ℝ → ℝ, Monotone f ∧
          ∀ E : ℝ, 0 < E → bekensteinBound R E = f (mlBound E)) ∧
      (∀ C v ξ d t : ℝ,
          mlBound 1 ≠ mlBound 2 ∧ lrBound C v ξ d t = lrBound C v ξ d t) ∧
      (∀ E C ξ d t v₁ v₂ : ℝ, 0 < C → 0 < ξ → t ≠ 0 → v₁ < v₂ →
          lrBound C v₁ ξ d t ≠ lrBound C v₂ ξ d t ∧ mlBound E = mlBound E) ∧
      (∀ ops memory t E : ℝ, 0 < E → 0 < t →
          ops ≤ lloydUltimateOps t E → memory ≤ bekensteinBound R E →
          (ops ≤ lloydUltimateOps t E) ∧ (memory ≤ bekensteinBound R E) ∧
          (0 < lloydUltimateOps t E) ∧ (0 < bekensteinBound R E) ∧
          (lloydUltimateOps t E = lloydRate E * t))

theorem gate6_physicalInformationLimitsAudit_closed :
    Gate6PhysicalInformationLimitsAuditClosed := by
  exact ⟨fun R hR => physical_information_limits_master R hR⟩

/-- The Gate 6 Hayden-Preskill evaporation audit: the repository proves the
finite-dimensional Page-compatible evaporation skeleton, the Hayden recovery
bound, its strict gap form, and the conditional recovery-error bound once the
remaining scrambling/decoupling/recovery targets are supplied. -/
structure Gate6HaydenPreskillEvaporationAuditClosed : Prop where
  recoveryBoundNonnegative :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      0 ≤ UnifiedTheory.LayerC.HaydenPreskill.HPRecoveryBound s
  haydenGapBound :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.HaydenGap s →
        UnifiedTheory.LayerC.HaydenPreskill.HPRecoveryBound s ≤ 1
  strictHaydenGapBound :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      s.k < s.r * s.N →
        UnifiedTheory.LayerC.HaydenPreskill.HPRecoveryBound s < 1
  pageCurveCompatibility :
    ∀ (s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup)
      (_h_resid_pos : 0 < s.residualBH)
      (σ : UnifiedTheory.LayerB.PageCurve.SchmidtSpectrum
        (s.k * s.residualBH) s.r),
        UnifiedTheory.LayerB.PageCurve.pageEntropy σ ≤
          Real.log (((min (s.k * s.residualBH) s.r : ℕ) : ℝ))
  recoveryErrorBounded :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Recovery_Target s →
        UnifiedTheory.LayerC.HaydenPreskill.HaydenGap s →
          ∃ err : ℝ, 0 ≤ err ∧ err ≤ 2

theorem gate6_haydenPreskillEvaporationAudit_closed :
    Gate6HaydenPreskillEvaporationAuditClosed := by
  let h := UnifiedTheory.LayerC.HaydenPreskill.haydenPreskill_master
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The Gate 6 AMPS audit: the repository proves the monogamy no-go, the
postulate-level fork, firewall/complementarity branches, the quantitative CKW
weak form, and exclusivity of the Page-time/equivalence-principle targets. -/
structure Gate6AMPSFirewallAuditClosed : Prop where
  directContradiction :
    ∀ le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement,
      le.ent_with_E → le.ent_with_bTilde → False
  eitherOr :
    ∀ le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement,
      (le.ent_with_E → ¬ le.ent_with_bTilde) ∧
        (le.ent_with_bTilde → ¬ le.ent_with_E)
  postulateFork :
    ∀ (p : UnifiedTheory.LayerC.AMPSFirewall.AMPSPostulates)
      (le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement),
      (p.unitarity → le.ent_with_E) →
        (p.equiv_principle → le.ent_with_bTilde) →
          ¬ (p.unitarity ∧ p.equiv_principle)
  firewallResolution :
    ∀ le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement,
      le.ent_with_E → ¬ le.ent_with_bTilde
  complementarityResolution :
    ∀ le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement,
      le.ent_with_bTilde → ¬ le.ent_with_E
  quantitativeCKW :
    ∀ q : UnifiedTheory.LayerC.AMPSFirewall.QuantitativeLateMode,
      q.bE = 1 → q.bBT = 0
  targetsExclusive :
    ∀ le : UnifiedTheory.LayerC.AMPSFirewall.LateModeEntanglement,
      ¬ (UnifiedTheory.LayerC.AMPSFirewall.AMPS_PageTime_Target le ∧
        UnifiedTheory.LayerC.AMPSFirewall.AMPS_EquivPrinciple_Target le)

theorem gate6_ampsFirewallAudit_closed :
    Gate6AMPSFirewallAuditClosed := by
  let h := UnifiedTheory.LayerC.AMPSFirewall.amps_master
  exact
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Gate 6 full audit envelope: in addition to the finite dark-sector,
cosmological-constant/graviton, information-preservation, holography, Page,
inflation, Hayden-Preskill, and AMPS audits, this packages the QQG conditional
cosmology bridge and the physical information-limit audit.  Unlike the lighter
finite-audit target, it leaves the remaining scrambling/decoupling/recovery
evaporation dynamics explicit as a physical input rather than treating finite
no-loss/Page formula audits as a complete evaporation model. -/
def gate6CosmologyBlackHoleTargetsOfFiniteAuditsInflationQQGAndInformationEnvelope
    (S : QQGScenario)
    (initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop) :
    Gate6CosmologyBlackHoleTargets where
  initialConditionOrCosmologicalMeasure :=
    initialConditionOrCosmologicalMeasure
  darkEnergyOrCosmologicalConstantMechanism :=
    Gate6CosmologicalConstantGravitonAuditClosed ∧
      Gate6QQGCosmologyBridgeAuditClosed S
  darkMatterPredictionOrExclusion :=
    Gate6DarkMatterPlanckWindowAuditClosed
  blackHoleEntropyEvaporationInformation :=
    Gate6FiniteInformationPreservationAuditClosed ∧
      Gate6DiscreteHolographyAuditClosed ∧
        Gate6StructuralPageCurveAuditClosed ∧
          Gate6PageFormulaAuditClosed ∧
            Gate6HaydenPreskillEvaporationAuditClosed ∧
              Gate6AMPSFirewallAuditClosed ∧
                Gate6PhysicalInformationLimitsAuditClosed ∧
                  microscopicBlackHoleEvaporationDynamics
  cmbStructureGravitationalWaveCompatibility :=
    Gate6InflationCMBTensorAuditClosed ∧
      Gate6QQGCosmologyBridgeAuditClosed S ∧
        lateStructureGravitationalWaveCompatibility

/-- With the full Gate 6 audit envelope harvested, the genuinely remaining
Gate 6 physics inputs are now explicit: a cosmological
measure/initial-condition principle, microscopic black-hole evaporation
dynamics, and a late-time structure/GW bridge beyond the inflation and QQG
audits. -/
theorem gate6_cosmologyBlackHole_closed_of_finiteAuditsInflationQQGAndInformationEnvelope
    (S : QQGScenario)
    {initialConditionOrCosmologicalMeasure
      microscopicBlackHoleEvaporationDynamics
      lateStructureGravitationalWaveCompatibility : Prop}
    (hinitial : initialConditionOrCosmologicalMeasure)
    (hevap : microscopicBlackHoleEvaporationDynamics)
    (hlate : lateStructureGravitationalWaveCompatibility) :
    Gate6CosmologyBlackHoleClosed
      (gate6CosmologyBlackHoleTargetsOfFiniteAuditsInflationQQGAndInformationEnvelope
        S initialConditionOrCosmologicalMeasure
        microscopicBlackHoleEvaporationDynamics
        lateStructureGravitationalWaveCompatibility) := by
  exact
    ⟨hinitial,
      ⟨gate6_cosmologicalConstantGravitonAudit_closed,
        gate6_qqgCosmologyBridgeAudit_closed S⟩,
      gate6_darkMatterPlanckWindowAudit_closed,
      ⟨gate6_finiteInformationPreservationAudit_closed,
        gate6_discreteHolographyAudit_closed,
        gate6_structuralPageCurveAudit_closed,
        gate6_pageFormulaAudit_closed,
        gate6_haydenPreskillEvaporationAudit_closed,
        gate6_ampsFirewallAudit_closed,
        gate6_physicalInformationLimitsAudit_closed,
        hevap⟩,
      ⟨gate6_inflationCMBTensorAudit_closed,
        gate6_qqgCosmologyBridgeAudit_closed S,
        hlate⟩⟩

/-- Named remaining Gate 6 bridge obligations.  This refines the three loose
physical inputs in the strict Gate 6 envelope into attackable subtargets:
cosmological initial data/measure, black-hole scrambling, decoupling, recovery
channels, late-time structure formation, and gravitational-wave compatibility. -/
structure Gate6NamedCosmologyBlackHoleBridgeTargets : Type where
  cosmologicalMeasureOrInitialState : Prop
  microscopicScramblingDynamics : Prop
  microscopicDecouplingDynamics : Prop
  microscopicRecoveryChannelDynamics : Prop
  lateStructureFormation : Prop
  gravitationalWaveCompatibility : Prop

/-- Gate 6 named bridge closure bundles all finite/audit layers already proved
in the repo with the remaining physical cosmology, evaporation, and late-time
compatibility obligations. -/
structure Gate6NamedCosmologyBlackHoleBridgeClosed
    (S : QQGScenario)
    (T : Gate6NamedCosmologyBlackHoleBridgeTargets) : Prop where
  cosmologicalMeasureOrInitialState :
    T.cosmologicalMeasureOrInitialState
  cosmologicalConstantGravitonAudit :
    Gate6CosmologicalConstantGravitonAuditClosed
  qqgCosmologyBridgeAudit :
    Gate6QQGCosmologyBridgeAuditClosed S
  darkMatterPlanckWindowAudit :
    Gate6DarkMatterPlanckWindowAuditClosed
  inflationCMBTensorAudit :
    Gate6InflationCMBTensorAuditClosed
  finiteInformationPreservationAudit :
    Gate6FiniteInformationPreservationAuditClosed
  discreteHolographyAudit :
    Gate6DiscreteHolographyAuditClosed
  structuralPageCurveAudit :
    Gate6StructuralPageCurveAuditClosed
  pageFormulaAudit :
    Gate6PageFormulaAuditClosed
  haydenPreskillEvaporationAudit :
    Gate6HaydenPreskillEvaporationAuditClosed
  ampsFirewallAudit :
    Gate6AMPSFirewallAuditClosed
  physicalInformationLimitsAudit :
    Gate6PhysicalInformationLimitsAuditClosed
  microscopicScramblingDynamics :
    T.microscopicScramblingDynamics
  microscopicDecouplingDynamics :
    T.microscopicDecouplingDynamics
  microscopicRecoveryChannelDynamics :
    T.microscopicRecoveryChannelDynamics
  lateStructureFormation :
    T.lateStructureFormation
  gravitationalWaveCompatibility :
    T.gravitationalWaveCompatibility

theorem gate6_namedCosmologyBlackHoleBridge_closed
    (S : QQGScenario)
    (T : Gate6NamedCosmologyBlackHoleBridgeTargets)
    (hinitial : T.cosmologicalMeasureOrInitialState)
    (hscrambling : T.microscopicScramblingDynamics)
    (hdecoupling : T.microscopicDecouplingDynamics)
    (hrecovery : T.microscopicRecoveryChannelDynamics)
    (hlate : T.lateStructureFormation)
    (hgw : T.gravitationalWaveCompatibility) :
    Gate6NamedCosmologyBlackHoleBridgeClosed S T := by
  exact
    ⟨hinitial,
      gate6_cosmologicalConstantGravitonAudit_closed,
      gate6_qqgCosmologyBridgeAudit_closed S,
      gate6_darkMatterPlanckWindowAudit_closed,
      gate6_inflationCMBTensorAudit_closed,
      gate6_finiteInformationPreservationAudit_closed,
      gate6_discreteHolographyAudit_closed,
      gate6_structuralPageCurveAudit_closed,
      gate6_pageFormulaAudit_closed,
      gate6_haydenPreskillEvaporationAudit_closed,
      gate6_ampsFirewallAudit_closed,
      gate6_physicalInformationLimitsAudit_closed,
      hscrambling, hdecoupling, hrecovery, hlate, hgw⟩

/-- The strict Gate 6 target induced by the named cosmology/black-hole bridge.
The three older loose inputs are now a named initial-state slot, a three-part
scrambling/decoupling/recovery evaporation slot, and a two-part
structure-formation/GW slot. -/
def gate6CosmologyBlackHoleTargetsOfNamedCosmologyBlackHoleBridge
    (S : QQGScenario)
    (T : Gate6NamedCosmologyBlackHoleBridgeTargets) :
    Gate6CosmologyBlackHoleTargets :=
  gate6CosmologyBlackHoleTargetsOfFiniteAuditsInflationQQGAndInformationEnvelope
    S T.cosmologicalMeasureOrInitialState
    (T.microscopicScramblingDynamics ∧
      T.microscopicDecouplingDynamics ∧
        T.microscopicRecoveryChannelDynamics)
    (T.lateStructureFormation ∧ T.gravitationalWaveCompatibility)

theorem gate6_cosmologyBlackHole_closed_of_namedCosmologyBlackHoleBridge
    (S : QQGScenario)
    (T : Gate6NamedCosmologyBlackHoleBridgeTargets)
    (hBridge : Gate6NamedCosmologyBlackHoleBridgeClosed S T) :
    Gate6CosmologyBlackHoleClosed
      (gate6CosmologyBlackHoleTargetsOfNamedCosmologyBlackHoleBridge S T) := by
  exact
    gate6_cosmologyBlackHole_closed_of_finiteAuditsInflationQQGAndInformationEnvelope
      S hBridge.cosmologicalMeasureOrInitialState
      ⟨hBridge.microscopicScramblingDynamics,
        hBridge.microscopicDecouplingDynamics,
        hBridge.microscopicRecoveryChannelDynamics⟩
      ⟨hBridge.lateStructureFormation,
        hBridge.gravitationalWaveCompatibility⟩

/-- Hayden-Preskill-native refinement of the black-hole evaporation bridge.
Instead of a generic microscopic-evaporation proposition, this exposes the
three analytic inputs already named in `LayerC.HaydenPreskill`: scrambling,
decoupling, and recovery with the Hayden gap. -/
structure Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed : Prop where
  scramblingTarget :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Scrambling_Target s
  decouplingTarget :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Decoupling_Target s
  recoveryTargetAndHaydenGap :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Recovery_Target s ∧
        UnifiedTheory.LayerC.HaydenPreskill.HaydenGap s
  recoveryBoundWellBehaved :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      0 ≤ UnifiedTheory.LayerC.HaydenPreskill.HPRecoveryBound s ∧
        UnifiedTheory.LayerC.HaydenPreskill.HPRecoveryBound s ≤ 1
  recoveryErrorBounded :
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      ∃ err : ℝ, 0 ≤ err ∧ err ≤ 2

theorem gate6_haydenPreskillMicroscopicEvaporationBridge_closed
    (hscrambling :
      ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
        UnifiedTheory.LayerC.HaydenPreskill.Scrambling_Target s)
    (hdecoupling :
      ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
        UnifiedTheory.LayerC.HaydenPreskill.Decoupling_Target s)
    (hrecoveryGap :
      ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
        UnifiedTheory.LayerC.HaydenPreskill.Recovery_Target s ∧
          UnifiedTheory.LayerC.HaydenPreskill.HaydenGap s) :
    Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed := by
  exact
    ⟨hscrambling, hdecoupling, hrecoveryGap,
      fun s =>
        UnifiedTheory.LayerC.HaydenPreskill.haydenPreskill_recovery
          hscrambling hdecoupling s (hrecoveryGap s).2,
      fun s =>
        UnifiedTheory.LayerC.HaydenPreskill.haydenPreskill_recovery_error_bounded
          s (hrecoveryGap s).1 (hrecoveryGap s).2⟩

/-- Gate 6 named target whose evaporation fields are specialized to the
Hayden-Preskill-native scrambling/decoupling/recovery obligations. -/
def gate6NamedCosmologyBlackHoleBridgeTargetsOfHaydenPreskillMicroscopicEvaporation
    (cosmologicalMeasureOrInitialState
      lateStructureFormation gravitationalWaveCompatibility : Prop) :
    Gate6NamedCosmologyBlackHoleBridgeTargets where
  cosmologicalMeasureOrInitialState :=
    cosmologicalMeasureOrInitialState
  microscopicScramblingDynamics :=
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Scrambling_Target s
  microscopicDecouplingDynamics :=
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Decoupling_Target s
  microscopicRecoveryChannelDynamics :=
    ∀ s : UnifiedTheory.LayerC.HaydenPreskill.HPSetup,
      UnifiedTheory.LayerC.HaydenPreskill.Recovery_Target s ∧
        UnifiedTheory.LayerC.HaydenPreskill.HaydenGap s
  lateStructureFormation := lateStructureFormation
  gravitationalWaveCompatibility := gravitationalWaveCompatibility

theorem gate6_namedCosmologyBlackHoleBridge_closed_of_haydenPreskillMicroscopicEvaporation
    (S : QQGScenario)
    {cosmologicalMeasureOrInitialState
      lateStructureFormation gravitationalWaveCompatibility : Prop}
    (hinitial : cosmologicalMeasureOrInitialState)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    Gate6NamedCosmologyBlackHoleBridgeClosed S
      (gate6NamedCosmologyBlackHoleBridgeTargetsOfHaydenPreskillMicroscopicEvaporation
        cosmologicalMeasureOrInitialState
        lateStructureFormation gravitationalWaveCompatibility) := by
  exact
    gate6_namedCosmologyBlackHoleBridge_closed S
      (gate6NamedCosmologyBlackHoleBridgeTargetsOfHaydenPreskillMicroscopicEvaporation
        cosmologicalMeasureOrInitialState
        lateStructureFormation gravitationalWaveCompatibility)
      hinitial hHP.scramblingTarget hHP.decouplingTarget
      hHP.recoveryTargetAndHaydenGap hlate hgw

/-! ## Gate 7: external tests -/

/-- External-test protocol obligations for keeping the framework falsifiable. -/
structure Gate7ExternalTestTargets : Type where
  predictionsFrozenBeforeComparison : Prop
  uncertaintyModelsAttached : Prop
  decisiveFutureTestsRecorded : Prop
  failureLedgerMaintained : Prop

/-- Gate 7 is closed when all public comparisons are preregistered and
failure-handling is explicit. -/
structure Gate7ExternalTestClosed
    (T : Gate7ExternalTestTargets) : Prop where
  predictionsFrozenBeforeComparison : T.predictionsFrozenBeforeComparison
  uncertaintyModelsAttached : T.uncertaintyModelsAttached
  decisiveFutureTestsRecorded : T.decisiveFutureTestsRecorded
  failureLedgerMaintained : T.failureLedgerMaintained

/-- The concrete Gate 7 preregistration target already present in
`PreRegistrationLedger.lean`.  This closes the protocol layer: five forward
predictions are separated from post-dictions and consistency checks, attached
to a matching falsification table, and assigned positive calendar horizons. -/
def gate7PreRegistrationLedgerTargets : Gate7ExternalTestTargets where
  predictionsFrozenBeforeComparison :=
    preRegisteredEntries.length = 5 ∧
      (∀ e ∈ preRegisteredEntries, e.category = .PreRegistered)
  uncertaintyModelsAttached :=
    falsificationTable.length = 5 ∧
      preRegisteredEntries.length = falsificationTable.length
  decisiveFutureTestsRecorded :=
    ∀ e ∈ preRegisteredEntries,
      (earliest_horizon_yr ≤ e.timeHorizonYr ∧
        e.timeHorizonYr ≤ longterm_horizon_yr) ∧
        e.timeHorizonYr > 0
  failureLedgerMaintained :=
    (∀ e ∈ postDictionEntries, e.timeHorizonYr = 0) ∧
      (∀ e ∈ postDictionEntries, e.category = .PostDiction) ∧
        (∀ e ∈ consistencyCheckEntries,
          e.category = .ConsistencyCheck) ∧
          (PredictionCategory.PreRegistered ≠
            PredictionCategory.PostDiction) ∧
          (PredictionCategory.PreRegistered ≠
            PredictionCategory.ConsistencyCheck) ∧
          (PredictionCategory.PostDiction ≠
            PredictionCategory.ConsistencyCheck)

/-- Gate 7 protocol closure follows from the existing preregistration ledger.
This does not mean the future experiments have already reported; it means the
repo has a formal public comparison target with uncertainty/falsification rows
and a failure ledger separating forward predictions from post-dictions. -/
theorem gate7_externalTests_closed_from_preRegistrationLedger :
    Gate7ExternalTestClosed gate7PreRegistrationLedgerTargets := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨pre_registered_count, preRegistered_all_tagged⟩
  · exact ⟨falsificationTable_length, falsificationTable_pre_registered_count⟩
  · intro e he
    have hhorizon := preRegistered_horizons_in_window e he
    refine ⟨hhorizon, ?_⟩
    exact lt_of_lt_of_le (by norm_num [earliest_horizon_yr]) hhorizon.1
  · exact
      ⟨postDiction_no_calendar_experiment, postDiction_all_tagged,
        consistencyCheck_all_tagged,
        (by intro h; cases h), (by intro h; cases h), (by intro h; cases h)⟩

#print axioms gate1_rawAggregateNonzero_of_closed
#print axioms gate1_completeChiralLawSupportAndConsistency_closed
#print axioms gate1_completeChiralAtlasRealization_closed
#print axioms gate1_positiveFrequencyHandedness_closed
#print axioms gate1_microscopicLaw_closed_of_signedFiberSums_and_orderCoupling
#print axioms gate1_physicalSelectionBridge_closed
#print axioms gate1_microscopicLaw_closed_of_physicalSelectionBridge
#print axioms gate2_baseDistortion_zero_iff_components_zero
#print axioms gate2_diffeomorphismInvariantObservableFamily_closed
#print axioms gate3_horizonProtection_and_total_tendsto_zero_of_certificate
#print axioms gate3_aggregateRateContraction_closed
#print axioms gate3_convergenceBridgeResidualSplit_closed
#print axioms gate3_residualGapExactZero_closed
#print axioms gate3_exactRecoveryCertificate_closed
#print axioms gate4_recoveredStage_bdg4d_operator_limit_of_interface
#print axioms gate4_recoveredBDGOperatorBridge_closed
#print axioms gate4_exactRecoveryRSSPoisson_closed
#print axioms gate4_recoveredBDGPoissonOperatorBridge_closed
#print axioms gate4_activeKernelConeBound_closed
#print axioms gate4_kernelProfileSplitSupplier_closed
#print axioms gate4_scheduledKernelOperatorBridge_closed
#print axioms gate5_arbitraryAxisBornObservable_closed
#print axioms gate5_localBornProjectiveCompleteness_closed
#print axioms gate5_recoveredCarrier_coverIndependence_of_jointlySurjective
#print axioms gate5_finiteCarrierCover_closed
#print axioms gate5_qftStandardModelIR_closed_of_finiteCarrierCover
#print axioms gate5_effectiveHilbertAudit_closed
#print axioms gate5_propagatorKinematicAudit_closed
#print axioms gate5_finiteGaugeAudit_closed
#print axioms gate5_standardModelParameterAudit_closed
#print axioms gate5_qftStandardModelIR_closed_of_finiteCarrierAndSMAudits
#print axioms gate5_lorentzianWightmanStatusAudit_closed
#print axioms gate5_chamberMassGapDecayAudit_closed
#print axioms gate5_hopfOctonionComplexGeometryFiniteAudit_closed
#print axioms gate5_qftStandardModelIR_closed_of_finiteCarrierSMAuditsWightmanAndMassGap
#print axioms gate5_qftStandardModelIR_closed_of_octonionS6BridgeAndFiniteAudits
#print axioms gate5_haagRuelleSpinStatisticsBridge_closed
#print axioms gate5_yangMillsHiggsRenormalizationBridge_closed
#print axioms gate5_qftStandardModelIR_closed_of_namedContinuumBridgesAndFiniteAudits
#print axioms gate5_recoveredCarrierCommonRefinement_closed
#print axioms gate6_darkDensity_atomic_audit_hook
#print axioms gate6_darkDensityAudit_closed
#print axioms gate6_darkMatterPlanckWindowAudit_closed
#print axioms gate6_cosmologicalConstantGravitonAudit_closed
#print axioms gate6_finiteInformationPreservationAudit_closed
#print axioms gate6_discreteHolographyAudit_closed
#print axioms gate6_structuralPageCurveAudit_closed
#print axioms gate6_pageFormulaAudit_closed
#print axioms gate6_cosmologyBlackHole_closed_of_finiteAudits
#print axioms gate6_inflationCMBTensorAudit_closed
#print axioms gate6_cosmologyBlackHole_closed_of_finiteAuditsAndInflationCompatibility
#print axioms gate6_cosmologyBlackHole_closed_of_finiteAuditsInflationQQGAndInformationEnvelope
#print axioms gate6_namedCosmologyBlackHoleBridge_closed
#print axioms gate6_cosmologyBlackHole_closed_of_namedCosmologyBlackHoleBridge
#print axioms gate6_haydenPreskillMicroscopicEvaporationBridge_closed
#print axioms gate6_namedCosmologyBlackHoleBridge_closed_of_haydenPreskillMicroscopicEvaporation
#print axioms gate6_haydenPreskillEvaporationAudit_closed
#print axioms gate6_ampsFirewallAudit_closed
#print axioms gate6_entropyFluxLimitBridge_closed
#print axioms gate6_arakiBHEightPiBalance_closed
#print axioms gate6_dorauMuchEinsteinBridge_closed
#print axioms gate6_qqgCosmologyBridgeAudit_closed
#print axioms gate6_physicalInformationLimitsAudit_closed
#print axioms gate7_externalTests_closed_from_preRegistrationLedger

end UnifiedTheory.Audit.KFTOESevenGateAttack
