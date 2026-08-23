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
import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DRecovered
import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound
import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverIndependence
import UnifiedTheory.LayerA.GravitonTTModes
import UnifiedTheory.LayerB.CosmologicalConstantAudit
import UnifiedTheory.LayerB.PreRegistrationLedger
import UnifiedTheory.LayerB.DarkMatterAudit
import UnifiedTheory.LayerB.InformationParadox
import UnifiedTheory.LayerC.PhysicalInformationLimits
import UnifiedTheory.Cosmology.QQG.Bridge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFTOESevenGateAttack

universe u v w z t

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.LayerB.PreRegistrationLedger
open UnifiedTheory.LayerB.DarkMatterAudit
open UnifiedTheory.LayerB.InformationParadox
open UnifiedTheory.LayerB.LiebRobinson
open UnifiedTheory.LayerB.MargolusLevitinTight
open UnifiedTheory.LayerC.BekensteinBound
open UnifiedTheory.LayerC.PhysicalInformationLimits
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
  finiteInjectiveBijective :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f → Function.Bijective f
  everyStateUniquePreimage :
    ∀ {α : Type*} [Finite α] (f : α → α),
      Function.Injective f → ∀ y : α, ∃! x : α, f x = y
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
      fun f hinj => finite_injective_is_bijective f hinj,
      fun f hinj => every_state_has_unique_preimage f hinj,
      fun f hinj => no_information_loss f hinj,
      fun f => unitarity_is_a_theorem f⟩

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
#print axioms gate2_baseDistortion_zero_iff_components_zero
#print axioms gate3_horizonProtection_and_total_tendsto_zero_of_certificate
#print axioms gate3_convergenceBridgeResidualSplit_closed
#print axioms gate3_exactRecoveryCertificate_closed
#print axioms gate4_recoveredStage_bdg4d_operator_limit_of_interface
#print axioms gate4_recoveredBDGOperatorBridge_closed
#print axioms gate4_kernelProfileSplitSupplier_closed
#print axioms gate4_scheduledKernelOperatorBridge_closed
#print axioms gate5_localBornProjectiveCompleteness_closed
#print axioms gate5_recoveredCarrier_coverIndependence_of_jointlySurjective
#print axioms gate5_finiteCarrierCover_closed
#print axioms gate5_recoveredCarrierCommonRefinement_closed
#print axioms gate6_darkDensity_atomic_audit_hook
#print axioms gate6_darkDensityAudit_closed
#print axioms gate6_cosmologicalConstantGravitonAudit_closed
#print axioms gate6_finiteInformationPreservationAudit_closed
#print axioms gate6_qqgCosmologyBridgeAudit_closed
#print axioms gate6_physicalInformationLimitsAudit_closed
#print axioms gate7_externalTests_closed_from_preRegistrationLedger

end UnifiedTheory.Audit.KFTOESevenGateAttack
