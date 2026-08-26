/-
  Audit/KFTOEAllAttacksCapstone.lean

  INTEGRATION OF THE GATE 4--6 ATTACKS

  This file records two deliberately different endpoints.

  * `HarmonicGate45FiniteBridgeClosed` is unconditional finite mathematics:
    the exact Gate-4 recovery stage and the causal Born local state/net share
    one chirality and site type, canonical incidence transport is recovered,
    and the local state/net is positive, normalized, isotonic, additive, local
    on disjoint finite regions, and Born-compatible.  The local computational
    expectations are identified with the fixed-parent conditional stage-PMF
    pushforward, and the pointwise-algebra zero-product boundary is retained
    explicitly.

  * `fixedSemanticActionSelectedHarmonicTOE_closed_of_nonzeroBDG` is the honest
    physical frontier.  It removes arbitrary QQG predicate meanings by using
    the fixed numerical protocol ledger and refuses the zero-BDG benchmark by
    requiring an identified nonzero target.  Continuum Gate-4, Gate-5, Gate-6,
    and empirical evidence remain explicit hypotheses.

  No empirical evidence value is constructed here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicHistoryGate4DerivedInputs
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteLocality
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteNetAdditivity
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance
import UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger
import UnifiedTheory.Audit.KFTOESharedHarmonicMicroscopicModel
import UnifiedTheory.Audit.KFTOEWellFoundedFullClosureTarget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEAllAttacksCapstone

noncomputable section

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalBornObservedWeight
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteLocality
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteNetAdditivity
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
open UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFTOEWellFoundedFullClosureTarget
open UnifiedTheory.Cosmology.QQG

universe u

variable {ι X Y chart : Type*} [Fintype ι] [Nonempty ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
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

/-! ## 1. Gate 4 recovery -> causal Born finite local net -/

open Classical in
/-- Finite facts that genuinely follow when the Gate-5 causal readout is
placed on the same recovered site type as the harmonic Gate-4 history.  The
readout remains a physical coarse-graining choice, but the state is no longer
an independent input once that choice is fixed. -/
structure HarmonicGate45FiniteBridgeClosed
    (R : HarmonicSingleGenerationReadout ι) : Prop where
  recoveredAtBound :
    PhysicalHauptvermutungRecoveredStage
      (countWindow H.recoveryBound)
      (curvatureBias H.recoveryBound)
      (spectralLocality H.recoveryBound)
      (scale H.recoveryBound) (total H.recoveryBound)
      (edge H.recoveryBound) (candidate H.recoveryBound)
  canonicalIncidenceTransport :
    ∀ i, candidate H.recoveryBound i =
      fourState.perm (edge H.recoveryBound i)
  causalBornWeights :
    ∀ i k,
      (harmonicLocalStateFunctional chirality R i
        (computationalEffectAt i k)).re =
          harmonicReadoutWeight chirality R i k
  conditionalStagePMFProvenance :
    ∀ i k,
      (causalBornStagePMF (canonicalHarmonicBornLaw chirality)
          (R.rankAt i) (R.parentSchedule (R.rankAt i))).map
          (R.observe (R.rankAt i)) k =
        ENNReal.ofReal
          ((harmonicLocalStateFunctional chirality R i
            (computationalEffectAt i k)).re)
  causalBornWeightsNormalized :
    ∀ i,
      ∑ k,
        (harmonicLocalStateFunctional chirality R i
          (computationalEffectAt i k)).re = 1
  finiteNetIsotony :
    ∀ {first second : Finset ι}, first ⊆ second →
      finiteLocalObservableAlgebra first ≤
        finiteLocalObservableAlgebra second
  finiteNetEmptyRegion :
    finiteLocalObservableAlgebra (∅ : Finset ι) = ⊥
  finiteNetFullRegion :
    finiteLocalObservableAlgebra (Finset.univ : Finset ι) = ⊤
  finiteNetAdditivity :
    ∀ first second : Finset ι,
      finiteLocalObservableAlgebra (first ∪ second) =
        finiteLocalObservableAlgebra first ⊔
          finiteLocalObservableAlgebra second
  finiteNetLocality :
    ∀ {first second : Finset ι}, Disjoint first second →
      ∀ (firstObservable : finiteLocalObservableAlgebra first)
        (secondObservable : finiteLocalObservableAlgebra second),
        (firstObservable : FiniteFieldObservable ι) *
            (secondObservable : FiniteFieldObservable ι) =
          (secondObservable : FiniteFieldObservable ι) *
            (firstObservable : FiniteFieldObservable ι)
  regionalStatesNormalized :
    ∀ i region,
      harmonicRegionStateFunctional chirality R i region 1 = 1
  regionalStatesPositive :
    ∀ i region
      (observable : finiteLocalObservableAlgebra region),
      0 ≤ (harmonicRegionStateFunctional chirality R i region
        (star observable * observable)).re
  regionalStatesIsotonyCompatible :
    ∀ i {first second : Finset ι} (h : first ⊆ second)
      (observable : finiteLocalObservableAlgebra first),
      harmonicRegionStateFunctional chirality R i second
          (StarSubalgebra.inclusion
            (finiteLocalObservableAlgebra_isotony h) observable) =
        harmonicRegionStateFunctional chirality R i first observable
  supportedDisjointProductsVanish :
    ∀ {first second : Finset ι}, Disjoint first second →
      ∀ {firstObservable secondObservable : FiniteFieldObservable ι},
        firstObservable ∈ regionSupportedObservables first →
        secondObservable ∈ regionSupportedObservables second →
        firstObservable * secondObservable = 0
  localStatePositive :
    ∀ i (observable : FiniteFieldObservable ι),
      0 ≤ (harmonicLocalStateFunctional chirality R i
        (star observable * observable)).re

/-- Gate-4 exact recovery and the derived causal Born finite net close the
finite Gate-4-to-Gate-5 seam without a separately supplied local state. -/
theorem harmonicGate45FiniteBridge_closed
    (R : HarmonicSingleGenerationReadout ι) :
    HarmonicGate45FiniteBridgeClosed H R := by
  have hRecovered :=
    H.recoveredStage_after_recoveryBound H.recoveryBound le_rfl
  exact
    { recoveredAtBound := hRecovered
      canonicalIncidenceTransport := hRecovered.candidate_transport
      causalBornWeights :=
        harmonicLocalStateFunctional_computationalEffect chirality R
      conditionalStagePMFProvenance :=
        harmonicCausalBornStagePMF_map_readout_eq_local_expectation chirality R
      causalBornWeightsNormalized :=
        harmonicLocalStateFunctional_computationalEffects_normalized chirality R
      finiteNetIsotony := fun h => finiteLocalObservableAlgebra_isotony h
      finiteNetEmptyRegion := finiteLocalObservableAlgebra_empty_eq_bot
      finiteNetFullRegion := finiteLocalObservableAlgebra_univ_eq_top
      finiteNetAdditivity := finiteLocalObservableAlgebra_union_eq_sup
      finiteNetLocality := fun h =>
        finiteLocalObservableAlgebra_commute_of_disjoint h
      regionalStatesNormalized :=
        harmonicRegionStateFunctional_normalized chirality R
      regionalStatesPositive :=
        harmonicRegionStateFunctional_positive chirality R
      regionalStatesIsotonyCompatible :=
        harmonicRegionStateFunctional_isotony_compatible chirality R
      supportedDisjointProductsVanish := fun h =>
        regionSupportedObservables_mul_eq_zero_of_disjoint h
      localStatePositive :=
        harmonicLocalStateFunctional_positive chirality R }

/-- The unconditional structural content now available across Gates 4--6.
This bundle is intentionally named *finite structural*, not physical TOE
closure: the Gate-4 package may still be the zero-profile benchmark, the
Gate-5 readout is a chosen coarse graining, and the QQG evidence here contains
only proved calculations and exact pushforward statistics. -/
structure HarmonicGate456FiniteStructuralClosed
    (R : HarmonicSingleGenerationReadout ι)
    (S : QQGScenario) (errorScale : ℝ) : Prop where
  gate4FiniteRecoveryAndLimit : H.Closed errorScale
  gate45FiniteBridge : HarmonicGate45FiniteBridgeClosed H R
  gate6CausalGrowthMeasure :
    Gate6ActionSelectedHarmonicBornCausalGrowthMeasureCertificate
  gate6FixedSemanticStructuralEvidence :
    QQGFixedSemanticStructuralEvidence S

theorem harmonicGate456FiniteStructural_closed
    (R : HarmonicSingleGenerationReadout ι)
    (S : QQGScenario) (errorScale : ℝ) :
    HarmonicGate456FiniteStructuralClosed H R S errorScale where
  gate4FiniteRecoveryAndLimit := H.closed errorScale
  gate45FiniteBridge := harmonicGate45FiniteBridge_closed H R
  gate6CausalGrowthMeasure :=
    gate6_actionSelectedHarmonicBornCausalGrowthMeasureCertificate_closed
  gate6FixedSemanticStructuralEvidence :=
    qqgFixedSemanticStructuralEvidence_closed S

/-! ## 2. One fixed-semantic physical frontier -/

/-- The strongest honest action-selected harmonic closure wrapper produced by
the present attacks.  In comparison with the previous capstone:

* QQG emergence predicates have fixed numerical meanings;
* empirical evidence for all six meanings is still required;
* a specified nonzero BDG target must be identified, excluding the canonical
  zero-profile consistency benchmark;
* the remaining continuum/QFT/cosmology inputs are still visible.

The target equality is returned with the ledger closure, so it cannot be
silently discarded by downstream callers. -/
theorem fixedSemanticActionSelectedHarmonicTOE_closed_of_nonzeroBDG
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    (P : QQGFixedSemanticPreregistration)
    (results : QQGFixedSemanticProtocolResults)
    {S : QQGScenario}
    {lateStructureFormation gravitationalWaveCompatibility : Prop}
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (physicalBDGTarget : ℝ)
    (hBDGTarget :
      BDG4DOperatorProfileData.target
        H.operatorKernelData.toProfileData = physicalBDGTarget)
    (hBDGTarget_nonzero : physicalBDGTarget ≠ 0)
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hQQGEvidence : QQGFixedSemanticEmpiricalEvidence P results)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    ActionSelectedHarmonicTOEClosureClosed
        (actionSelectedHarmonicWellFoundedTOEClosureTargets H gate5Targets
          (fixedSemanticQQGEmergenceClaims P results) S
          lateStructureFormation gravitationalWaveCompatibility errorScale
          horizonEstimatorConvergence nullBalanceFromDynamics) ∧
      BDG4DOperatorProfileData.target
          H.operatorKernelData.toProfileData = physicalBDGTarget ∧
        physicalBDGTarget ≠ 0 := by
  refine ⟨?_, hBDGTarget, hBDGTarget_nonzero⟩
  exact
    actionSelectedHarmonicWellFoundedTOEClosureTargets_closed_exactAtlas
      H (fixedSemanticQQGEmergenceClaims P results)
      hhorizon hnull hgate5 hQQGEvidence.toEmergenceHypotheses
      hHP hlate hgw

#print axioms harmonicGate45FiniteBridge_closed
#print axioms harmonicGate456FiniteStructural_closed
#print axioms fixedSemanticActionSelectedHarmonicTOE_closed_of_nonzeroBDG

end

end UnifiedTheory.Audit.KFTOEAllAttacksCapstone
