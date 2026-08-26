/-
  Audit/KFTOEWellFoundedFullClosureTarget.lean

  Seven-gate closure target using finite natural-rank termination for Gate 3.

  This replaces the stale dependence on a real asymptotic convergence package
  by the smaller `StoppableNatRankStep` obligation.  It derives Gate 2, exact
  finite Gate 3 recovery, and the density/operator/recovery part of Gate 4.
  The genuinely independent physical inputs remain explicit.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOEFullClosureTarget
import UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedGate4Handoff
import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
import UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
import UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
import UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEWellFoundedFullClosureTarget

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3Supplier
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedRank
open UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3WellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornProtectedWellFoundedGate3
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornWellFoundedGate4Handoff
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
open UnifiedTheory.Audit.KFCausalSetHarmonicBornAtlasExactAudit
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
open UnifiedTheory.Cosmology.QQG
open UnifiedTheory.Audit.KFTOESevenGateAttack
open UnifiedTheory.Audit.KFTOEFullClosureTarget

variable {ι X Y chart : Type*} [Fintype ι]
variable [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
variable {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
variable {scale c step descentRate remainder total : ℕ → ℝ}
variable {edge : ℕ → ι → E4}
variable {candidate : ℕ → ι → Equiv.Perm Direction}
variable {countQuantum curvatureQuantum spectralQuantum : ℕ → ι → ℕ}
variable {countGap curvatureGap spectralGap : ℝ}

/-- The finite-spectrum information required by the existing Gate 2 semantic
theorem, projected from well-founded Gate 3 data. -/
def wellFoundedGate3QuantizedResiduals
    (D : MicroscopicGate3WellFoundedRankData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap where
  countGap_pos := D.countGap_pos
  curvatureGap_pos := D.curvatureGap_pos
  spectralGap_pos := D.spectralGap_pos
  count_eq := D.count_eq
  curvature_eq := D.curvature_eq
  spectral_eq := D.spectral_eq

/-- Honest Gate 3 closure: the recovery deadline is constructed and is exactly
the initial natural-valued defect rank. -/
structure Gate3WellFoundedExactRecoveryClosed
    (D : MicroscopicGate3WellFoundedRankData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) : Prop where
  horizonProtection :
    ∀ n,
      linearResponse (w n) (source n) (finiteAreaChange (c n) (J n)) = 0 ∧
        quadraticResponse (w n) (source n)
          (finiteAreaChange (c n) (J n)) = 0
  exactZeroAfter :
    ∀ n, D.defectRank 0 ≤ n →
      total n = 0 ∧
        (∀ i, countWindow n i = 0) ∧
          (∀ i, curvatureBias n i = 0) ∧
            (∀ i, spectralLocality n i = 0) ∧
              candidate n = canonicalCSpecBridgeCandidate (edge n)
  recoveredAfter :
    ∀ n, D.defectRank 0 ≤ n →
      PhysicalHauptvermutungRecoveredStage
        (countWindow n) (curvatureBias n) (spectralLocality n)
        (scale n) (total n) (edge n) (candidate n)
  totalTendsToZero : Tendsto total atTop (nhds 0)

theorem gate3_wellFoundedExactRecovery_closed
    (D : MicroscopicGate3WellFoundedRankData w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap) :
    Gate3WellFoundedExactRecoveryClosed D where
  horizonProtection := D.horizonProtection
  exactZeroAfter := D.exact_zero_after_initial_defectRank
  recoveredAfter := D.recoveredStage_after_initial_defectRank
  totalTendsToZero := by
    have heq : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] total := by
      filter_upwards [D.eventually_exact_zero] with n hn
      exact hn.1.symm
    exact tendsto_const_nhds.congr' heq

variable
  (G : MicroscopicGate3WellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    w J source countWindow curvatureBias spectralLocality
    scale c step descentRate remainder total edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

/-- Gate 4 target with the density, operator-profile, and exact-recovery
interface supplied by the well-founded handoff.  Only horizon estimation and
dynamical null balance remain separate propositions. -/
noncomputable def wellFoundedGate4HorizonEinsteinAnalyticTargets
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    Gate4HorizonEinsteinAnalyticTargets where
  horizonEstimatorConvergence := horizonEstimatorConvergence
  physicalScheduledDensity :=
    Tendsto (fun n => (G.chartCertificate n).density) atTop atTop
  bdgKernelProfileCertificate :=
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean
        G.operatorKernelData.toProfileData ((G.chartCertificate n).density))
      atTop
      (nhds (BDG4DOperatorProfileData.target
        G.operatorKernelData.toProfileData))
  nullBalanceFromDynamics := nullBalanceFromDynamics
  recoveredBDGInterfaceSupplied := G.Closed errorScale

theorem wellFoundedGate4HorizonEinsteinAnalytic_closed
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics) :
    Gate4HorizonEinsteinAnalyticClosed
      (wellFoundedGate4HorizonEinsteinAnalyticTargets G errorScale
        horizonEstimatorConvergence nullBalanceFromDynamics) := by
  have H := G.closed errorScale
  exact
    ⟨hhorizon, H.scheduledDensityTendsToInfinity,
      H.chartOperatorLimit, hnull, H⟩

/-- The seven-gate ledger with Gate 2 and Gate 3 constructively discharged by
well-founded data and the proved portion of Gate 4 filled by its handoff. -/
noncomputable def wellFoundedTOEClosureTargets
    (gate1Targets : Gate1MicroscopicLawTargets)
    (gate5Targets : Gate5QFTStandardModelIRTargets)
    (gate6Targets : Gate6CosmologyBlackHoleTargets)
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    TOEClosureTargets where
  gate1Targets := gate1Targets
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery := Gate3WellFoundedExactRecoveryClosed G.gate3
  gate4Targets :=
    wellFoundedGate4HorizonEinsteinAnalyticTargets G errorScale
      horizonEstimatorConvergence nullBalanceFromDynamics
  gate5Targets := gate5Targets
  gate6Targets := gate6Targets
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Conditional full ledger closure along the viable finite-rank route.

The theorem derives Gate 2, finite-time Gate 3, the scheduled-density/operator/
recovery portion of Gate 4, and the Gate 7 protocol audit.  Gate 1, the two
remaining Gate 4 propositions, Gate 5, and Gate 6 are intentionally explicit
hypotheses and are not presented as proved physics. -/
theorem wellFoundedTOEClosureTargets_closed
    {gate1Targets : Gate1MicroscopicLawTargets}
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    {gate6Targets : Gate6CosmologyBlackHoleTargets}
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hgate1 : Gate1MicroscopicLawClosed gate1Targets)
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hgate6 : Gate6CosmologyBlackHoleClosed gate6Targets) :
    TOEClosureClosed
      (wellFoundedTOEClosureTargets G gate1Targets gate5Targets gate6Targets
        errorScale horizonEstimatorConvergence nullBalanceFromDynamics) := by
  exact
    ⟨hgate1,
      quantizedGate3Residuals_gate2HauptvermutungSemantic_closed
        (wellFoundedGate3QuantizedResiduals G.gate3),
      gate3_wellFoundedExactRecovery_closed G.gate3,
      wellFoundedGate4HorizonEinsteinAnalytic_closed G hhorizon hnull,
      hgate5, hgate6,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-! ## Honest harmonic end-to-end ledger -/

/-- Alternative seven-gate target whose closure predicate uses *literally* the
Born-shell atlas realization built from the action-selected raw harmonic
schedule and the canonical positive-radial completion, for both chiralities.

This record deliberately does not reuse `TOEClosureTargets.gate1Targets`.
That older field is hard-coded to the fixed complete-chiral atlas law, which
is not definitionally or propositionally identified with the running
harmonic Born-shell law.  Keeping a separate target prevents certificates for
the two laws from being silently conflated. -/
structure ActionSelectedHarmonicTOEClosureTargets : Type where
  gate2Targets : Gate2HauptvermutungSemanticTargets
  gate3ExactRecovery : Prop
  gate4Targets : Gate4HorizonEinsteinAnalyticTargets
  gate5Targets : Gate5QFTStandardModelIRTargets
  gate6Targets : Gate6CosmologyBlackHoleTargets
  gate7Targets : Gate7ExternalTestTargets

/-- Honest closure predicate for the harmonic alternative.  The two Gate 1
certificates refer to the same harmonic Born-shell laws.  Their raw coupling
schedule is selected by the vacuum action; the positive-radial completion is a
separate canonical construction. -/
structure ActionSelectedHarmonicTOEClosureClosed
    (T : ActionSelectedHarmonicTOEClosureTargets) : Prop where
  gate1Zero : Gate1HarmonicBornShellAtlasRealizationClosed (0 : Fin 2)
  gate1One : Gate1HarmonicBornShellAtlasRealizationClosed (1 : Fin 2)
  gate2Closed : Gate2HauptvermutungSemanticClosed T.gate2Targets
  gate3Closed : T.gate3ExactRecovery
  gate4Closed : Gate4HorizonEinsteinAnalyticClosed T.gate4Targets
  gate5Closed : Gate5QFTStandardModelIRClosed T.gate5Targets
  gate6Closed : Gate6CosmologyBlackHoleClosed T.gate6Targets
  gate7Closed : Gate7ExternalTestClosed T.gate7Targets

variable {chirality : Fin 2}
variable
  {parentSchedule :
    (n : ℕ) → RankedGrowthPath CausalSetGrowthBranch n}
variable {observe : (n : ℕ) → CausalSetGrowthBranch n → ι}
variable {corrector : ℕ → ι → ℝ}
variable {correctorCoeff : ℕ → ℝ}

variable
  (H : HarmonicBornProtectedWellFoundedGate4ScheduledKernelData
    (ι := ι) (X := X) (Y := Y) (chart := chart)
    chirality parentSchedule observe J
    countWindow curvatureBias spectralLocality corrector
    scale c total correctorCoeff edge candidate
    countQuantum curvatureQuantum spectralQuantum
    countGap curvatureGap spectralGap)

/-- Finite-spectrum Gate 2 data projected from the *harmonic* Gate 3 supplier. -/
def harmonicWellFoundedGate3QuantizedResiduals :
    QuantizedGate3Residuals
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
      countGap curvatureGap spectralGap where
  countGap_pos := H.gate3.countGap_pos
  curvatureGap_pos := H.gate3.curvatureGap_pos
  spectralGap_pos := H.gate3.spectralGap_pos
  count_eq := H.gate3.count_eq
  curvature_eq := H.gate3.curvature_eq
  spectral_eq := H.gate3.spectral_eq

/-- Gate 4 target filled specifically by the harmonic Born protected-source
handoff.  `H` contains the still-unproved source-driven `rank_step`, the
residual-to-chart identities, the positive affine density schedule, and the
independent analytic kernel package. -/
noncomputable def harmonicWellFoundedGate4HorizonEinsteinAnalyticTargets
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    Gate4HorizonEinsteinAnalyticTargets where
  horizonEstimatorConvergence := horizonEstimatorConvergence
  physicalScheduledDensity :=
    Tendsto (fun n => (H.chartCertificate n).density) atTop atTop
  bdgKernelProfileCertificate :=
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean
        H.operatorKernelData.toProfileData ((H.chartCertificate n).density))
      atTop
      (nhds (BDG4DOperatorProfileData.target
        H.operatorKernelData.toProfileData))
  nullBalanceFromDynamics := nullBalanceFromDynamics
  recoveredBDGInterfaceSupplied := H.Closed errorScale

theorem harmonicWellFoundedGate4HorizonEinsteinAnalytic_closed
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics) :
    Gate4HorizonEinsteinAnalyticClosed
      (harmonicWellFoundedGate4HorizonEinsteinAnalyticTargets H errorScale
        horizonEstimatorConvergence nullBalanceFromDynamics) := by
  have hClosed := H.closed errorScale
  exact
    ⟨hhorizon, hClosed.scheduledDensityTendsToInfinity,
      hClosed.chartOperatorLimit, hnull, hClosed⟩

/-- Strongest current well-founded target whose Gate 1, Gate 3, Gate 4, and
causal-history Gate 6 components all use the harmonic Born construction.  Gate
6's measure slot is an infinite causal-growth measure, not yet a cosmological
readout.  This remains a conditional aggregate ledger: no theorem here yet
identifies the Gate 4 continuum, Gate 5 QFT, and scenario `S` as limits of one
shared microscopic model, and evidence for the fixed QQG claims ledger remains
an explicit closure hypothesis. -/
noncomputable def actionSelectedHarmonicWellFoundedTOEClosureTargets
    (gate5Targets : Gate5QFTStandardModelIRTargets)
    (claims : QQGEmergenceClaims)
    (S : UnifiedTheory.Cosmology.QQG.QQGScenario)
    (lateStructureFormation gravitationalWaveCompatibility : Prop)
    (errorScale : ℝ)
    (horizonEstimatorConvergence nullBalanceFromDynamics : Prop) :
    ActionSelectedHarmonicTOEClosureTargets where
  gate2Targets :=
    gate2QuantizedResidualSemanticTargets
      countWindow curvatureBias spectralLocality
      countQuantum curvatureQuantum spectralQuantum
  gate3ExactRecovery := H.gate3.Closed
  gate4Targets :=
    harmonicWellFoundedGate4HorizonEinsteinAnalyticTargets H errorScale
      horizonEstimatorConvergence nullBalanceFromDynamics
  gate5Targets := gate5Targets
  gate6Targets :=
    gate6CosmologyBlackHoleTargetsOfNamedCosmologyBlackHoleBridge claims S
      (gate6NamedTargetsOfActionSelectedHarmonicBornCausalGrowthMeasure
        lateStructureFormation gravitationalWaveCompatibility)
  gate7Targets := gate7PreRegistrationLedgerTargets

/-- Reduced conditional capstone for the honest harmonic alternative.

The only Gate 1 hypothesis is the exact finite noncancellation check for the
canonical positive-radial Born correction on the displayed 140-edge atlas in
chirality zero; reflection conjugacy proves chirality one.  Selection of the
raw harmonic schedule and every other growth-law field are theorems.  `H`
ties Gate 3 to the harmonic Born weights and protected source, but itself
supplies the unresolved rank update, chart matching, density schedule, and
analytic kernel.  Gate 6's bare causal-measure hypothesis is removed by the
infinite trajectory measure, while its physical cosmological readout remains
outside this ledger and its QQG emergence evidence remains explicit. -/
theorem actionSelectedHarmonicWellFoundedTOEClosureTargets_closed
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    (claims : QQGEmergenceClaims)
    {S : UnifiedTheory.Cosmology.QQG.QQGScenario}
    {lateStructureFormation gravitationalWaveCompatibility : Prop}
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hAtlasZero : HarmonicBornShellAtlasTransitionNonzero (0 : Fin 2))
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hQQGEmergence : QQGEmergenceHypotheses claims)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    ActionSelectedHarmonicTOEClosureClosed
      (actionSelectedHarmonicWellFoundedTOEClosureTargets H gate5Targets claims S
        lateStructureFormation gravitationalWaveCompatibility errorScale
        horizonEstimatorConvergence nullBalanceFromDynamics) := by
  exact
    ⟨gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
        (0 : Fin 2) hAtlasZero,
      gate1HarmonicBornShellAtlasRealization_closed_of_transition_nonzero
        (1 : Fin 2)
        (harmonicBornShellAtlasTransitionNonzero_one_of_zero hAtlasZero),
      quantizedGate3Residuals_gate2HauptvermutungSemantic_closed
        (harmonicWellFoundedGate3QuantizedResiduals H),
      H.gate3.closed,
      harmonicWellFoundedGate4HorizonEinsteinAnalytic_closed H hhorizon hnull,
      hgate5,
      gate6_cosmologyBlackHole_closed_of_actionSelectedHarmonicBornCausalGrowthMeasure
        claims S hQQGEmergence hHP hlate hgw,
      gate7_externalTests_closed_from_preRegistrationLedger⟩

/-- The exact rational-root atlas audit removes the last finite Gate 1 premise
from the harmonic capstone.  The remaining arguments are precisely the
continuum/horizon, Gate 5, and physical Gate 6 bridge obligations displayed in
the theorem; `H` still contains the separately supplied Gate 4 chart/kernel
data and, unless instantiated by the source-driven sector, its Gate 3 update. -/
theorem actionSelectedHarmonicWellFoundedTOEClosureTargets_closed_exactAtlas
    {gate5Targets : Gate5QFTStandardModelIRTargets}
    (claims : QQGEmergenceClaims)
    {S : UnifiedTheory.Cosmology.QQG.QQGScenario}
    {lateStructureFormation gravitationalWaveCompatibility : Prop}
    {errorScale : ℝ}
    {horizonEstimatorConvergence nullBalanceFromDynamics : Prop}
    (hhorizon : horizonEstimatorConvergence)
    (hnull : nullBalanceFromDynamics)
    (hgate5 : Gate5QFTStandardModelIRClosed gate5Targets)
    (hQQGEmergence : QQGEmergenceHypotheses claims)
    (hHP : Gate6HaydenPreskillMicroscopicEvaporationBridgeClosed)
    (hlate : lateStructureFormation)
    (hgw : gravitationalWaveCompatibility) :
    ActionSelectedHarmonicTOEClosureClosed
      (actionSelectedHarmonicWellFoundedTOEClosureTargets H gate5Targets claims S
        lateStructureFormation gravitationalWaveCompatibility errorScale
        horizonEstimatorConvergence nullBalanceFromDynamics) := by
  exact actionSelectedHarmonicWellFoundedTOEClosureTargets_closed H claims
    harmonicBornShellAtlasTransitionNonzero_zero
    hhorizon hnull hgate5 hQQGEmergence hHP hlate hgw

#print axioms gate3_wellFoundedExactRecovery_closed
#print axioms wellFoundedGate4HorizonEinsteinAnalytic_closed
#print axioms wellFoundedTOEClosureTargets_closed
#print axioms harmonicWellFoundedGate4HorizonEinsteinAnalytic_closed
#print axioms actionSelectedHarmonicWellFoundedTOEClosureTargets_closed

end

end UnifiedTheory.Audit.KFTOEWellFoundedFullClosureTarget
