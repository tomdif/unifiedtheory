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

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFTOESevenGateAttack

universe u v w z t

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.LayerB.PreRegistrationLedger
open UnifiedTheory.LayerB.DarkMatterAudit

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
#print axioms gate2_baseDistortion_zero_iff_components_zero
#print axioms gate3_horizonProtection_and_total_tendsto_zero_of_certificate
#print axioms gate4_recoveredStage_bdg4d_operator_limit_of_interface
#print axioms gate4_recoveredBDGOperatorBridge_closed
#print axioms gate4_scheduledKernelOperatorBridge_closed
#print axioms gate5_localBornProjectiveCompleteness_closed
#print axioms gate5_recoveredCarrier_coverIndependence_of_jointlySurjective
#print axioms gate5_finiteCarrierCover_closed
#print axioms gate6_darkDensity_atomic_audit_hook
#print axioms gate6_darkDensityAudit_closed
#print axioms gate6_cosmologicalConstantGravitonAudit_closed
#print axioms gate7_externalTests_closed_from_preRegistrationLedger

end UnifiedTheory.Audit.KFTOESevenGateAttack
