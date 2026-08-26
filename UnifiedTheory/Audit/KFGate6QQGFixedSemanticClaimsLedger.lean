/-
  Audit/KFGate6QQGFixedSemanticClaimsLedger.lean

  FIXED-SEMANTIC, FALSIFIABLE QQG EMERGENCE LEDGER

  `QQGEmergenceClaims` deliberately permits arbitrary predicates.  That is a
  useful interface, but it is not itself a physical specification.  This
  module instantiates the interface with six fixed numerical protocol
  semantics.  The formal predictions are tied to the repository's explicit
  beta functions, tensor-ratio formula, and harmonic rank-one QQG readout.

  Protocol registrations and results are data types.  No result, pass token,
  or emergence witness is constructed here.  Lean proves only structural
  calculations and logical consequences of externally supplied results.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger

noncomputable section

open scoped ENNReal
open Set MeasureTheory
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout
open UnifiedTheory.Cosmology.QQG

local instance qqgScenarioMeasurableSpace : MeasurableSpace QQGScenario := ⊤

/-! ## 1. Preregistration and externally supplied protocol results -/

/-- Metadata frozen before looking at a result.  A value only specifies a
protocol; it is not evidence that the protocol passed. -/
structure QQGProtocolRegistration where
  protocolId : String
  frozenAt : ℕ

/-- Metadata attached to an externally acquired result.  The dataset digest
is deliberately opaque to this arithmetic layer; authenticity remains an
external data-governance obligation. -/
structure QQGProtocolResultToken where
  protocolId : String
  observedAt : ℕ
  datasetDigest : String

/-- The result belongs to the frozen protocol and was acquired strictly after
registration. -/
def QQGProtocolRegistration.Matches
    (registration : QQGProtocolRegistration)
    (result : QQGProtocolResultToken) : Prop :=
  registration.protocolId = result.protocolId ∧
    registration.frozenAt < result.observedAt

/-- One preregistration containing fixed tolerances for the six QQG
emergence tests.  The fields select tolerances, not predicates. -/
structure QQGFixedSemanticPreregistration where
  ghostProtocol : QQGProtocolRegistration
  ghostNegativityTolerance : ℝ
  ghostNegativityTolerance_nonneg : 0 ≤ ghostNegativityTolerance
  weylProtocol : QQGProtocolRegistration
  tensorRatioTolerance : ℝ
  tensorRatioTolerance_nonneg : 0 ≤ tensorRatioTolerance
  betaProtocol : QQGProtocolRegistration
  betaXiTolerance : ℝ
  betaXiTolerance_nonneg : 0 ≤ betaXiTolerance
  betaLambdaTolerance : ℝ
  betaLambdaTolerance_nonneg : 0 ≤ betaLambdaTolerance
  noBoundaryProtocol : QQGProtocolRegistration
  noBoundaryLogBayesThreshold : ℝ
  coincidenceProtocol : QQGProtocolRegistration
  coincidenceLogScaleTolerance : ℝ
  coincidenceLogScaleTolerance_nonneg :
    0 ≤ coincidenceLogScaleTolerance
  emergentGRProtocol : QQGProtocolRegistration
  einsteinResidualTolerance : ℝ
  einsteinResidualTolerance_nonneg : 0 ≤ einsteinResidualTolerance

/-- Spectral scan proxy for ghost containment.  A significantly negative
minimum physical spectral weight refutes the fixed claim. -/
structure QQGGhostSpectralResult where
  token : QQGProtocolResultToken
  minimumPhysicalSpectralWeight : ℝ
  uncertainty : ℝ
  uncertainty_nonneg : 0 ≤ uncertainty

/-- CMB tensor-ratio result used to test the explicit QQG `r_predicted`
observable. -/
structure QQGWeylTensorResult where
  token : QQGProtocolResultToken
  measuredTensorRatio : ℝ
  uncertainty : ℝ
  uncertainty_nonneg : 0 ≤ uncertainty

/-- Flow measurement used to compare both components with the explicit QQG
beta functions at one coupling point. -/
structure QQGBetaFlowResult where
  token : QQGProtocolResultToken
  matterWeight : ℝ
  measuredBetaXi : ℝ
  measuredBetaLambda : ℝ
  betaXiUncertainty : ℝ
  betaXiUncertainty_nonneg : 0 ≤ betaXiUncertainty
  betaLambdaUncertainty : ℝ
  betaLambdaUncertainty_nonneg : 0 ≤ betaLambdaUncertainty

/-- Model-selection result for the no-boundary proposal.  The fixed pass rule
uses the conservative lower error bar on the log Bayes factor. -/
structure QQGNoBoundaryResult where
  token : QQGProtocolResultToken
  logBayesFactor : ℝ
  uncertainty : ℝ
  uncertainty_nonneg : 0 ≤ uncertainty

/-- Measured logarithmic locations of tachyon crossing, strong-coupling
entry, and reheating. -/
structure QQGScaleCoincidenceResult where
  token : QQGProtocolResultToken
  tachyonLogScale : ℝ
  strongCouplingLogScale : ℝ
  reheatingLogScale : ℝ
  uncertainty : ℝ
  uncertainty_nonneg : 0 ≤ uncertainty

/-- Normalized residual of the proposed Einstein effective equation at a
matching scale. -/
structure QQGEinsteinResidualResult where
  token : QQGProtocolResultToken
  normalizedResidual : ℝ
  uncertainty : ℝ
  uncertainty_nonneg : 0 ≤ uncertainty

/-- External protocol outputs indexed exactly like the six fields of
`QQGEmergenceClaims`.  This structure contains raw results, not proofs that
they satisfy the preregistration. -/
structure QQGFixedSemanticProtocolResults where
  ghost : ℝ → ℝ → QQGGhostSpectralResult
  weyl : ℝ → ℝ → QQGWeylTensorResult
  beta : QQGCouplings → QQGBetaFlowResult
  noBoundary : ℝ → ℝ → QQGNoBoundaryResult
  coincidence : ℝ → QQGScaleCoincidenceResult
  emergentGR : ℝ → QQGEinsteinResidualResult

/-! ## 2. Six fixed pass and refutation predicates -/

def GhostSpectralPasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam₀ N : ℝ) : Prop :=
  P.ghostProtocol.Matches (R.ghost lam₀ N).token ∧
    -(P.ghostNegativityTolerance + (R.ghost lam₀ N).uncertainty) ≤
      (R.ghost lam₀ N).minimumPhysicalSpectralWeight

def GhostSpectralRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam₀ N : ℝ) : Prop :=
  P.ghostProtocol.Matches (R.ghost lam₀ N).token ∧
    (R.ghost lam₀ N).minimumPhysicalSpectralWeight <
      -(P.ghostNegativityTolerance + (R.ghost lam₀ N).uncertainty)

/-- The Weyl/CMB semantic is agreement with the explicit QQG tensor-ratio
formula, within preregistered tolerance plus reported uncertainty. -/
def WeylTensorPasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam_tH N_e : ℝ) : Prop :=
  P.weylProtocol.Matches (R.weyl lam_tH N_e).token ∧
    |(R.weyl lam_tH N_e).measuredTensorRatio -
        r_predicted lam_tH N_e| ≤
      P.tensorRatioTolerance + (R.weyl lam_tH N_e).uncertainty

def WeylTensorRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam_tH N_e : ℝ) : Prop :=
  P.weylProtocol.Matches (R.weyl lam_tH N_e).token ∧
    P.tensorRatioTolerance + (R.weyl lam_tH N_e).uncertainty <
      |(R.weyl lam_tH N_e).measuredTensorRatio -
        r_predicted lam_tH N_e|

/-- The beta-scheme semantic compares measured flow with both explicit
one-loop beta functions. -/
def BetaFlowPasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (c : QQGCouplings) : Prop :=
  P.betaProtocol.Matches (R.beta c).token ∧
    |(R.beta c).measuredBetaXi - betaXi c| ≤
      P.betaXiTolerance + (R.beta c).betaXiUncertainty ∧
    |(R.beta c).measuredBetaLambda -
        betaLambda (R.beta c).matterWeight c| ≤
      P.betaLambdaTolerance + (R.beta c).betaLambdaUncertainty

def BetaFlowRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (c : QQGCouplings) : Prop :=
  P.betaProtocol.Matches (R.beta c).token ∧
    (P.betaXiTolerance + (R.beta c).betaXiUncertainty <
        |(R.beta c).measuredBetaXi - betaXi c| ∨
      P.betaLambdaTolerance + (R.beta c).betaLambdaUncertainty <
        |(R.beta c).measuredBetaLambda -
          betaLambda (R.beta c).matterWeight c|)

def NoBoundaryPasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam₀ N : ℝ) : Prop :=
  P.noBoundaryProtocol.Matches (R.noBoundary lam₀ N).token ∧
    P.noBoundaryLogBayesThreshold ≤
      (R.noBoundary lam₀ N).logBayesFactor -
        (R.noBoundary lam₀ N).uncertainty

def NoBoundaryRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam₀ N : ℝ) : Prop :=
  P.noBoundaryProtocol.Matches (R.noBoundary lam₀ N).token ∧
    (R.noBoundary lam₀ N).logBayesFactor +
        (R.noBoundary lam₀ N).uncertainty <
      P.noBoundaryLogBayesThreshold

def ScaleCoincidencePasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam_tH : ℝ) : Prop :=
  P.coincidenceProtocol.Matches (R.coincidence lam_tH).token ∧
    |(R.coincidence lam_tH).tachyonLogScale -
        (R.coincidence lam_tH).strongCouplingLogScale| ≤
      P.coincidenceLogScaleTolerance +
        (R.coincidence lam_tH).uncertainty ∧
    |(R.coincidence lam_tH).strongCouplingLogScale -
        (R.coincidence lam_tH).reheatingLogScale| ≤
      P.coincidenceLogScaleTolerance +
        (R.coincidence lam_tH).uncertainty

def ScaleCoincidenceRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (lam_tH : ℝ) : Prop :=
  P.coincidenceProtocol.Matches (R.coincidence lam_tH).token ∧
    (P.coincidenceLogScaleTolerance +
          (R.coincidence lam_tH).uncertainty <
        |(R.coincidence lam_tH).tachyonLogScale -
          (R.coincidence lam_tH).strongCouplingLogScale| ∨
      P.coincidenceLogScaleTolerance +
          (R.coincidence lam_tH).uncertainty <
        |(R.coincidence lam_tH).strongCouplingLogScale -
          (R.coincidence lam_tH).reheatingLogScale|)

def EinsteinResidualPasses
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (matchingScale : ℝ) : Prop :=
  P.emergentGRProtocol.Matches (R.emergentGR matchingScale).token ∧
    |(R.emergentGR matchingScale).normalizedResidual| ≤
      P.einsteinResidualTolerance +
        (R.emergentGR matchingScale).uncertainty

def EinsteinResidualRefuted
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) (matchingScale : ℝ) : Prop :=
  P.emergentGRProtocol.Matches (R.emergentGR matchingScale).token ∧
    P.einsteinResidualTolerance +
        (R.emergentGR matchingScale).uncertainty <
      |(R.emergentGR matchingScale).normalizedResidual|

theorem ghostSpectral_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {lam₀ N : ℝ}
    (h : GhostSpectralPasses P R lam₀ N) :
    ¬ GhostSpectralRefuted P R lam₀ N := by
  intro hRefuted
  exact (not_lt_of_ge h.2) hRefuted.2

theorem weylTensor_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {lam_tH N_e : ℝ}
    (h : WeylTensorPasses P R lam_tH N_e) :
    ¬ WeylTensorRefuted P R lam_tH N_e := by
  intro hRefuted
  exact (not_lt_of_ge h.2) hRefuted.2

theorem betaFlow_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {c : QQGCouplings}
    (h : BetaFlowPasses P R c) : ¬ BetaFlowRefuted P R c := by
  intro hRefuted
  rcases hRefuted.2 with hXi | hLambda
  · exact (not_lt_of_ge h.2.1) hXi
  · exact (not_lt_of_ge h.2.2) hLambda

theorem noBoundary_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {lam₀ N : ℝ}
    (h : NoBoundaryPasses P R lam₀ N) :
    ¬ NoBoundaryRefuted P R lam₀ N := by
  intro hRefuted
  have hUncertainty := (R.noBoundary lam₀ N).uncertainty_nonneg
  linarith [h.2, hRefuted.2]

theorem scaleCoincidence_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {lam_tH : ℝ}
    (h : ScaleCoincidencePasses P R lam_tH) :
    ¬ ScaleCoincidenceRefuted P R lam_tH := by
  intro hRefuted
  rcases hRefuted.2 with hFirst | hSecond
  · exact (not_lt_of_ge h.2.1) hFirst
  · exact (not_lt_of_ge h.2.2) hSecond

theorem einsteinResidual_passes_not_refuted
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults} {matchingScale : ℝ}
    (h : EinsteinResidualPasses P R matchingScale) :
    ¬ EinsteinResidualRefuted P R matchingScale := by
  intro hRefuted
  exact (not_lt_of_ge h.2) hRefuted.2

/-! ## 3. Fixed `QQGEmergenceClaims` and empirical evidence -/

/-- The promised fixed-semantic instantiation.  Callers may supply protocol
data, but cannot replace any of the six predicates by `True` or an unrelated
proposition. -/
def fixedSemanticQQGEmergenceClaims
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) : QQGEmergenceClaims where
  ghostResolution := GhostSpectralPasses P R
  weylPerturbationConsistency := WeylTensorPasses P R
  physicalBetaScheme := BetaFlowPasses P R
  noBoundaryInitialState := NoBoundaryPasses P R
  strongCouplingCoincidence := ScaleCoincidencePasses P R
  emergentGR := EinsteinResidualPasses P R

/-- External empirical evidence for every evaluation point required by the
current global QQG hypothesis API.  No inhabitant is supplied in this file. -/
structure QQGFixedSemanticEmpiricalEvidence
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) : Prop where
  ghost : ∀ lam₀ N, GhostSpectralPasses P R lam₀ N
  weyl : ∀ lam_tH N_e, WeylTensorPasses P R lam_tH N_e
  beta : ∀ c, BetaFlowPasses P R c
  noBoundary : ∀ lam₀ N, NoBoundaryPasses P R lam₀ N
  coincidence : ∀ lam_tH, ScaleCoincidencePasses P R lam_tH
  emergentGR : ∀ matchingScale, EinsteinResidualPasses P R matchingScale

/-- Empirical protocol evidence can be passed into the existing conditional
QQG bridge, but the conversion does not create any evidence. -/
theorem QQGFixedSemanticEmpiricalEvidence.toEmergenceHypotheses
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults}
    (E : QQGFixedSemanticEmpiricalEvidence P R) :
    QQGEmergenceHypotheses (fixedSemanticQQGEmergenceClaims P R) := by
  exact ⟨E.ghost, E.weyl, E.beta, E.noBoundary,
    E.coincidence, E.emergentGR⟩

/-- A single preregistered refutation blocks the corresponding global
empirical-evidence bundle.  This witnesses genuine falsifiability without
asserting that a refuting result exists. -/
inductive QQGFixedSemanticRefutation
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults) : Prop where
  | ghost (lam₀ N : ℝ) (h : GhostSpectralRefuted P R lam₀ N)
  | weyl (lam_tH N_e : ℝ) (h : WeylTensorRefuted P R lam_tH N_e)
  | beta (c : QQGCouplings) (h : BetaFlowRefuted P R c)
  | noBoundary (lam₀ N : ℝ) (h : NoBoundaryRefuted P R lam₀ N)
  | coincidence (lam_tH : ℝ) (h : ScaleCoincidenceRefuted P R lam_tH)
  | emergentGR (matchingScale : ℝ)
      (h : EinsteinResidualRefuted P R matchingScale)

theorem empiricalEvidence_not_refutation
    {P : QQGFixedSemanticPreregistration}
    {R : QQGFixedSemanticProtocolResults}
    (E : QQGFixedSemanticEmpiricalEvidence P R) :
    ¬ QQGFixedSemanticRefutation P R := by
  intro hRefuted
  cases hRefuted with
  | ghost lam₀ N h => exact ghostSpectral_passes_not_refuted (E.ghost lam₀ N) h
  | weyl lam_tH N_e h => exact weylTensor_passes_not_refuted (E.weyl lam_tH N_e) h
  | beta c h => exact betaFlow_passes_not_refuted (E.beta c) h
  | noBoundary lam₀ N h =>
      exact noBoundary_passes_not_refuted (E.noBoundary lam₀ N) h
  | coincidence lam_tH h =>
      exact scaleCoincidence_passes_not_refuted (E.coincidence lam_tH) h
  | emergentGR matchingScale h =>
      exact einsteinResidual_passes_not_refuted (E.emergentGR matchingScale) h

/-! ## 4. Exact structural evidence from the harmonic binary readout -/

/-- Real-valued low-branch probability predicted by the exact pushforward
law. -/
def harmonicBinaryPredictedLowFrequency : ℝ := 1 / 2

/-- Real-valued high-branch probability predicted by the exact pushforward
law. -/
def harmonicBinaryPredictedHighFrequency : ℝ := 1 / 2

/-- Mean e-fold count of the exact two-point readout law. -/
def harmonicBinaryPredictedMeanEFolds : ℝ :=
  harmonicBinaryPredictedLowFrequency * binaryQQGLowScenario.N_e +
    harmonicBinaryPredictedHighFrequency * binaryQQGHighScenario.N_e

/-- Variance of the e-fold count under the exact two-point readout law. -/
def harmonicBinaryPredictedVarianceEFolds : ℝ :=
  harmonicBinaryPredictedLowFrequency *
      (binaryQQGLowScenario.N_e - harmonicBinaryPredictedMeanEFolds) ^ 2 +
    harmonicBinaryPredictedHighFrequency *
      (binaryQQGHighScenario.N_e - harmonicBinaryPredictedMeanEFolds) ^ 2

def harmonicBinaryPredictedLowTensorRatio : ℝ :=
  r_predicted binaryQQGLowScenario.lam_tH binaryQQGLowScenario.N_e

def harmonicBinaryPredictedHighTensorRatio : ℝ :=
  r_predicted binaryQQGHighScenario.lam_tH binaryQQGHighScenario.N_e

theorem harmonicBinaryPredictedMeanEFolds_eq :
    harmonicBinaryPredictedMeanEFolds = 55 := by
  norm_num [harmonicBinaryPredictedMeanEFolds,
    harmonicBinaryPredictedLowFrequency,
    harmonicBinaryPredictedHighFrequency,
    binaryQQGLowScenario, binaryQQGHighScenario]

theorem harmonicBinaryPredictedVarianceEFolds_eq :
    harmonicBinaryPredictedVarianceEFolds = 25 := by
  norm_num [harmonicBinaryPredictedVarianceEFolds,
    harmonicBinaryPredictedMeanEFolds,
    harmonicBinaryPredictedLowFrequency,
    harmonicBinaryPredictedHighFrequency,
    binaryQQGLowScenario, binaryQQGHighScenario]

theorem harmonicBinaryPredictedLowTensorRatio_pos :
    0 < harmonicBinaryPredictedLowTensorRatio := by
  exact r_predicted_pos binaryQQGLowScenario.lam_tH_pos
    binaryQQGLowScenario.N_e_pos

theorem harmonicBinaryPredictedHighTensorRatio_pos :
    0 < harmonicBinaryPredictedHighTensorRatio := by
  exact r_predicted_pos binaryQQGHighScenario.lam_tH_pos
    binaryQQGHighScenario.N_e_pos

/-- All structural facts available without empirical data. -/
structure QQGFixedSemanticStructuralEvidence (S : QQGScenario) : Prop where
  qqgCalculation : QQGProvenConclusions S
  binaryReadoutNonconstant :
    ∃ first second : ∀ n : ℕ, CausalSetGrowthBranch n,
      harmonicRankOneQQGReadout first ≠ harmonicRankOneQQGReadout second
  lowMass : ∀ chirality : Fin 2,
    (harmonicBinaryQQGInitialMeasure chirality).measure
      {binaryQQGLowScenario} = 1 / 2
  highMass : ∀ chirality : Fin 2,
    (harmonicBinaryQQGInitialMeasure chirality).measure
      {binaryQQGHighScenario} = 1 / 2
  meanEFolds : harmonicBinaryPredictedMeanEFolds = 55
  varianceEFolds : harmonicBinaryPredictedVarianceEFolds = 25
  lowTensorRatioPositive : 0 < harmonicBinaryPredictedLowTensorRatio
  highTensorRatioPositive : 0 < harmonicBinaryPredictedHighTensorRatio

theorem qqgFixedSemanticStructuralEvidence_closed (S : QQGScenario) :
    QQGFixedSemanticStructuralEvidence S := by
  exact
    ⟨qqg_proven_conclusions S,
      harmonicRankOneQQGReadout_nonconstant,
      harmonicBinaryQQGInitialMeasure_low,
      harmonicBinaryQQGInitialMeasure_high,
      harmonicBinaryPredictedMeanEFolds_eq,
      harmonicBinaryPredictedVarianceEFolds_eq,
      harmonicBinaryPredictedLowTensorRatio_pos,
      harmonicBinaryPredictedHighTensorRatio_pos⟩

/-! ## 5. A preregistered, directly falsifiable binary prediction -/

/-- Tolerances and chronology for a forward test of the concrete harmonic
binary readout.  Predicted central values are fixed definitions above and are
not caller-supplied fields. -/
structure HarmonicBinaryQQGPredictionSpecification where
  registration : QQGProtocolRegistration
  lowFrequencyTolerance : ℝ
  lowFrequencyTolerance_nonneg : 0 ≤ lowFrequencyTolerance
  meanEFoldsTolerance : ℝ
  meanEFoldsTolerance_nonneg : 0 ≤ meanEFoldsTolerance
  lowTensorRatioTolerance : ℝ
  lowTensorRatioTolerance_nonneg : 0 ≤ lowTensorRatioTolerance
  highTensorRatioTolerance : ℝ
  highTensorRatioTolerance_nonneg : 0 ≤ highTensorRatioTolerance

/-- External result of the binary forward-test protocol.  No value is
constructed in this module. -/
structure HarmonicBinaryQQGPredictionResult where
  token : QQGProtocolResultToken
  observedLowFrequency : ℝ
  observedMeanEFolds : ℝ
  observedLowTensorRatio : ℝ
  observedHighTensorRatio : ℝ
  lowFrequencyUncertainty : ℝ
  lowFrequencyUncertainty_nonneg : 0 ≤ lowFrequencyUncertainty
  meanEFoldsUncertainty : ℝ
  meanEFoldsUncertainty_nonneg : 0 ≤ meanEFoldsUncertainty
  lowTensorRatioUncertainty : ℝ
  lowTensorRatioUncertainty_nonneg : 0 ≤ lowTensorRatioUncertainty
  highTensorRatioUncertainty : ℝ
  highTensorRatioUncertainty_nonneg : 0 ≤ highTensorRatioUncertainty

def HarmonicBinaryQQGPredictionPasses
    (P : HarmonicBinaryQQGPredictionSpecification)
    (R : HarmonicBinaryQQGPredictionResult) : Prop :=
  P.registration.Matches R.token ∧
    |R.observedLowFrequency - harmonicBinaryPredictedLowFrequency| ≤
      P.lowFrequencyTolerance + R.lowFrequencyUncertainty ∧
    |R.observedMeanEFolds - harmonicBinaryPredictedMeanEFolds| ≤
      P.meanEFoldsTolerance + R.meanEFoldsUncertainty ∧
    |R.observedLowTensorRatio - harmonicBinaryPredictedLowTensorRatio| ≤
      P.lowTensorRatioTolerance + R.lowTensorRatioUncertainty ∧
    |R.observedHighTensorRatio - harmonicBinaryPredictedHighTensorRatio| ≤
      P.highTensorRatioTolerance + R.highTensorRatioUncertainty

def HarmonicBinaryQQGPredictionRefuted
    (P : HarmonicBinaryQQGPredictionSpecification)
    (R : HarmonicBinaryQQGPredictionResult) : Prop :=
  P.registration.Matches R.token ∧
    (P.lowFrequencyTolerance + R.lowFrequencyUncertainty <
        |R.observedLowFrequency - harmonicBinaryPredictedLowFrequency| ∨
      P.meanEFoldsTolerance + R.meanEFoldsUncertainty <
        |R.observedMeanEFolds - harmonicBinaryPredictedMeanEFolds| ∨
      P.lowTensorRatioTolerance + R.lowTensorRatioUncertainty <
        |R.observedLowTensorRatio - harmonicBinaryPredictedLowTensorRatio| ∨
      P.highTensorRatioTolerance + R.highTensorRatioUncertainty <
        |R.observedHighTensorRatio - harmonicBinaryPredictedHighTensorRatio|)

theorem harmonicBinaryPrediction_passes_not_refuted
    {P : HarmonicBinaryQQGPredictionSpecification}
    {R : HarmonicBinaryQQGPredictionResult}
    (h : HarmonicBinaryQQGPredictionPasses P R) :
    ¬ HarmonicBinaryQQGPredictionRefuted P R := by
  intro hRefuted
  rcases hRefuted.2 with hLow | hMean | hLowTensor | hHighTensor
  · exact (not_lt_of_ge h.2.1) hLow
  · exact (not_lt_of_ge h.2.2.1) hMean
  · exact (not_lt_of_ge h.2.2.2.1) hLowTensor
  · exact (not_lt_of_ge h.2.2.2.2) hHighTensor

/-! ## 6. Conditional handoff to the existing QQG bridge -/

/-- Structural evidence is unconditional; the conditional Einstein branch is
obtained only when an external empirical-evidence bundle is supplied. -/
theorem fixedSemanticQQG_conditionalEinsteinBranch
    (P : QQGFixedSemanticPreregistration)
    (R : QQGFixedSemanticProtocolResults)
    (S : QQGScenario)
    (E : QQGFixedSemanticEmpiricalEvidence P R) :
    QQGConditionalEinsteinBranch (fixedSemanticQQGEmergenceClaims P R) S := by
  exact qqg_cosmology_implies_conditional_einstein
    (fixedSemanticQQGEmergenceClaims P R) S E.toEmergenceHypotheses

#print axioms qqgFixedSemanticStructuralEvidence_closed
#print axioms empiricalEvidence_not_refutation
#print axioms harmonicBinaryPrediction_passes_not_refuted
#print axioms fixedSemanticQQG_conditionalEinsteinBranch

end

end UnifiedTheory.Audit.KFGate6QQGFixedSemanticClaimsLedger
