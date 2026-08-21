/-
  Audit/KFCausalCSpecRecoveredStageBDGInterface.lean

  Bridge from exact recovered CSpec stages to the existing BDG continuum
  assembler.

  Scope: this file does not prove the interval-volume/RNC/Watson asymptotics.
  It packages those named analytic hypotheses together with the exact recovery
  certificate and proves that the combined object feeds both:

    * the finite RSS/Poisson horizon-flux error gate; and
    * the BDG per-layer continuum d'Alembertian assembler.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageGRLimit
import UnifiedTheory.Audit.KFCausalCSpecBDGDerivation

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBDGDerivation
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- A bundled interface from exact recovered CSpec stages to the BDG continuum
assembler.

The `exact_recovery` field is the finite Hauptvermutung/recovery side.  The
`layer_asymptotics`, `mean_decomposition`, and moment fields are the analytic
BDG/RNC side already consumed by `bdg_dalembertian_from_layers`. -/
structure RecoveredStageBDGAsymptoticInterface
    (cell layer : Type*) [Fintype cell] where
  cSpecWeight : ℕ → cell → ℝ
  horizonSource : ℕ → cell → ℝ
  repairSource : ℕ → cell → ℝ
  countWindow : ℕ → cell → ℝ
  curvatureBias : ℕ → cell → ℝ
  spectralLocality : ℕ → cell → ℝ
  scale : ℕ → ℝ
  areaCoeff : ℕ → ℝ
  step : ℕ → ℝ
  descentRate : ℕ → ℝ
  remainder : ℕ → ℝ
  total : ℕ → ℝ
  edge : ℕ → cell → E4
  candidate : ℕ → cell → Equiv.Perm Direction
  stepFloor : ℝ
  weightBase : ℝ
  sourceBase : ℝ
  residualGap : ℝ
  layers : Finset layer
  meanBDG : ℕ → ℝ
  layerMean : layer → ℕ → ℝ
  bdgWeight : layer → ℝ
  layerConstant : layer → ℝ
  layerSecond : layer → ℝ
  selfCoeff : ℝ
  curvatureCoeff : ℝ
  phiAtPoint : ℝ
  boxPhi : ℝ
  curvaturePhi : ℝ
  exact_recovery :
    PhysicalHauptvermutungExactRecoveryCertificate
      cSpecWeight horizonSource repairSource
      countWindow curvatureBias spectralLocality
      scale areaCoeff step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap
  mean_decomposition :
    ∀ n,
      meanBDG n =
        selfCoeff * phiAtPoint +
          ∑ i ∈ layers, bdgWeight i * layerMean i n
  layer_asymptotics :
    ∀ i ∈ layers,
      Tendsto (layerMean i) atTop
        (𝓝 (layerConstant i * phiAtPoint +
          layerSecond i * (boxPhi + curvatureCoeff * curvaturePhi)))
  moment_cancel :
    selfCoeff + ∑ i ∈ layers, bdgWeight i * layerConstant i = 0
  moment_normalization :
    ∑ i ∈ layers, bdgWeight i * layerSecond i = 1

namespace RecoveredStageBDGAsymptoticInterface

theorem eventually_recoveredStage
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n) := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_recoveredStage
      I.exact_recovery

theorem eventually_rssPoissonError_zero
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer)
    (errorScale : ℝ) :
    ∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0 := by
  exact
    physicalHauptvermutungExactRecoveryCertificate_eventually_rssPoissonError_zero
      I.exact_recovery

theorem bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer) :
    Tendsto I.meanBDG atTop
      (𝓝 (I.boxPhi + I.curvatureCoeff * I.curvaturePhi)) := by
  exact
    bdg_dalembertian_from_layers
      atTop I.layers I.meanBDG I.layerMean
      I.bdgWeight I.layerConstant I.layerSecond
      I.selfCoeff I.curvatureCoeff I.phiAtPoint I.boxPhi I.curvaturePhi
      I.mean_decomposition I.layer_asymptotics
      I.moment_cancel I.moment_normalization

theorem recoveredStage_and_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer) :
    (∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n)) ∧
      Tendsto I.meanBDG atTop
        (𝓝 (I.boxPhi + I.curvatureCoeff * I.curvaturePhi)) := by
  exact ⟨I.eventually_recoveredStage, I.bdg_dalembertian_tendsto⟩

theorem rssPoissonError_zero_and_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0) ∧
      Tendsto I.meanBDG atTop
        (𝓝 (I.boxPhi + I.curvatureCoeff * I.curvaturePhi)) := by
  exact ⟨I.eventually_rssPoissonError_zero errorScale, I.bdg_dalembertian_tendsto⟩

theorem standard_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer)
    (hcurvatureCoeff : I.curvatureCoeff = (-1 / 2 : ℝ)) :
    Tendsto I.meanBDG atTop
      (𝓝 (I.boxPhi - (1 / 2) * I.curvaturePhi)) := by
  have h := I.bdg_dalembertian_tendsto
  rw [hcurvatureCoeff] at h
  convert h using 2
  ring

theorem rssPoissonError_zero_and_standard_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGAsymptoticInterface cell layer)
    (errorScale : ℝ)
    (hcurvatureCoeff : I.curvatureCoeff = (-1 / 2 : ℝ)) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0) ∧
      Tendsto I.meanBDG atTop
        (𝓝 (I.boxPhi - (1 / 2) * I.curvaturePhi)) := by
  exact
    ⟨I.eventually_rssPoissonError_zero errorScale,
      I.standard_bdg_dalembertian_tendsto hcurvatureCoeff⟩

#print axioms RecoveredStageBDGAsymptoticInterface.eventually_recoveredStage
#print axioms RecoveredStageBDGAsymptoticInterface.eventually_rssPoissonError_zero
#print axioms RecoveredStageBDGAsymptoticInterface.bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGAsymptoticInterface.recoveredStage_and_bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGAsymptoticInterface.standard_bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGAsymptoticInterface.rssPoissonError_zero_and_standard_bdg_dalembertian_tendsto

end RecoveredStageBDGAsymptoticInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
