/-
  Audit/KFCausalCSpecRecoveredStageBDGProfile.lean

  Continuous-profile bridge for the recovered-stage BDG interface.

  The 4D gate/profile theorems in the volume sector are naturally stated with a
  real high-density parameter tending to `atTop`.  The recovered CSpec stages are
  indexed by `n : Nat`.  This file proves the small but important adapter:

      real profile limit atTop + density_n -> atTop
        ==> sequence-level per-layer asymptotics.

  It then packages that adapter into a recovered-stage/profile interface feeding
  the existing `RecoveredStageBDGAsymptoticInterface`.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDGInterface

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- Sequence-level BDG layer asymptotics obtained from continuous high-density
profiles sampled along a density sequence. -/
structure BDGProfileSequenceAsymptotics (layer : Type*) where
  layers : Finset layer
  density : ℕ → ℝ
  layerMean : layer → ℕ → ℝ
  profileMean : layer → ℝ → ℝ
  layerConstant : layer → ℝ
  layerSecond : layer → ℝ
  curvatureCoeff : ℝ
  phiAtPoint : ℝ
  boxPhi : ℝ
  curvaturePhi : ℝ
  density_tendsto_atTop : Tendsto density atTop atTop
  profile_tendsto :
    ∀ i ∈ layers,
      Tendsto (profileMean i) atTop
        (𝓝 (layerConstant i * phiAtPoint +
          layerSecond i * (boxPhi + curvatureCoeff * curvaturePhi)))
  layerMean_eventually_eq_profile :
    ∀ i, ∀ᶠ n in atTop, layerMean i n = profileMean i (density n)

namespace BDGProfileSequenceAsymptotics

theorem layer_asymptotics
    {layer : Type*} (A : BDGProfileSequenceAsymptotics layer) :
    ∀ i ∈ A.layers,
      Tendsto (A.layerMean i) atTop
        (𝓝 (A.layerConstant i * A.phiAtPoint +
          A.layerSecond i * (A.boxPhi + A.curvatureCoeff * A.curvaturePhi))) := by
  intro i hi
  have hsample :
      Tendsto (fun n => A.profileMean i (A.density n)) atTop
        (𝓝 (A.layerConstant i * A.phiAtPoint +
          A.layerSecond i * (A.boxPhi + A.curvatureCoeff * A.curvaturePhi))) :=
    (A.profile_tendsto i hi).comp A.density_tendsto_atTop
  have heq :
      (fun n => A.profileMean i (A.density n)) =ᶠ[atTop] A.layerMean i := by
    filter_upwards [A.layerMean_eventually_eq_profile i] with n hn
    exact hn.symm
  exact Filter.Tendsto.congr' heq hsample

#print axioms BDGProfileSequenceAsymptotics.layer_asymptotics

end BDGProfileSequenceAsymptotics

/-- A recovered-stage BDG interface whose per-layer asymptotics are supplied by
continuous high-density profiles sampled along the CSpec refinement sequence. -/
structure RecoveredStageBDGProfileSequenceInterface
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
  meanBDG : ℕ → ℝ
  bdgWeight : layer → ℝ
  selfCoeff : ℝ
  profile : BDGProfileSequenceAsymptotics layer
  exact_recovery :
    PhysicalHauptvermutungExactRecoveryCertificate
      cSpecWeight horizonSource repairSource
      countWindow curvatureBias spectralLocality
      scale areaCoeff step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap
  mean_decomposition :
    ∀ n,
      meanBDG n =
        selfCoeff * profile.phiAtPoint +
          ∑ i ∈ profile.layers, bdgWeight i * profile.layerMean i n
  moment_cancel :
    selfCoeff + ∑ i ∈ profile.layers,
      bdgWeight i * profile.layerConstant i = 0
  moment_normalization :
    ∑ i ∈ profile.layers, bdgWeight i * profile.layerSecond i = 1

namespace RecoveredStageBDGProfileSequenceInterface

def toAsymptoticInterface
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGProfileSequenceInterface cell layer) :
    RecoveredStageBDGAsymptoticInterface cell layer where
  cSpecWeight := I.cSpecWeight
  horizonSource := I.horizonSource
  repairSource := I.repairSource
  countWindow := I.countWindow
  curvatureBias := I.curvatureBias
  spectralLocality := I.spectralLocality
  scale := I.scale
  areaCoeff := I.areaCoeff
  step := I.step
  descentRate := I.descentRate
  remainder := I.remainder
  total := I.total
  edge := I.edge
  candidate := I.candidate
  stepFloor := I.stepFloor
  weightBase := I.weightBase
  sourceBase := I.sourceBase
  residualGap := I.residualGap
  layers := I.profile.layers
  meanBDG := I.meanBDG
  layerMean := I.profile.layerMean
  bdgWeight := I.bdgWeight
  layerConstant := I.profile.layerConstant
  layerSecond := I.profile.layerSecond
  selfCoeff := I.selfCoeff
  curvatureCoeff := I.profile.curvatureCoeff
  phiAtPoint := I.profile.phiAtPoint
  boxPhi := I.profile.boxPhi
  curvaturePhi := I.profile.curvaturePhi
  exact_recovery := I.exact_recovery
  mean_decomposition := I.mean_decomposition
  layer_asymptotics := I.profile.layer_asymptotics
  moment_cancel := I.moment_cancel
  moment_normalization := I.moment_normalization

theorem eventually_recoveredStage
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGProfileSequenceInterface cell layer) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n) := by
  exact I.toAsymptoticInterface.eventually_recoveredStage

theorem profile_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGProfileSequenceInterface cell layer) :
    Tendsto I.meanBDG atTop
      (𝓝 (I.profile.boxPhi + I.profile.curvatureCoeff * I.profile.curvaturePhi)) := by
  exact I.toAsymptoticInterface.bdg_dalembertian_tendsto

theorem rssPoissonError_zero_and_profile_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGProfileSequenceInterface cell layer)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0) ∧
      Tendsto I.meanBDG atTop
        (𝓝 (I.profile.boxPhi + I.profile.curvatureCoeff * I.profile.curvaturePhi)) := by
  exact I.toAsymptoticInterface.rssPoissonError_zero_and_bdg_dalembertian_tendsto
    errorScale

theorem rssPoissonError_zero_and_standard_profile_bdg_dalembertian_tendsto
    {cell layer : Type*} [Fintype cell]
    (I : RecoveredStageBDGProfileSequenceInterface cell layer)
    (errorScale : ℝ)
    (hcurvatureCoeff : I.profile.curvatureCoeff = (-1 / 2 : ℝ)) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0) ∧
      Tendsto I.meanBDG atTop
        (𝓝 (I.profile.boxPhi - (1 / 2) * I.profile.curvaturePhi)) := by
  exact
    I.toAsymptoticInterface.rssPoissonError_zero_and_standard_bdg_dalembertian_tendsto
      errorScale hcurvatureCoeff

#print axioms RecoveredStageBDGProfileSequenceInterface.toAsymptoticInterface
#print axioms RecoveredStageBDGProfileSequenceInterface.eventually_recoveredStage
#print axioms RecoveredStageBDGProfileSequenceInterface.profile_bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_profile_bdg_dalembertian_tendsto
#print axioms RecoveredStageBDGProfileSequenceInterface.rssPoissonError_zero_and_standard_profile_bdg_dalembertian_tendsto

end RecoveredStageBDGProfileSequenceInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
