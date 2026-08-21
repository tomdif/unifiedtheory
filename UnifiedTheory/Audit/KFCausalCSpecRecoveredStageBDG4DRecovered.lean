/-
  Audit/KFCausalCSpecRecoveredStageBDG4DRecovered.lean

  Concrete recovered-stage bridge for the reduced 4D BDG operator profile.

  Previous files established:

    * exact recovered CSpec stages force zero RSS/Poisson horizon error;
    * real high-density BDG profile limits can be sampled along `n : Nat`;
    * the reduced 4D BDG operator theorem supplies such a real profile source.

  This file combines those ingredients into one recovered-stage interface for
  the concrete one-channel 4D operator profile.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DOperator

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecEntropyFluxLimit
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- Exact recovered CSpec data plus a concrete reduced 4D BDG operator profile.

The `operatorData` field is still analytic/geometric data: it must be supplied
from the physical local chart and support/regularity/cone-bound estimates.  Once
it is supplied, this record has no remaining abstract BDG layer hypothesis. -/
structure RecoveredStageBDG4DOperatorInterface
    (cell : Type*) [Fintype cell] where
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
  density : ℕ → ℝ
  density_tendsto_atTop : Tendsto density atTop atTop
  phiAtPoint : ℝ
  curvaturePhi : ℝ
  operatorData : BDG4DOperatorProfileData
  exact_recovery :
    PhysicalHauptvermutungExactRecoveryCertificate
      cSpecWeight horizonSource repairSource
      countWindow curvatureBias spectralLocality
      scale areaCoeff step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase residualGap

namespace RecoveredStageBDG4DOperatorInterface

/-- The sampled 4D operator profile as a recovered-stage profile-sequence
interface with one BDG channel of weight `1`. -/
noncomputable def toProfileSequenceInterface
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) :
    RecoveredStageBDGProfileSequenceInterface cell Unit where
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
  meanBDG := fun n =>
    BDG4DOperatorProfileData.mean I.operatorData (I.density n)
  bdgWeight := fun _ => 1
  selfCoeff := 0
  profile :=
    I.operatorData.sequenceAsymptotics
      I.density I.density_tendsto_atTop I.phiAtPoint I.curvaturePhi
  exact_recovery := I.exact_recovery
  mean_decomposition := by
    intro n
    simp [BDG4DOperatorProfileData.sequenceAsymptotics]
  moment_cancel := by
    simp [BDG4DOperatorProfileData.sequenceAsymptotics]
  moment_normalization := by
    simp [BDG4DOperatorProfileData.sequenceAsymptotics]

theorem eventually_recoveredStage
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) :
    ∀ᶠ n in atTop,
      PhysicalHauptvermutungRecoveredStage
        (I.countWindow n) (I.curvatureBias n) (I.spectralLocality n)
        (I.scale n) (I.total n) (I.edge n) (I.candidate n) := by
  exact I.toProfileSequenceInterface.eventually_recoveredStage

theorem operator_tendsto
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell) :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean I.operatorData (I.density n))
      atTop
      (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) :=
  I.operatorData.sampled_tendsto I.density I.density_tendsto_atTop

theorem rssPoissonError_zero_and_operator_tendsto
    {cell : Type*} [Fintype cell]
    (I : RecoveredStageBDG4DOperatorInterface cell)
    (errorScale : ℝ) :
    (∀ᶠ n in atTop,
      ∀ i,
        rssPoissonError
          (I.countWindow n i) (I.curvatureBias n i) errorScale = 0) ∧
      Tendsto
        (fun n => BDG4DOperatorProfileData.mean I.operatorData (I.density n))
        atTop
        (𝓝 (BDG4DOperatorProfileData.target I.operatorData)) := by
  have h :=
    I.toProfileSequenceInterface.rssPoissonError_zero_and_profile_bdg_dalembertian_tendsto
      errorScale
  simpa [toProfileSequenceInterface, BDG4DOperatorProfileData.sequenceAsymptotics]
    using h

theorem recoveredStage_and_operator_tendsto
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
  exact ⟨I.eventually_recoveredStage, I.operator_tendsto⟩

#print axioms RecoveredStageBDG4DOperatorInterface.toProfileSequenceInterface
#print axioms RecoveredStageBDG4DOperatorInterface.eventually_recoveredStage
#print axioms RecoveredStageBDG4DOperatorInterface.operator_tendsto
#print axioms RecoveredStageBDG4DOperatorInterface.rssPoissonError_zero_and_operator_tendsto
#print axioms RecoveredStageBDG4DOperatorInterface.recoveredStage_and_operator_tendsto

end RecoveredStageBDG4DOperatorInterface

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
