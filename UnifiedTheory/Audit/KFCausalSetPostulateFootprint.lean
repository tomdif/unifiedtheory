/-
  Audit/KFCausalSetPostulateFootprint.lean

  MACHINE-CHECKED POSTULATE FOOTPRINTS

  This file checks transitive declaration dependencies for the finite core,
  projective transport, and the clock/weak interpretation layer.
-/

import Batteries.Tactic.PrintDependents
import UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.hashCommand false

namespace UnifiedTheory.Audit.KFCausalSetPostulateFootprint

open Lean Elab Command

private def declarationDependsOn
    (environment : Environment) (target dependency : Name) : Bool :=
  let initial :=
    Batteries.Tactic.CollectDependents.mkState #[(dependency, true)] false
  let (result, _state) :=
    Batteries.Tactic.CollectDependents.collect target
      |>.run environment |>.run initial
  result

/-- Fail the build unless the first declaration transitively uses the second. -/
elab "#assert_depends_on " target:ident dependency:ident : command => do
  let environment ← getEnv
  let targetName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo target
  let dependencyName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo dependency
  unless declarationDependsOn environment targetName dependencyName do
    throwErrorAt target
      "postulate-footprint failure: {targetName} does not depend on {dependencyName}"

/-- Fail the build if the first declaration transitively uses the second. -/
elab "#assert_not_depends_on " target:ident dependency:ident : command => do
  let environment ← getEnv
  let targetName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo target
  let dependencyName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo dependency
  if declarationDependsOn environment targetName dependencyName then
    throwErrorAt target
      "postulate-footprint failure: {targetName} unexpectedly depends on {dependencyName}"

/-! ## 1. Finite selection footprint -/

open UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw

-- Purity of the pair and the explicit sign rule are genuine dependencies.
#assert_depends_on signResponse_uniqueBalancedSignatureLaw
  elementary_symmetry_derives_chiral_phase
#assert_depends_on signResponse_uniqueBalancedSignatureLaw
  bilinearSelectedPhase?

-- Neither clock interpretation nor harmonic-action bridges select the member.
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  SatisfiesClockBirthIdentification
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  causalPositiveOrientationEvolution
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  VacuumSpectatorCausalAction
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  IsExchangeableNormalizedSpectatorSource
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  SatisfiesFractionalVolumeCouplingBridge
#assert_not_depends_on signResponse_uniqueBalancedSignatureLaw
  numberVolumeVacuumSpectatorCausalAction

-- The variational predicate is only an equivalent encoding of that same rule.
#assert_depends_on variationalSelection_iff_signMatching
  signResponse_uniqueBalancedSignatureLaw
#assert_not_depends_on variationalSelection_iff_signMatching
  SatisfiesClockBirthIdentification
#assert_not_depends_on variationalSelection_iff_signMatching
  causalPositiveOrientationEvolution

/-! ## 2. Transport and microscopic-action footprint -/

-- The abstract chiral sign transports without the clock dictionary.
#assert_not_depends_on causalPositiveOrientationGrowthLaw_sign_transport
  SatisfiesClockBirthIdentification
#assert_not_depends_on causalPositiveOrientationGrowthLaw_sign_transport
  causalPositiveOrientationEvolution
#assert_not_depends_on causalPositiveOrientationGrowthLaw_sign_transport
  SatisfiesFractionalVolumeCouplingBridge
#assert_not_depends_on causalPositiveOrientationGrowthLaw_sign_transport
  VacuumSpectatorCausalAction
#assert_not_depends_on causalPositiveOrientationGrowthLaw_sign_transport
  IsExchangeableNormalizedSpectatorSource

-- The newest spectator-action law does use the exchangeable action container.
#assert_depends_on microscopicSpectatorGrowth_projective_stronglyPositive
  VacuumSpectatorCausalAction
#assert_depends_on microscopicSpectatorGrowth_projective_stronglyPositive
  source_eq_uniform
#assert_not_depends_on microscopicSpectatorGrowth_projective_stronglyPositive
  SatisfiesFractionalVolumeCouplingBridge
#assert_depends_on completeMicroscopicActionConjugationEquivalence
  VacuumSpectatorCausalAction
#assert_not_depends_on completeMicroscopicActionConjugationEquivalence
  SatisfiesClockBirthIdentification
#assert_not_depends_on completeMicroscopicActionConjugationEquivalence
  SatisfiesFractionalVolumeCouplingBridge
#assert_not_depends_on completeMicroscopicActionConjugationEquivalence
  numberVolumeVacuumSpectatorCausalAction

/-! ## 3. Interpretation-layer footprint -/

-- The weak-handedness capstone genuinely uses clock evolution and the weak map.
#assert_depends_on finite_causal_positive_energy_derives_left_handed_weak_interaction
  causalPositiveOrientationEvolution
#assert_depends_on finite_causal_positive_energy_derives_left_handed_weak_interaction
  causalWeakVertex

-- It interprets a fixed representative rather than using the sign selector.
#assert_not_depends_on finite_causal_positive_energy_derives_left_handed_weak_interaction
  signResponse_uniqueBalancedSignatureLaw

/-- Checked summary object consumed by the root build after every dependency
assertion above has succeeded. -/
theorem postulateFootprintAudit_complete : True := trivial

#print axioms postulateFootprintAudit_complete

end UnifiedTheory.Audit.KFCausalSetPostulateFootprint
