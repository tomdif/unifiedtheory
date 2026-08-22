/-
  Audit/KFRecoveredCSpecHopfBornPhaseClassSeparation.lean

  Recovered-stage Born data separates Hopf phase classes.

  `KFRecoveredCSpecHopfBornSeparation` proves that local Pauli/all-axis Born
  data is equivalent to the recovered quotient Bloch observable.  `KFHopfSurjectivity`
  and `KFHopfFiberExactness` prove that the normalized algebraic Hopf quotient
  is bijective onto the unit Bloch sphere.

  This file composes those results at recovered-stage scope:

  * equality of recovered phase classes is equivalent to equality of recovered
    quotient Bloch observables;
  * equality of Pauli Born data is equivalent to equality of recovered phase
    classes;
  * equality of all-axis Born data is equivalent to equality of recovered phase
    classes.

  This is finite local projective-qubit observational completeness.  It is not
  detector dynamics, continuum QFT, spin/statistics, Standard Model recovery,
  quotient topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfSurjectivity
import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornSeparation

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

variable {site site' : Type*}

theorem quotientBlochAt_eq_of_phaseClassAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (h : I.phaseClassAt n x = J.phaseClassAt m y) :
    I.quotientBlochAt n x = J.quotientBlochAt m y := by
  simpa [
    phaseClassAt,
    quotientBlochAt,
    LocalHopfSpinorField.quotientBlochAt
  ] using congrArg UnitSpinorCoords.quotientUnitBloch h

theorem phaseClassAt_eq_of_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (hB : I.quotientBlochAt n x = J.quotientBlochAt m y) :
    I.phaseClassAt n x = J.phaseClassAt m y := by
  apply UnitSpinorCoords.quotientUnitBloch_injective
  simpa [
    phaseClassAt,
    quotientBlochAt,
    LocalHopfSpinorField.quotientBlochAt
  ] using hB

theorem phaseClassAt_eq_iff_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.phaseClassAt n x = J.phaseClassAt m y ↔
      I.quotientBlochAt n x = J.quotientBlochAt m y := by
  constructor
  · exact quotientBlochAt_eq_of_phaseClassAt_eq I J n m x y
  · exact phaseClassAt_eq_of_quotientBlochAt_eq I J n m x y

theorem samePauliBornData_iff_phaseClassAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SamePauliBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y := by
  constructor
  · intro h
    exact phaseClassAt_eq_of_quotientBlochAt_eq I J n m x y
      (quotientBlochAt_eq_of_samePauliBornData I J n m x y h)
  · intro h
    exact samePauliBornData_of_quotientBlochAt_eq I J n m x y
      (quotientBlochAt_eq_of_phaseClassAt_eq I J n m x y h)

theorem sameAllAxisBornData_iff_phaseClassAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SameAllAxisBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y := by
  constructor
  · intro h
    exact phaseClassAt_eq_of_quotientBlochAt_eq I J n m x y
      (quotientBlochAt_eq_of_sameAllAxisBornData I J n m x y h)
  · intro h
    exact sameAllAxisBornData_of_quotientBlochAt_eq I J n m x y
      (quotientBlochAt_eq_of_phaseClassAt_eq I J n m x y h)

theorem phaseClassAt_eq_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.phaseClassAt n x = J.phaseClassAt m y ↔
      SamePauliBornData I J n m x y := by
  exact (samePauliBornData_iff_phaseClassAt_eq I J n m x y).symm

theorem phaseClassAt_eq_iff_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.phaseClassAt n x = J.phaseClassAt m y ↔
      SameAllAxisBornData I J n m x y := by
  exact (sameAllAxisBornData_iff_phaseClassAt_eq I J n m x y).symm

theorem phaseRotate_samePhaseClassAt
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).phaseClassAt n x = I.phaseClassAt n x := by
  exact phaseRotate_phaseClassAt_eq I P n x

/-- Bundled local theorem: recovered-stage Born data is observationally complete
for the projective Hopf phase class. -/
theorem recoveredStage_local_born_projective_observational_completeness
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    (SamePauliBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y) ∧
    (SameAllAxisBornData I J n m x y ↔
      I.phaseClassAt n x = J.phaseClassAt m y) ∧
    (I.quotientBlochAt n x = J.quotientBlochAt m y ↔
      I.phaseClassAt n x = J.phaseClassAt m y) := by
  exact
    ⟨samePauliBornData_iff_phaseClassAt_eq I J n m x y,
      sameAllAxisBornData_iff_phaseClassAt_eq I J n m x y,
      (phaseClassAt_eq_iff_quotientBlochAt_eq I J n m x y).symm⟩

#print axioms RecoveredStageHopfFiberInterface.phaseClassAt_eq_of_quotientBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.samePauliBornData_iff_phaseClassAt_eq
#print axioms RecoveredStageHopfFiberInterface.sameAllAxisBornData_iff_phaseClassAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_samePhaseClassAt
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_born_projective_observational_completeness

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
