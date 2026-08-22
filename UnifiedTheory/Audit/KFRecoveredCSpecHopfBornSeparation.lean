/-
  Audit/KFRecoveredCSpecHopfBornSeparation.lean

  Observational completeness for recovered-stage Hopf Born data.

  The previous files construct local gauge-invariant Born probabilities from
  recovered-stage Hopf quotient fibers and prove finite tomography.  This file
  turns that into a separation theorem:

  * equality of Pauli-X/Y/Z Born pairs is equivalent to equality of the local
    quotient Bloch observable;
  * equality of all arbitrary-axis Born pairs is equivalent to equality of the
    local quotient Bloch observable;
  * local stagewise `U(1)` gauge rotations preserve the complete Born data.

  This is finite local qubit observational completeness.  It is not continuum
  QFT, detector dynamics, spin/statistics, or Standard Model recovery.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornTomography

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

variable {site site' : Type*}

/-- Equality of the three Pauli-axis Born probability pairs at two local
recovered-stage sites. -/
def SamePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') : Prop :=
  I.bornXAt n x = J.bornXAt m y ∧
  I.bornYAt n x = J.bornYAt m y ∧
  I.bornZAt n x = J.bornZAt m y

/-- Equality of all arbitrary-axis Born probability pairs at two local
recovered-stage sites. -/
def SameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') : Prop :=
  ∀ A : UnitBlochAxis, I.bornAlongAt A n x = J.bornAlongAt A m y

theorem samePauliBornData_of_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (hB : I.quotientBlochAt n x = J.quotientBlochAt m y) :
    SamePauliBornData I J n m x y := by
  unfold SamePauliBornData
  exact
    ⟨by simpa [bornXAt] using congrArg UnitBlochCoords.bornX hB,
      by simpa [bornYAt] using congrArg UnitBlochCoords.bornY hB,
      by simpa [bornZAt] using congrArg UnitBlochCoords.bornZ hB⟩

theorem quotientBlochAt_eq_of_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (h : SamePauliBornData I J n m x y) :
    I.quotientBlochAt n x = J.quotientBlochAt m y := by
  rcases h with ⟨hX, hY, hZ⟩
  apply UnitBlochCoords.ext_coords
  · calc
      (I.quotientBlochAt n x).x = (I.bornXAt n x).expectation :=
        (bornXAt_expectation_eq_quotientBloch_x I n x).symm
      _ = (J.bornXAt m y).expectation :=
        congrArg BinaryBornPair.expectation hX
      _ = (J.quotientBlochAt m y).x :=
        bornXAt_expectation_eq_quotientBloch_x J m y
  · calc
      (I.quotientBlochAt n x).y = (I.bornYAt n x).expectation :=
        (bornYAt_expectation_eq_quotientBloch_y I n x).symm
      _ = (J.bornYAt m y).expectation :=
        congrArg BinaryBornPair.expectation hY
      _ = (J.quotientBlochAt m y).y :=
        bornYAt_expectation_eq_quotientBloch_y J m y
  · calc
      (I.quotientBlochAt n x).z = (I.bornZAt n x).expectation :=
        (bornZAt_expectation_eq_quotientBloch_z I n x).symm
      _ = (J.bornZAt m y).expectation :=
        congrArg BinaryBornPair.expectation hZ
      _ = (J.quotientBlochAt m y).z :=
        bornZAt_expectation_eq_quotientBloch_z J m y

theorem samePauliBornData_iff_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SamePauliBornData I J n m x y ↔
      I.quotientBlochAt n x = J.quotientBlochAt m y := by
  constructor
  · exact quotientBlochAt_eq_of_samePauliBornData I J n m x y
  · exact samePauliBornData_of_quotientBlochAt_eq I J n m x y

theorem sameAllAxisBornData_of_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (hB : I.quotientBlochAt n x = J.quotientBlochAt m y) :
    SameAllAxisBornData I J n m x y := by
  intro A
  simpa [bornAlongAt] using congrArg (UnitBlochAxis.bornAlong A) hB

theorem samePauliBornData_of_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (h : SameAllAxisBornData I J n m x y) :
    SamePauliBornData I J n m x y := by
  unfold SamePauliBornData
  exact
    ⟨by
      calc
        I.bornXAt n x =
            I.bornAlongAt UnitBlochAxis.pauliX n x :=
          (bornAlongAt_pauliX_eq_bornXAt I n x).symm
        _ = J.bornAlongAt UnitBlochAxis.pauliX m y :=
          h UnitBlochAxis.pauliX
        _ = J.bornXAt m y :=
          bornAlongAt_pauliX_eq_bornXAt J m y,
      by
      calc
        I.bornYAt n x =
            I.bornAlongAt UnitBlochAxis.pauliY n x :=
          (bornAlongAt_pauliY_eq_bornYAt I n x).symm
        _ = J.bornAlongAt UnitBlochAxis.pauliY m y :=
          h UnitBlochAxis.pauliY
        _ = J.bornYAt m y :=
          bornAlongAt_pauliY_eq_bornYAt J m y,
      by
      calc
        I.bornZAt n x =
            I.bornAlongAt UnitBlochAxis.pauliZ n x :=
          (bornAlongAt_pauliZ_eq_bornZAt I n x).symm
        _ = J.bornAlongAt UnitBlochAxis.pauliZ m y :=
          h UnitBlochAxis.pauliZ
        _ = J.bornZAt m y :=
          bornAlongAt_pauliZ_eq_bornZAt J m y⟩

theorem quotientBlochAt_eq_of_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site')
    (h : SameAllAxisBornData I J n m x y) :
    I.quotientBlochAt n x = J.quotientBlochAt m y := by
  exact quotientBlochAt_eq_of_samePauliBornData I J n m x y
    (samePauliBornData_of_sameAllAxisBornData I J n m x y h)

theorem sameAllAxisBornData_iff_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SameAllAxisBornData I J n m x y ↔
      I.quotientBlochAt n x = J.quotientBlochAt m y := by
  constructor
  · exact quotientBlochAt_eq_of_sameAllAxisBornData I J n m x y
  · exact sameAllAxisBornData_of_quotientBlochAt_eq I J n m x y

theorem sameAllAxisBornData_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SameAllAxisBornData I J n m x y ↔
      SamePauliBornData I J n m x y := by
  constructor
  · exact samePauliBornData_of_sameAllAxisBornData I J n m x y
  · intro h
    exact sameAllAxisBornData_of_quotientBlochAt_eq I J n m x y
      (quotientBlochAt_eq_of_samePauliBornData I J n m x y h)

theorem phaseRotate_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    SamePauliBornData (I.phaseRotate P) I n n x x := by
  unfold SamePauliBornData
  exact
    ⟨phaseRotate_bornXAt_eq I P n x,
      phaseRotate_bornYAt_eq I P n x,
      phaseRotate_bornZAt_eq I P n x⟩

theorem phaseRotate_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    SameAllAxisBornData (I.phaseRotate P) I n n x x := by
  intro A
  exact phaseRotate_bornAlongAt_eq I P A n x

/-- Bundled local observational-completeness theorem: the complete Born data is
exactly the local quotient Bloch observable, and local gauge rotations preserve
that data. -/
theorem recoveredStage_local_born_observational_completeness
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    (SamePauliBornData I J n m x y ↔
      I.quotientBlochAt n x = J.quotientBlochAt m y) ∧
    (SameAllAxisBornData I J n m x y ↔
      I.quotientBlochAt n x = J.quotientBlochAt m y) := by
  exact
    ⟨samePauliBornData_iff_quotientBlochAt_eq I J n m x y,
      sameAllAxisBornData_iff_quotientBlochAt_eq I J n m x y⟩

#print axioms RecoveredStageHopfFiberInterface.quotientBlochAt_eq_of_samePauliBornData
#print axioms RecoveredStageHopfFiberInterface.samePauliBornData_iff_quotientBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.sameAllAxisBornData_iff_quotientBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.sameAllAxisBornData_iff_samePauliBornData
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_sameAllAxisBornData
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_born_observational_completeness

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
