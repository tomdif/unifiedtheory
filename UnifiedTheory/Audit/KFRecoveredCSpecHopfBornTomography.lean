/-
  Audit/KFRecoveredCSpecHopfBornTomography.lean

  Local Born tomography for recovered-stage Hopf quotient fibers.

  `KFRecoveredCSpecHopfBornAxisObservable` proves valid arbitrary-axis Born
  probability pairs from the local quotient Bloch observable.  This file proves
  that those probabilities contain exactly the expected Bloch information:

  * the expectation of an arbitrary-axis Born pair is `a · B`;
  * the Pauli-X/Y/Z Born expectations recover the `x/y/z` Bloch coordinates;
  * at every recovered stage/site, the three Pauli Born pairs reconstruct the
    local quotient Bloch observable;
  * this reconstruction is invariant under local stagewise `U(1)` gauge
    rotation.

  This is finite qubit tomography.  It is not a detector model, continuum QFT,
  spin/statistics, or Standard Model parameter recovery.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable.BinaryBornPair

/-- Expectation value of a binary plus/minus Born probability pair. -/
noncomputable def expectation (P : BinaryBornPair) : Real :=
  P.plus - P.minus

theorem expectation_eq_two_plus_sub_one (P : BinaryBornPair) :
    P.expectation = 2 * P.plus - 1 := by
  unfold expectation
  nlinarith [P.total]

theorem expectation_eq_one_sub_two_minus (P : BinaryBornPair) :
    P.expectation = 1 - 2 * P.minus := by
  unfold expectation
  nlinarith [P.total]

end UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable.BinaryBornPair

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitBlochCoords

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

theorem bornX_expectation_eq_x (B : UnitBlochCoords) :
    B.bornX.expectation = B.x := by
  unfold BinaryBornPair.expectation bornX bornPlusX bornMinusX
  ring

theorem bornY_expectation_eq_y (B : UnitBlochCoords) :
    B.bornY.expectation = B.y := by
  unfold BinaryBornPair.expectation bornY bornPlusY bornMinusY
  ring

theorem bornZ_expectation_eq_z (B : UnitBlochCoords) :
    B.bornZ.expectation = B.z := by
  unfold BinaryBornPair.expectation bornZ bornPlusZ bornMinusZ
  ring

/-- Reconstruct a unit Bloch point from the expectations of its three Pauli
Born probability pairs. -/
noncomputable def reconstructFromPauliBorn
    (B : UnitBlochCoords) :
    UnitBlochCoords where
  x := B.bornX.expectation
  y := B.bornY.expectation
  z := B.bornZ.expectation
  unit := by
    rw [bornX_expectation_eq_x, bornY_expectation_eq_y, bornZ_expectation_eq_z]
    exact B.unit

theorem reconstructFromPauliBorn_eq
    (B : UnitBlochCoords) :
    B.reconstructFromPauliBorn = B := by
  apply UnitBlochCoords.ext_coords
  · exact bornX_expectation_eq_x B
  · exact bornY_expectation_eq_y B
  · exact bornZ_expectation_eq_z B

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitBlochCoords

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable.UnitBlochAxis

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

theorem bornAlong_expectation_eq_dot
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    (A.bornAlong B).expectation = A.dot B := by
  unfold BinaryBornPair.expectation bornAlong bornPlusAlong bornMinusAlong
  ring

theorem pauliX_expectation_eq_x (B : UnitBlochCoords) :
    (pauliX.bornAlong B).expectation = B.x := by
  rw [pauliX_bornAlong_eq_bornX]
  exact UnitBlochCoords.bornX_expectation_eq_x B

theorem pauliY_expectation_eq_y (B : UnitBlochCoords) :
    (pauliY.bornAlong B).expectation = B.y := by
  rw [pauliY_bornAlong_eq_bornY]
  exact UnitBlochCoords.bornY_expectation_eq_y B

theorem pauliZ_expectation_eq_z (B : UnitBlochCoords) :
    (pauliZ.bornAlong B).expectation = B.z := by
  rw [pauliZ_bornAlong_eq_bornZ]
  exact UnitBlochCoords.bornZ_expectation_eq_z B

end UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable.UnitBlochAxis

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

variable {site : Type*}

theorem bornXAt_expectation_eq_quotientBloch_x
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.bornXAt n x).expectation = (I.quotientBlochAt n x).x := by
  exact UnitBlochCoords.bornX_expectation_eq_x (I.quotientBlochAt n x)

theorem bornYAt_expectation_eq_quotientBloch_y
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.bornYAt n x).expectation = (I.quotientBlochAt n x).y := by
  exact UnitBlochCoords.bornY_expectation_eq_y (I.quotientBlochAt n x)

theorem bornZAt_expectation_eq_quotientBloch_z
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.bornZAt n x).expectation = (I.quotientBlochAt n x).z := by
  exact UnitBlochCoords.bornZ_expectation_eq_z (I.quotientBlochAt n x)

theorem bornAlongAt_expectation_eq_dot
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (I.bornAlongAt A n x).expectation =
      A.dot (I.quotientBlochAt n x) := by
  exact UnitBlochAxis.bornAlong_expectation_eq_dot A (I.quotientBlochAt n x)

/-- The Bloch point reconstructed from local Pauli Born expectations. -/
noncomputable def reconstructedBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnitBlochCoords where
  x := (I.bornXAt n x).expectation
  y := (I.bornYAt n x).expectation
  z := (I.bornZAt n x).expectation
  unit := by
    rw [
      bornXAt_expectation_eq_quotientBloch_x,
      bornYAt_expectation_eq_quotientBloch_y,
      bornZAt_expectation_eq_quotientBloch_z]
    exact (I.quotientBlochAt n x).unit

theorem reconstructedBlochAt_eq_quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.reconstructedBlochAt n x = I.quotientBlochAt n x := by
  apply UnitBlochCoords.ext_coords
  · exact bornXAt_expectation_eq_quotientBloch_x I n x
  · exact bornYAt_expectation_eq_quotientBloch_y I n x
  · exact bornZAt_expectation_eq_quotientBloch_z I n x

theorem phaseRotate_bornAlongAt_expectation_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    ((I.phaseRotate P).bornAlongAt A n x).expectation =
      (I.bornAlongAt A n x).expectation := by
  exact congrArg BinaryBornPair.expectation
    (phaseRotate_bornAlongAt_eq I P A n x)

theorem phaseRotate_reconstructedBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).reconstructedBlochAt n x =
      I.reconstructedBlochAt n x := by
  rw [
    reconstructedBlochAt_eq_quotientBlochAt,
    reconstructedBlochAt_eq_quotientBlochAt,
    phaseRotate_quotientBlochAt_eq]

/-- Bundled local tomography statement: three Pauli Born pairs reconstruct the
gauge-invariant local quotient Bloch observable. -/
theorem recoveredStage_local_pauli_born_tomography
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.reconstructedBlochAt n x = I.quotientBlochAt n x ∧
    ∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).reconstructedBlochAt n x =
        I.reconstructedBlochAt n x := by
  exact
    ⟨reconstructedBlochAt_eq_quotientBlochAt I n x,
      fun P => phaseRotate_reconstructedBlochAt_eq I P n x⟩

#print axioms BinaryBornPair.expectation_eq_two_plus_sub_one
#print axioms UnitBlochCoords.bornX_expectation_eq_x
#print axioms UnitBlochAxis.bornAlong_expectation_eq_dot
#print axioms RecoveredStageHopfFiberInterface.bornAlongAt_expectation_eq_dot
#print axioms RecoveredStageHopfFiberInterface.reconstructedBlochAt_eq_quotientBlochAt
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_reconstructedBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_pauli_born_tomography

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
