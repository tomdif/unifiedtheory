/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrier.lean

  Recovered-stage projective qubit carriers.

  `KFRecoveredCSpecHopfProjectiveQubitState` identifies every recovered
  stage/site Hopf phase class with the finite `ProjectiveQubitState` API.  This
  file packages that state as a small carrier object whose Bloch point, Pauli
  Born pairs, arbitrary-axis Born pairs, and reconstructed state move together.

  Lean proves:

  * a projective qubit carrier is determined by its state;
  * Pauli/all-axis Born data are equivalent to carrier equality;
  * every recovered stage/site has a carrier whose fields agree with the
    existing local quotient Bloch and Born observables;
  * local Pauli Born reconstruction and local stagewise `U(1)` gauge invariance
    lift from projective states to carriers.

  This is finite local projective-qubit kinematics.  It is not detector
  dynamics, continuum QFT, spin/statistics, Standard Model recovery, quotient
  topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitState

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier

open UnifiedTheory.Audit.KFHopfProjectiveQubitState
open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

/-- A finite projective qubit carrier.  The state is primary; Bloch and Born
observables are derived projections. -/
structure ProjectiveQubitCarrier where
  state : ProjectiveQubitState

namespace ProjectiveQubitCarrier

@[ext] theorem ext_state {C D : ProjectiveQubitCarrier}
    (h : C.state = D.state) : C = D := by
  cases C with
  | mk c =>
    cases D with
    | mk d =>
      cases h
      rfl

theorem eq_iff_state_eq (C D : ProjectiveQubitCarrier) :
    C = D ↔ C.state = D.state := by
  constructor
  · intro h
    exact congrArg ProjectiveQubitCarrier.state h
  · exact ext_state

/-- Carrier Bloch point. -/
noncomputable def bloch (C : ProjectiveQubitCarrier) : UnitBlochCoords :=
  C.state.bloch

/-- Carrier Pauli-X Born pair. -/
noncomputable def bornX (C : ProjectiveQubitCarrier) : BinaryBornPair :=
  C.state.bornX

/-- Carrier Pauli-Y Born pair. -/
noncomputable def bornY (C : ProjectiveQubitCarrier) : BinaryBornPair :=
  C.state.bornY

/-- Carrier Pauli-Z Born pair. -/
noncomputable def bornZ (C : ProjectiveQubitCarrier) : BinaryBornPair :=
  C.state.bornZ

/-- Carrier arbitrary-axis Born pair. -/
noncomputable def bornAlong
    (C : ProjectiveQubitCarrier) (A : UnitBlochAxis) : BinaryBornPair :=
  C.state.bornAlong A

/-- Equality of carrier Pauli-axis Born probability pairs. -/
def SamePauliBornData (C D : ProjectiveQubitCarrier) : Prop :=
  C.bornX = D.bornX ∧
  C.bornY = D.bornY ∧
  C.bornZ = D.bornZ

/-- Equality of all carrier arbitrary-axis Born probability pairs. -/
def SameAllAxisBornData (C D : ProjectiveQubitCarrier) : Prop :=
  ∀ A : UnitBlochAxis, C.bornAlong A = D.bornAlong A

theorem bornX_expectation_eq_bloch_x (C : ProjectiveQubitCarrier) :
    C.bornX.expectation = C.bloch.x := by
  exact ProjectiveQubitState.bornX_expectation_eq_bloch_x C.state

theorem bornY_expectation_eq_bloch_y (C : ProjectiveQubitCarrier) :
    C.bornY.expectation = C.bloch.y := by
  exact ProjectiveQubitState.bornY_expectation_eq_bloch_y C.state

theorem bornZ_expectation_eq_bloch_z (C : ProjectiveQubitCarrier) :
    C.bornZ.expectation = C.bloch.z := by
  exact ProjectiveQubitState.bornZ_expectation_eq_bloch_z C.state

theorem bornAlong_expectation_eq_dot
    (C : ProjectiveQubitCarrier) (A : UnitBlochAxis) :
    (C.bornAlong A).expectation = A.dot C.bloch := by
  exact ProjectiveQubitState.bornAlong_expectation_eq_dot C.state A

/-- Reconstruct the carrier from its Pauli Born expectations. -/
noncomputable def reconstructed (C : ProjectiveQubitCarrier) :
    ProjectiveQubitCarrier where
  state := C.state.reconstructedState

theorem reconstructed_eq (C : ProjectiveQubitCarrier) :
    C.reconstructed = C := by
  apply ext_state
  exact ProjectiveQubitState.reconstructedState_eq C.state

theorem samePauliBornData_iff_state_eq
    (C D : ProjectiveQubitCarrier) :
    SamePauliBornData C D ↔ C.state = D.state := by
  simpa [SamePauliBornData, bornX, bornY, bornZ] using
    ProjectiveQubitState.samePauliBornData_iff_eq C.state D.state

theorem sameAllAxisBornData_iff_state_eq
    (C D : ProjectiveQubitCarrier) :
    SameAllAxisBornData C D ↔ C.state = D.state := by
  simpa [SameAllAxisBornData, bornAlong] using
    ProjectiveQubitState.sameAllAxisBornData_iff_eq C.state D.state

theorem samePauliBornData_iff_eq
    (C D : ProjectiveQubitCarrier) :
    SamePauliBornData C D ↔ C = D := by
  calc
    SamePauliBornData C D ↔ C.state = D.state :=
      samePauliBornData_iff_state_eq C D
    _ ↔ C = D :=
      (eq_iff_state_eq C D).symm

theorem sameAllAxisBornData_iff_eq
    (C D : ProjectiveQubitCarrier) :
    SameAllAxisBornData C D ↔ C = D := by
  calc
    SameAllAxisBornData C D ↔ C.state = D.state :=
      sameAllAxisBornData_iff_state_eq C D
    _ ↔ C = D :=
      (eq_iff_state_eq C D).symm

/-- Bundled carrier interface theorem. -/
theorem projective_qubit_carrier_interface
    (C D : ProjectiveQubitCarrier) :
    C.reconstructed = C ∧
    (SamePauliBornData C D ↔ C = D) ∧
    (SameAllAxisBornData C D ↔ C = D) ∧
    (C.bloch = D.bloch ↔ C = D) := by
  exact
    ⟨reconstructed_eq C,
      samePauliBornData_iff_eq C D,
      sameAllAxisBornData_iff_eq C D,
      by
        constructor
        · intro hB
          apply ext_state
          exact (ProjectiveQubitState.eq_iff_bloch_eq C.state D.state).mpr hB
        · intro h
          exact congrArg ProjectiveQubitCarrier.bloch h⟩

#print axioms ProjectiveQubitCarrier.reconstructed_eq
#print axioms ProjectiveQubitCarrier.samePauliBornData_iff_eq
#print axioms ProjectiveQubitCarrier.sameAllAxisBornData_iff_eq
#print axioms ProjectiveQubitCarrier.projective_qubit_carrier_interface

end ProjectiveQubitCarrier

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier.ProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

variable {site site' : Type*}

/-- The recovered projective qubit carrier at one stage/site. -/
noncomputable def projectiveCarrierAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    ProjectiveQubitCarrier where
  state := I.projectiveStateAt n x

theorem projectiveCarrierAt_state_eq_projectiveStateAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).state = I.projectiveStateAt n x := by
  rfl

theorem projectiveCarrierAt_bloch_eq_quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).bloch = I.quotientBlochAt n x := by
  exact projectiveStateAt_bloch_eq_quotientBlochAt I n x

theorem projectiveCarrierAt_bornX_eq_bornXAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).bornX = I.bornXAt n x := by
  exact projectiveStateAt_bornX_eq_bornXAt I n x

theorem projectiveCarrierAt_bornY_eq_bornYAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).bornY = I.bornYAt n x := by
  exact projectiveStateAt_bornY_eq_bornYAt I n x

theorem projectiveCarrierAt_bornZ_eq_bornZAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).bornZ = I.bornZAt n x := by
  exact projectiveStateAt_bornZ_eq_bornZAt I n x

theorem projectiveCarrierAt_bornAlong_eq_bornAlongAt
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).bornAlong A = I.bornAlongAt A n x := by
  exact projectiveStateAt_bornAlong_eq_bornAlongAt I A n x

theorem reconstructed_projectiveCarrierAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierAt n x).reconstructed = I.projectiveCarrierAt n x := by
  exact ProjectiveQubitCarrier.reconstructed_eq (I.projectiveCarrierAt n x)

theorem phaseRotate_projectiveCarrierAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).projectiveCarrierAt n x = I.projectiveCarrierAt n x := by
  apply ProjectiveQubitCarrier.ext_state
  exact phaseRotate_projectiveStateAt_eq I P n x

theorem projectiveCarrierAt_eq_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.projectiveCarrierAt n x = J.projectiveCarrierAt m y ↔
      SamePauliBornData I J n m x y := by
  calc
    I.projectiveCarrierAt n x = J.projectiveCarrierAt m y ↔
        I.projectiveStateAt n x = J.projectiveStateAt m y := by
      constructor
      · intro h
        exact congrArg ProjectiveQubitCarrier.state h
      · intro h
        exact ProjectiveQubitCarrier.ext_state h
    _ ↔ SamePauliBornData I J n m x y :=
      projectiveStateAt_eq_iff_samePauliBornData I J n m x y

theorem samePauliBornData_iff_projectiveCarrierAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SamePauliBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y := by
  exact (projectiveCarrierAt_eq_iff_samePauliBornData I J n m x y).symm

theorem projectiveCarrierAt_eq_iff_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.projectiveCarrierAt n x = J.projectiveCarrierAt m y ↔
      SameAllAxisBornData I J n m x y := by
  calc
    I.projectiveCarrierAt n x = J.projectiveCarrierAt m y ↔
        I.projectiveStateAt n x = J.projectiveStateAt m y := by
      constructor
      · intro h
        exact congrArg ProjectiveQubitCarrier.state h
      · intro h
        exact ProjectiveQubitCarrier.ext_state h
    _ ↔ SameAllAxisBornData I J n m x y :=
      projectiveStateAt_eq_iff_sameAllAxisBornData I J n m x y

theorem sameAllAxisBornData_iff_projectiveCarrierAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SameAllAxisBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y := by
  exact (projectiveCarrierAt_eq_iff_sameAllAxisBornData I J n m x y).symm

theorem carrierSamePauliBornData_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    ProjectiveQubitCarrier.SamePauliBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
      SamePauliBornData I J n m x y := by
  calc
    ProjectiveQubitCarrier.SamePauliBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
        I.projectiveCarrierAt n x = J.projectiveCarrierAt m y :=
      ProjectiveQubitCarrier.samePauliBornData_iff_eq
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y)
    _ ↔ SamePauliBornData I J n m x y :=
      projectiveCarrierAt_eq_iff_samePauliBornData I J n m x y

theorem carrierSameAllAxisBornData_iff_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    ProjectiveQubitCarrier.SameAllAxisBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
      SameAllAxisBornData I J n m x y := by
  calc
    ProjectiveQubitCarrier.SameAllAxisBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
        I.projectiveCarrierAt n x = J.projectiveCarrierAt m y :=
      ProjectiveQubitCarrier.sameAllAxisBornData_iff_eq
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y)
    _ ↔ SameAllAxisBornData I J n m x y :=
      projectiveCarrierAt_eq_iff_sameAllAxisBornData I J n m x y

/-- Bundled recovered-stage projective qubit carrier interface. -/
theorem recoveredStage_projective_qubit_carrier_interface
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    (I.projectiveCarrierAt n x).reconstructed = I.projectiveCarrierAt n x ∧
    (SamePauliBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y) ∧
    (SameAllAxisBornData I J n m x y ↔
      I.projectiveCarrierAt n x = J.projectiveCarrierAt m y) ∧
    (ProjectiveQubitCarrier.SamePauliBornData
        (I.projectiveCarrierAt n x) (J.projectiveCarrierAt m y) ↔
      SamePauliBornData I J n m x y) ∧
    (∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).projectiveCarrierAt n x = I.projectiveCarrierAt n x) := by
  exact
    ⟨reconstructed_projectiveCarrierAt_eq I n x,
      samePauliBornData_iff_projectiveCarrierAt_eq I J n m x y,
      sameAllAxisBornData_iff_projectiveCarrierAt_eq I J n m x y,
      carrierSamePauliBornData_iff_samePauliBornData I J n m x y,
      fun P => phaseRotate_projectiveCarrierAt_eq I P n x⟩

#print axioms RecoveredStageHopfFiberInterface.projectiveCarrierAt_bloch_eq_quotientBlochAt
#print axioms RecoveredStageHopfFiberInterface.reconstructed_projectiveCarrierAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_projectiveCarrierAt_eq
#print axioms RecoveredStageHopfFiberInterface.samePauliBornData_iff_projectiveCarrierAt_eq
#print axioms RecoveredStageHopfFiberInterface.carrierSamePauliBornData_iff_samePauliBornData
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
