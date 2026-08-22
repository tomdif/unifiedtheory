/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitState.lean

  Recovered-stage local projective qubit states.

  `KFHopfProjectiveQubitState` packages normalized Hopf phase classes as a
  finite projective-qubit state API.  The recovered-stage Hopf/Born stack
  already constructs a normalized phase class, a quotient Bloch observable, and
  Pauli/all-axis Born data at every stage/site.  This file identifies those two
  surfaces:

  * every recovered stage/site carries a `ProjectiveQubitState`;
  * its state-level Bloch and Born observables are exactly the existing local
    quotient Bloch and Born observables;
  * local Pauli Born expectations reconstruct that projective state;
  * local stagewise `U(1)` gauge rotations leave the projective state unchanged;
  * local Born observational completeness is restated as equality of recovered
    projective qubit states.

  This is still finite local projective-qubit kinematics.  It is not detector
  dynamics, continuum QFT, spin/statistics, Standard Model recovery, quotient
  topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfProjectiveQubitState
import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornPhaseClassReconstruction

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfProjectiveQubitState
open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

variable {site site' : Type*}

/-- The recovered projective qubit state at one stage/site. -/
noncomputable def projectiveStateAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    ProjectiveQubitState :=
  I.phaseClassAt n x

theorem projectiveStateAt_eq_phaseClassAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.projectiveStateAt n x = I.phaseClassAt n x := by
  rfl

/-- The state-level Bloch point is exactly the recovered quotient Bloch
observable. -/
theorem projectiveStateAt_bloch_eq_quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveStateAt n x).bloch = I.quotientBlochAt n x := by
  rfl

theorem projectiveStateAt_bornX_eq_bornXAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveStateAt n x).bornX = I.bornXAt n x := by
  rfl

theorem projectiveStateAt_bornY_eq_bornYAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveStateAt n x).bornY = I.bornYAt n x := by
  rfl

theorem projectiveStateAt_bornZ_eq_bornZAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveStateAt n x).bornZ = I.bornZAt n x := by
  rfl

theorem projectiveStateAt_bornAlong_eq_bornAlongAt
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (I.projectiveStateAt n x).bornAlong A = I.bornAlongAt A n x := by
  rfl

/-- The recovered projective qubit state reconstructed from local Pauli Born
expectations. -/
noncomputable def reconstructedProjectiveStateAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    ProjectiveQubitState :=
  ProjectiveQubitState.ofBloch (I.reconstructedBlochAt n x)

/-- Local Pauli Born expectations reconstruct the recovered projective qubit
state. -/
theorem reconstructedProjectiveStateAt_eq_projectiveStateAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.reconstructedProjectiveStateAt n x = I.projectiveStateAt n x := by
  simpa [
    reconstructedProjectiveStateAt,
    projectiveStateAt,
    reconstructedPhaseClassAt,
    ProjectiveQubitState.ofBloch
  ] using reconstructedPhaseClassAt_eq_phaseClassAt I n x

/-- Local stagewise `U(1)` gauge rotation leaves the recovered projective qubit
state unchanged. -/
theorem phaseRotate_projectiveStateAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).projectiveStateAt n x = I.projectiveStateAt n x := by
  simpa [projectiveStateAt] using phaseRotate_phaseClassAt_eq I P n x

theorem phaseRotate_reconstructedProjectiveStateAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).reconstructedProjectiveStateAt n x =
      I.reconstructedProjectiveStateAt n x := by
  rw [
    reconstructedProjectiveStateAt_eq_projectiveStateAt,
    reconstructedProjectiveStateAt_eq_projectiveStateAt,
    phaseRotate_projectiveStateAt_eq]

theorem samePauliBornData_iff_projectiveStateAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SamePauliBornData I J n m x y ↔
      I.projectiveStateAt n x = J.projectiveStateAt m y := by
  simpa [projectiveStateAt] using
    samePauliBornData_iff_phaseClassAt_eq I J n m x y

theorem sameAllAxisBornData_iff_projectiveStateAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    SameAllAxisBornData I J n m x y ↔
      I.projectiveStateAt n x = J.projectiveStateAt m y := by
  simpa [projectiveStateAt] using
    sameAllAxisBornData_iff_phaseClassAt_eq I J n m x y

theorem projectiveStateAt_eq_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.projectiveStateAt n x = J.projectiveStateAt m y ↔
      SamePauliBornData I J n m x y := by
  exact (samePauliBornData_iff_projectiveStateAt_eq I J n m x y).symm

theorem projectiveStateAt_eq_iff_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.projectiveStateAt n x = J.projectiveStateAt m y ↔
      SameAllAxisBornData I J n m x y := by
  exact (sameAllAxisBornData_iff_projectiveStateAt_eq I J n m x y).symm

theorem projectiveSamePauliBornData_iff_samePauliBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    ProjectiveQubitState.SamePauliBornData
        (I.projectiveStateAt n x) (J.projectiveStateAt m y) ↔
      SamePauliBornData I J n m x y := by
  calc
    ProjectiveQubitState.SamePauliBornData
        (I.projectiveStateAt n x) (J.projectiveStateAt m y) ↔
        I.projectiveStateAt n x = J.projectiveStateAt m y :=
      ProjectiveQubitState.samePauliBornData_iff_eq
        (I.projectiveStateAt n x) (J.projectiveStateAt m y)
    _ ↔ SamePauliBornData I J n m x y :=
      projectiveStateAt_eq_iff_samePauliBornData I J n m x y

theorem projectiveSameAllAxisBornData_iff_sameAllAxisBornData
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    ProjectiveQubitState.SameAllAxisBornData
        (I.projectiveStateAt n x) (J.projectiveStateAt m y) ↔
      SameAllAxisBornData I J n m x y := by
  calc
    ProjectiveQubitState.SameAllAxisBornData
        (I.projectiveStateAt n x) (J.projectiveStateAt m y) ↔
        I.projectiveStateAt n x = J.projectiveStateAt m y :=
      ProjectiveQubitState.sameAllAxisBornData_iff_eq
        (I.projectiveStateAt n x) (J.projectiveStateAt m y)
    _ ↔ SameAllAxisBornData I J n m x y :=
      projectiveStateAt_eq_iff_sameAllAxisBornData I J n m x y

/-- Bundled recovered-stage projective qubit state interface. -/
theorem recoveredStage_projective_qubit_state_interface
    (I : RecoveredStageHopfFiberInterface site)
    (J : RecoveredStageHopfFiberInterface site')
    (n m : ℕ) (x : site) (y : site') :
    I.reconstructedProjectiveStateAt n x = I.projectiveStateAt n x ∧
    (SamePauliBornData I J n m x y ↔
      I.projectiveStateAt n x = J.projectiveStateAt m y) ∧
    (SameAllAxisBornData I J n m x y ↔
      I.projectiveStateAt n x = J.projectiveStateAt m y) ∧
    (ProjectiveQubitState.SamePauliBornData
        (I.projectiveStateAt n x) (J.projectiveStateAt m y) ↔
      SamePauliBornData I J n m x y) ∧
    (∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).projectiveStateAt n x = I.projectiveStateAt n x) := by
  exact
    ⟨reconstructedProjectiveStateAt_eq_projectiveStateAt I n x,
      samePauliBornData_iff_projectiveStateAt_eq I J n m x y,
      sameAllAxisBornData_iff_projectiveStateAt_eq I J n m x y,
      projectiveSamePauliBornData_iff_samePauliBornData I J n m x y,
      fun P => phaseRotate_projectiveStateAt_eq I P n x⟩

#print axioms RecoveredStageHopfFiberInterface.projectiveStateAt_bloch_eq_quotientBlochAt
#print axioms RecoveredStageHopfFiberInterface.reconstructedProjectiveStateAt_eq_projectiveStateAt
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_projectiveStateAt_eq
#print axioms RecoveredStageHopfFiberInterface.samePauliBornData_iff_projectiveStateAt_eq
#print axioms RecoveredStageHopfFiberInterface.projectiveSamePauliBornData_iff_samePauliBornData
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_state_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
