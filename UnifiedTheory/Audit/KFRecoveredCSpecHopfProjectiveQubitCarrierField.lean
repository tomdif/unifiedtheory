/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierField.lean

  Stagewise recovered projective qubit carrier fields.

  `KFRecoveredCSpecHopfProjectiveQubitCarrier` packages one recovered local
  projective qubit as a carrier.  This file lifts that object to an entire
  recovered stage: a carrier field is one projective qubit carrier at every
  site.

  Lean proves:

  * carrier fields are extensionally determined sitewise;
  * pointwise Pauli/all-axis Born data are equivalent to equality of carrier
    fields;
  * every recovered stage has a projective carrier field whose pointwise Bloch
    and Born projections agree with the existing local observables;
  * Pauli Born reconstruction and stagewise local `U(1)` gauge invariance lift
    from individual carriers to the whole carrier field.

  This is finite local projective-qubit kinematics.  It is not detector
  dynamics, continuum QFT, spin/statistics, Standard Model recovery, quotient
  topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier.ProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

/-- A finite recovered projective qubit carrier field over sites. -/
abbrev ProjectiveQubitCarrierField (site : Type u) : Type u :=
  site → ProjectiveQubitCarrier

namespace ProjectiveQubitCarrierField

theorem ext_site
    {site : Type*} {F G : ProjectiveQubitCarrierField site}
    (h : ∀ x : site, F x = G x) :
    F = G := by
  funext x
  exact h x

/-- Pointwise equality of Pauli-axis Born data for carrier fields. -/
def SamePauliBornData
    {site : Type*} (F G : ProjectiveQubitCarrierField site) : Prop :=
  ∀ x : site, ProjectiveQubitCarrier.SamePauliBornData (F x) (G x)

/-- Pointwise equality of all arbitrary-axis Born data for carrier fields. -/
def SameAllAxisBornData
    {site : Type*} (F G : ProjectiveQubitCarrierField site) : Prop :=
  ∀ x : site, ProjectiveQubitCarrier.SameAllAxisBornData (F x) (G x)

/-- Pointwise Pauli Born reconstruction of a carrier field. -/
noncomputable def reconstructed
    {site : Type*} (F : ProjectiveQubitCarrierField site) :
    ProjectiveQubitCarrierField site :=
  fun x => (F x).reconstructed

theorem reconstructed_eq
    {site : Type*} (F : ProjectiveQubitCarrierField site) :
    reconstructed F = F := by
  apply ext_site
  intro x
  exact ProjectiveQubitCarrier.reconstructed_eq (F x)

theorem samePauliBornData_iff_eq
    {site : Type*} (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornData F G ↔ F = G := by
  constructor
  · intro h
    apply ext_site
    intro x
    exact (ProjectiveQubitCarrier.samePauliBornData_iff_eq (F x) (G x)).mp
      (h x)
  · intro h
    subst h
    intro x
    exact (ProjectiveQubitCarrier.samePauliBornData_iff_eq (F x) (F x)).mpr
      rfl

theorem sameAllAxisBornData_iff_eq
    {site : Type*} (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornData F G ↔ F = G := by
  constructor
  · intro h
    apply ext_site
    intro x
    exact (ProjectiveQubitCarrier.sameAllAxisBornData_iff_eq (F x) (G x)).mp
      (h x)
  · intro h
    subst h
    intro x
    exact (ProjectiveQubitCarrier.sameAllAxisBornData_iff_eq (F x) (F x)).mpr
      rfl

/-- Bundled carrier-field interface theorem. -/
theorem projective_qubit_carrier_field_interface
    {site : Type*} (F G : ProjectiveQubitCarrierField site) :
    reconstructed F = F ∧
    (SamePauliBornData F G ↔ F = G) ∧
    (SameAllAxisBornData F G ↔ F = G) := by
  exact
    ⟨reconstructed_eq F,
      samePauliBornData_iff_eq F G,
      sameAllAxisBornData_iff_eq F G⟩

#print axioms ProjectiveQubitCarrierField.reconstructed_eq
#print axioms ProjectiveQubitCarrierField.samePauliBornData_iff_eq
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornData_iff_eq
#print axioms ProjectiveQubitCarrierField.projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier.ProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

variable {site : Type*}

/-- The recovered projective qubit carrier field at a whole stage. -/
noncomputable def projectiveCarrierFieldAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) :
    ProjectiveQubitCarrierField site :=
  fun x => I.projectiveCarrierAt n x

theorem projectiveCarrierFieldAt_apply
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.projectiveCarrierFieldAt n x = I.projectiveCarrierAt n x := by
  rfl

theorem projectiveCarrierFieldAt_bloch_eq_quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierFieldAt n x).bloch = I.quotientBlochAt n x := by
  exact projectiveCarrierAt_bloch_eq_quotientBlochAt I n x

theorem projectiveCarrierFieldAt_bornX_eq_bornXAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierFieldAt n x).bornX = I.bornXAt n x := by
  exact projectiveCarrierAt_bornX_eq_bornXAt I n x

theorem projectiveCarrierFieldAt_bornY_eq_bornYAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierFieldAt n x).bornY = I.bornYAt n x := by
  exact projectiveCarrierAt_bornY_eq_bornYAt I n x

theorem projectiveCarrierFieldAt_bornZ_eq_bornZAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierFieldAt n x).bornZ = I.bornZAt n x := by
  exact projectiveCarrierAt_bornZ_eq_bornZAt I n x

theorem projectiveCarrierFieldAt_bornAlong_eq_bornAlongAt
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (I.projectiveCarrierFieldAt n x).bornAlong A =
      I.bornAlongAt A n x := by
  exact projectiveCarrierAt_bornAlong_eq_bornAlongAt I A n x

/-- Pointwise equality of local Pauli-axis Born data across two carrier fields
over the same site type. -/
def SamePauliBornCarrierFieldData
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) : Prop :=
  ∀ x : site, SamePauliBornData I J n m x x

/-- Pointwise equality of all local arbitrary-axis Born data across two carrier
fields over the same site type. -/
def SameAllAxisBornCarrierFieldData
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) : Prop :=
  ∀ x : site, SameAllAxisBornData I J n m x x

theorem reconstructed_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed (I.projectiveCarrierFieldAt n) =
      I.projectiveCarrierFieldAt n := by
  exact ProjectiveQubitCarrierField.reconstructed_eq (I.projectiveCarrierFieldAt n)

theorem phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    (I.phaseRotate P).projectiveCarrierFieldAt n =
      I.projectiveCarrierFieldAt n := by
  apply ProjectiveQubitCarrierField.ext_site
  intro x
  exact phaseRotate_projectiveCarrierAt_eq I P n x

theorem samePauliBornCarrierFieldData_iff_projectiveCarrierFieldAt_eq
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) :
    SamePauliBornCarrierFieldData I J n m ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m := by
  constructor
  · intro h
    apply ProjectiveQubitCarrierField.ext_site
    intro x
    exact (samePauliBornData_iff_projectiveCarrierAt_eq I J n m x x).mp
      (h x)
  · intro h x
    exact (samePauliBornData_iff_projectiveCarrierAt_eq I J n m x x).mpr
      (congrFun h x)

theorem sameAllAxisBornCarrierFieldData_iff_projectiveCarrierFieldAt_eq
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) :
    SameAllAxisBornCarrierFieldData I J n m ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m := by
  constructor
  · intro h
    apply ProjectiveQubitCarrierField.ext_site
    intro x
    exact (sameAllAxisBornData_iff_projectiveCarrierAt_eq I J n m x x).mp
      (h x)
  · intro h x
    exact (sameAllAxisBornData_iff_projectiveCarrierAt_eq I J n m x x).mpr
      (congrFun h x)

theorem carrierFieldSamePauliBornData_iff_samePauliBornCarrierFieldData
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      SamePauliBornCarrierFieldData I J n m := by
  constructor
  · intro h x
    exact (carrierSamePauliBornData_iff_samePauliBornData I J n m x x).mp
      (h x)
  · intro h x
    exact (carrierSamePauliBornData_iff_samePauliBornData I J n m x x).mpr
      (h x)

theorem carrierFieldSameAllAxisBornData_iff_sameAllAxisBornCarrierFieldData
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      SameAllAxisBornCarrierFieldData I J n m := by
  constructor
  · intro h x
    exact (carrierSameAllAxisBornData_iff_sameAllAxisBornData I J n m x x).mp
      (h x)
  · intro h x
    exact (carrierSameAllAxisBornData_iff_sameAllAxisBornData I J n m x x).mpr
      (h x)

/-- Bundled recovered-stage projective carrier-field interface. -/
theorem recoveredStage_projective_qubit_carrier_field_interface
    (I J : RecoveredStageHopfFiberInterface site)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.reconstructed (I.projectiveCarrierFieldAt n) =
      I.projectiveCarrierFieldAt n ∧
    (SamePauliBornCarrierFieldData I J n m ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m) ∧
    (SameAllAxisBornCarrierFieldData I J n m ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m) ∧
    (ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      SamePauliBornCarrierFieldData I J n m) ∧
    (∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).projectiveCarrierFieldAt n =
        I.projectiveCarrierFieldAt n) := by
  exact
    ⟨reconstructed_projectiveCarrierFieldAt_eq I n,
      samePauliBornCarrierFieldData_iff_projectiveCarrierFieldAt_eq I J n m,
      sameAllAxisBornCarrierFieldData_iff_projectiveCarrierFieldAt_eq I J n m,
      carrierFieldSamePauliBornData_iff_samePauliBornCarrierFieldData I J n m,
      fun P => phaseRotate_projectiveCarrierFieldAt_eq I P n⟩

#print axioms ProjectiveQubitCarrierField.samePauliBornData_iff_eq
#print axioms RecoveredStageHopfFiberInterface.reconstructed_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.samePauliBornCarrierFieldData_iff_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.carrierFieldSamePauliBornData_iff_samePauliBornCarrierFieldData
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
