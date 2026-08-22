/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCover.lean

  Cover/descent covariance for recovered projective qubit carrier fields.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRestriction` proves that a
  carrier field can be pulled back along any single probe map.  This file adds
  the cover-level consequence: if a family of probes jointly hits every site,
  then equality or Born-data equality on all probe pullbacks reflects equality
  or Born-data equality of the original carrier fields.

  Lean proves:

  * carrier-field equality on a jointly-surjective probe cover is equivalent to
    global carrier-field equality;
  * Pauli/all-axis Born-data equality on a jointly-surjective probe cover is
    equivalent to global Pauli/all-axis Born-data equality;
  * reconstruction commutes with every probe in the cover;
  * recovered-stage local `U(1)` gauge invisibility remains true on every probe
    in the cover.

  This is finite cover/descent covariance for local projective-qubit
  kinematics.  It is not detector dynamics, continuum QFT, spin/statistics,
  Standard Model recovery, quotient topology, a sheaf over a topological site,
  or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRestriction

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

/-- A dependent family of probe maps covers the site type when every site is hit
by at least one probe point. -/
def JointlySurjective
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site) : Prop :=
  ∀ x : site, ∃ i : cover, ∃ p : probe i, f i p = x

/-- Carrier-field equality after pulling back to every probe in a cover. -/
def EqualOnCover
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (F G : ProjectiveQubitCarrierField site) : Prop :=
  ∀ i : cover, pullback (f i) F = pullback (f i) G

/-- Pauli Born-data equality after pulling back to every probe in a cover. -/
def SamePauliBornDataOnCover
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (F G : ProjectiveQubitCarrierField site) : Prop :=
  ∀ i : cover, SamePauliBornData (pullback (f i) F) (pullback (f i) G)

/-- All-axis Born-data equality after pulling back to every probe in a cover. -/
def SameAllAxisBornDataOnCover
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (F G : ProjectiveQubitCarrierField site) : Prop :=
  ∀ i : cover, SameAllAxisBornData (pullback (f i) F) (pullback (f i) G)

theorem reconstructed_pullback_on_cover
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (F : ProjectiveQubitCarrierField site) :
    ∀ i : cover,
      reconstructed (pullback (f i) F) =
        pullback (f i) (reconstructed F) := by
  intro i
  exact reconstructed_pullback (f i) F

theorem equalOnCover_of_eq
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : F = G) :
    EqualOnCover probe f F G := by
  intro i
  exact pullback_eq_of_eq (f i) h

theorem eq_of_equalOnCover_of_jointlySurjective
    {cover : Type u} {site : Type v}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    (hcover : JointlySurjective probe f)
    {F G : ProjectiveQubitCarrierField site}
    (h : EqualOnCover probe f F G) :
    F = G := by
  apply ext_site
  intro x
  rcases hcover x with ⟨i, p, hp⟩
  have hi := congrFun (h i) p
  simpa [pullback, hp] using hi

theorem equalOnCover_iff_eq_of_jointlySurjective
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (hcover : JointlySurjective probe f)
    (F G : ProjectiveQubitCarrierField site) :
    EqualOnCover probe f F G ↔ F = G := by
  constructor
  · intro h
    exact eq_of_equalOnCover_of_jointlySurjective hcover h
  · intro h
    exact equalOnCover_of_eq probe f h

theorem samePauliBornDataOnCover_of_samePauliBornData
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornData F G) :
    SamePauliBornDataOnCover probe f F G := by
  intro i
  exact samePauliBornData_pullback (f i) h

theorem samePauliBornData_of_samePauliBornDataOnCover_of_jointlySurjective
    {cover : Type u} {site : Type v}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    (hcover : JointlySurjective probe f)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornDataOnCover probe f F G) :
    SamePauliBornData F G := by
  intro x
  rcases hcover x with ⟨i, p, hp⟩
  have hi := h i p
  simpa [pullback, hp] using hi

theorem samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (hcover : JointlySurjective probe f)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornDataOnCover probe f F G ↔ SamePauliBornData F G := by
  constructor
  · intro h
    exact samePauliBornData_of_samePauliBornDataOnCover_of_jointlySurjective
      hcover h
  · intro h
    exact samePauliBornDataOnCover_of_samePauliBornData probe f h

theorem sameAllAxisBornDataOnCover_of_sameAllAxisBornData
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornData F G) :
    SameAllAxisBornDataOnCover probe f F G := by
  intro i
  exact sameAllAxisBornData_pullback (f i) h

theorem sameAllAxisBornData_of_sameAllAxisBornDataOnCover_of_jointlySurjective
    {cover : Type u} {site : Type v}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    (hcover : JointlySurjective probe f)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornDataOnCover probe f F G) :
    SameAllAxisBornData F G := by
  intro x
  rcases hcover x with ⟨i, p, hp⟩
  have hi := h i p
  simpa [pullback, hp] using hi

theorem sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (hcover : JointlySurjective probe f)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornDataOnCover probe f F G ↔ SameAllAxisBornData F G := by
  constructor
  · intro h
    exact sameAllAxisBornData_of_sameAllAxisBornDataOnCover_of_jointlySurjective
      hcover h
  · intro h
    exact sameAllAxisBornDataOnCover_of_sameAllAxisBornData probe f h

/-- Bundled carrier-field cover/descent theorem for jointly-surjective probes. -/
theorem cover_projective_qubit_carrier_field_interface
    {cover : Type u} {site : Type v}
    (probe : cover → Type w)
    (f : (i : cover) → probe i → site)
    (hcover : JointlySurjective probe f)
    (F G : ProjectiveQubitCarrierField site) :
    (∀ i : cover, reconstructed (pullback (f i) F) = pullback (f i) F) ∧
    (EqualOnCover probe f F G ↔ F = G) ∧
    (SamePauliBornDataOnCover probe f F G ↔ SamePauliBornData F G) ∧
    (SameAllAxisBornDataOnCover probe f F G ↔ SameAllAxisBornData F G) ∧
    (∀ i : cover,
      reconstructed (pullback (f i) F) =
        pullback (f i) (reconstructed F)) := by
  exact
    ⟨fun i => reconstructed_eq (pullback (f i) F),
      equalOnCover_iff_eq_of_jointlySurjective probe f hcover F G,
      samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
        probe f hcover F G,
      sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
        probe f hcover F G,
      reconstructed_pullback_on_cover probe f F⟩

#print axioms ProjectiveQubitCarrierField.equalOnCover_iff_eq_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.cover_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v w

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u} {cover : Type v} {probe : cover → Type w}

theorem cover_projectiveCarrierFieldAt_reconstructed_eq
    (I : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (n : ℕ) :
    ∀ i : cover,
      ProjectiveQubitCarrierField.reconstructed
          (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n)) =
        ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) := by
  intro i
  exact pullback_projectiveCarrierFieldAt_reconstructed_eq I (f i) n

theorem cover_projectiveCarrierFieldAt_reconstructed_commute
    (I : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (n : ℕ) :
    ∀ i : cover,
      ProjectiveQubitCarrierField.reconstructed
          (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n)) =
        ProjectiveQubitCarrierField.pullback (f i)
          (ProjectiveQubitCarrierField.reconstructed (I.projectiveCarrierFieldAt n)) := by
  intro i
  exact pullback_projectiveCarrierFieldAt_reconstructed_commute I (f i) n

/-- Local stagewise `U(1)` gauge invisibility remains true on every probe in a
cover. -/
theorem cover_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    ∀ i : cover,
      ProjectiveQubitCarrierField.pullback (f i)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) := by
  intro i
  exact pullback_phaseRotate_projectiveCarrierFieldAt_eq I (f i) P n

theorem cover_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (hcover : ProjectiveQubitCarrierField.JointlySurjective probe f)
    (n m : ℕ) :
    (∀ i : cover,
      ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m)) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m := by
  exact ProjectiveQubitCarrierField.equalOnCover_iff_eq_of_jointlySurjective
    probe f hcover (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (hcover : ProjectiveQubitCarrierField.JointlySurjective probe f)
    (n m : ℕ) :
    (∀ i : cover,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) ↔
      ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) := by
  exact
    ProjectiveQubitCarrierField.samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
      probe f hcover (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (hcover : ProjectiveQubitCarrierField.JointlySurjective probe f)
    (n m : ℕ) :
    (∀ i : cover,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) ↔
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) := by
  exact
    ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
      probe f hcover (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

/-- Bundled recovered-stage cover/descent theorem for projective carrier
fields. -/
theorem recoveredStage_projective_qubit_carrier_field_cover_interface
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (hcover : ProjectiveQubitCarrierField.JointlySurjective probe f)
    (n m : ℕ) :
    (∀ i : cover,
      ProjectiveQubitCarrierField.reconstructed
          (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n)) =
        ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n)) ∧
    (∀ P : ℕ → UnitPhaseField site, ∀ i : cover,
      ProjectiveQubitCarrierField.pullback (f i)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n)) ∧
    ((∀ i : cover,
      ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m)) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m) ∧
    ((∀ i : cover,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) ↔
      ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)) ∧
    ((∀ i : cover,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) ↔
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)) := by
  exact
    ⟨cover_projectiveCarrierFieldAt_reconstructed_eq I f n,
      fun P => cover_phaseRotate_projectiveCarrierFieldAt_eq I f P n,
      cover_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective I J f hcover n m,
      cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
        I J f hcover n m,
      cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
        I J f hcover n m⟩

#print axioms RecoveredStageHopfFiberInterface.cover_projectiveCarrierFieldAt_reconstructed_eq
#print axioms RecoveredStageHopfFiberInterface.cover_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.cover_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_cover_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
