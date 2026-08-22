/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverRefinement.lean

  Reindex-refinement covariance for recovered projective qubit carrier-field
  covers.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCover` proves that a
  jointly-surjective family of probe maps separates global carrier-field
  equality and Born-data equality.  This file proves that the result is
  invariant under surjective reindexing of that cover: repeating or refining
  the cover index set does not change the observable equality tests.

  Lean proves:

  * joint surjectivity transfers from a cover to any surjective reindexing;
  * joint surjectivity reflects from any reindexed cover back to the original
    cover;
  * carrier-field equality on a cover is equivalent to carrier-field equality
    on any surjective reindexing of the cover;
  * Pauli/all-axis Born-data equality on a cover is equivalent to the same data
    equality on any surjective reindexing of the cover;
  * recovered-stage local `U(1)` gauge invisibility remains true on the
    reindexed cover.

  This is finite cover-refinement covariance for local projective-qubit
  kinematics.  It is not detector dynamics, continuum QFT, spin/statistics,
  Standard Model recovery, quotient topology, a sheaf over a topological site,
  or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCover

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w z

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

/-- Reindex a dependent family of probes along a map of cover indices. -/
def reindexProbe
    {cover : Type u} {cover' : Type v}
    (probe : cover → Type w)
    (r : cover' → cover) :
    cover' → Type w :=
  fun j => probe (r j)

/-- Reindex the probe-to-site maps along a map of cover indices. -/
def reindexMap
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover) :
    (j : cover') → reindexProbe probe r j → site :=
  fun j p => f (r j) p

theorem reindexProbe_apply
    {cover : Type u} {cover' : Type v}
    (probe : cover → Type w)
    (r : cover' → cover)
    (j : cover') :
    reindexProbe probe r j = probe (r j) := by
  rfl

theorem reindexMap_apply
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (j : cover') (p : reindexProbe probe r j) :
    reindexMap f r j p = f (r j) p := by
  rfl

theorem pullback_reindexMap
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (F : ProjectiveQubitCarrierField site)
    (j : cover') :
    pullback (reindexMap f r j) F = pullback (f (r j)) F := by
  rfl

theorem jointlySurjective_of_reindex
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    {r : cover' → cover}
    (h : JointlySurjective (reindexProbe probe r) (reindexMap f r)) :
    JointlySurjective probe f := by
  intro x
  rcases h x with ⟨j, p, hp⟩
  exact ⟨r j, p, hp⟩

theorem jointlySurjective_reindex_of_jointlySurjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (h : JointlySurjective probe f) :
    JointlySurjective (reindexProbe probe r) (reindexMap f r) := by
  intro x
  rcases h x with ⟨i, p, hp⟩
  rcases hr i with ⟨j, rfl⟩
  exact ⟨j, p, hp⟩

theorem jointlySurjective_reindex_iff_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    (r : cover' → cover)
    (hr : Function.Surjective r) :
    JointlySurjective (reindexProbe probe r) (reindexMap f r) ↔
      JointlySurjective probe f := by
  constructor
  · intro h
    exact jointlySurjective_of_reindex h
  · intro h
    exact jointlySurjective_reindex_of_jointlySurjective r hr h

theorem equalOnCover_reindex_of_equalOnCover
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    {F G : ProjectiveQubitCarrierField site}
    (h : EqualOnCover probe f F G) :
    EqualOnCover (reindexProbe probe r) (reindexMap f r) F G := by
  intro j
  exact h (r j)

theorem equalOnCover_of_equalOnCover_reindex_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    {r : cover' → cover}
    (hr : Function.Surjective r)
    {F G : ProjectiveQubitCarrierField site}
    (h : EqualOnCover (reindexProbe probe r) (reindexMap f r) F G) :
    EqualOnCover probe f F G := by
  intro i
  rcases hr i with ⟨j, rfl⟩
  exact h j

theorem equalOnCover_reindex_iff_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (F G : ProjectiveQubitCarrierField site) :
    EqualOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      EqualOnCover probe f F G := by
  constructor
  · intro h
    exact equalOnCover_of_equalOnCover_reindex_of_surjective hr h
  · intro h
    exact equalOnCover_reindex_of_equalOnCover f r h

theorem samePauliBornDataOnCover_reindex_of_samePauliBornDataOnCover
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornDataOnCover probe f F G) :
    SamePauliBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G := by
  intro j
  exact h (r j)

theorem samePauliBornDataOnCover_of_reindex_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    {r : cover' → cover}
    (hr : Function.Surjective r)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G) :
    SamePauliBornDataOnCover probe f F G := by
  intro i
  rcases hr i with ⟨j, rfl⟩
  exact h j

theorem samePauliBornDataOnCover_reindex_iff_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SamePauliBornDataOnCover probe f F G := by
  constructor
  · intro h
    exact samePauliBornDataOnCover_of_reindex_of_surjective hr h
  · intro h
    exact samePauliBornDataOnCover_reindex_of_samePauliBornDataOnCover f r h

theorem sameAllAxisBornDataOnCover_reindex_of_sameAllAxisBornDataOnCover
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornDataOnCover probe f F G) :
    SameAllAxisBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G := by
  intro j
  exact h (r j)

theorem sameAllAxisBornDataOnCover_of_reindex_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    {f : (i : cover) → probe i → site}
    {r : cover' → cover}
    (hr : Function.Surjective r)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G) :
    SameAllAxisBornDataOnCover probe f F G := by
  intro i
  rcases hr i with ⟨j, rfl⟩
  exact h j

theorem sameAllAxisBornDataOnCover_reindex_iff_of_surjective
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SameAllAxisBornDataOnCover probe f F G := by
  constructor
  · intro h
    exact sameAllAxisBornDataOnCover_of_reindex_of_surjective hr h
  · intro h
    exact sameAllAxisBornDataOnCover_reindex_of_sameAllAxisBornDataOnCover f r h

/-- Bundled reindex-refinement theorem for projective carrier-field covers. -/
theorem reindex_cover_projective_qubit_carrier_field_interface
    {cover : Type u} {cover' : Type v} {site : Type z}
    {probe : cover → Type w}
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (hcover : JointlySurjective probe f)
    (F G : ProjectiveQubitCarrierField site) :
    JointlySurjective (reindexProbe probe r) (reindexMap f r) ∧
    (EqualOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      EqualOnCover probe f F G) ∧
    (SamePauliBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SamePauliBornDataOnCover probe f F G) ∧
    (SameAllAxisBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SameAllAxisBornDataOnCover probe f F G) ∧
    (EqualOnCover (reindexProbe probe r) (reindexMap f r) F G ↔ F = G) ∧
    (SamePauliBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SamePauliBornData F G) ∧
    (SameAllAxisBornDataOnCover (reindexProbe probe r) (reindexMap f r) F G ↔
      SameAllAxisBornData F G) := by
  have hcover' :
      JointlySurjective (reindexProbe probe r) (reindexMap f r) :=
    jointlySurjective_reindex_of_jointlySurjective r hr hcover
  exact
    ⟨hcover',
      equalOnCover_reindex_iff_of_surjective f r hr F G,
      samePauliBornDataOnCover_reindex_iff_of_surjective f r hr F G,
      sameAllAxisBornDataOnCover_reindex_iff_of_surjective f r hr F G,
      equalOnCover_iff_eq_of_jointlySurjective
        (reindexProbe probe r) (reindexMap f r) hcover' F G,
      samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
        (reindexProbe probe r) (reindexMap f r) hcover' F G,
      sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
        (reindexProbe probe r) (reindexMap f r) hcover' F G⟩

#print axioms ProjectiveQubitCarrierField.jointlySurjective_reindex_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.equalOnCover_reindex_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.samePauliBornDataOnCover_reindex_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_reindex_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.reindex_cover_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v w z

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u} {cover : Type v} {cover' : Type w} {probe : cover → Type z}

theorem reindex_cover_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    ∀ j : cover',
      ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n) := by
  intro j
  exact pullback_phaseRotate_projectiveCarrierFieldAt_eq I
    (ProjectiveQubitCarrierField.reindexMap f r j) P n

theorem reindex_cover_projectiveCarrierFieldAt_eq_iff_of_surjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (n m : ℕ) :
    (∀ j : cover',
      ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m)) ↔
    (∀ i : cover,
      ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m)) := by
  exact ProjectiveQubitCarrierField.equalOnCover_reindex_iff_of_surjective
    f r hr (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem reindex_cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_surjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (n m : ℕ) :
    (∀ j : cover',
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m))) ↔
    (∀ i : cover,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) := by
  exact ProjectiveQubitCarrierField.samePauliBornDataOnCover_reindex_iff_of_surjective
    f r hr (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem reindex_cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_surjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (n m : ℕ) :
    (∀ j : cover',
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m))) ↔
    (∀ i : cover,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) := by
  exact ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_reindex_iff_of_surjective
    f r hr (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

/-- Bundled recovered-stage reindex-refinement theorem for projective carrier
field covers. -/
theorem recoveredStage_projective_qubit_carrier_field_cover_reindex_interface
    (I J : RecoveredStageHopfFiberInterface site)
    (f : (i : cover) → probe i → site)
    (r : cover' → cover)
    (hr : Function.Surjective r)
    (hcover : ProjectiveQubitCarrierField.JointlySurjective probe f)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.JointlySurjective
        (ProjectiveQubitCarrierField.reindexProbe probe r)
        (ProjectiveQubitCarrierField.reindexMap f r) ∧
    (∀ P : ℕ → UnitPhaseField site, ∀ j : cover',
      ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n)) ∧
    ((∀ j : cover',
      ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m)) ↔
      (∀ i : cover,
        ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n) =
          ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m))) ∧
    ((∀ j : cover',
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m))) ↔
      (∀ i : cover,
        ProjectiveQubitCarrierField.SamePauliBornData
          (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
          (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m)))) ∧
    ((∀ j : cover',
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.reindexMap f r j)
          (J.projectiveCarrierFieldAt m))) ↔
      (∀ i : cover,
        ProjectiveQubitCarrierField.SameAllAxisBornData
          (ProjectiveQubitCarrierField.pullback (f i) (I.projectiveCarrierFieldAt n))
          (ProjectiveQubitCarrierField.pullback (f i) (J.projectiveCarrierFieldAt m)))) := by
  exact
    ⟨ProjectiveQubitCarrierField.jointlySurjective_reindex_of_jointlySurjective
        r hr hcover,
      fun P => reindex_cover_phaseRotate_projectiveCarrierFieldAt_eq I f r P n,
      reindex_cover_projectiveCarrierFieldAt_eq_iff_of_surjective I J f r hr n m,
      reindex_cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_surjective
        I J f r hr n m,
      reindex_cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_surjective
        I J f r hr n m⟩

#print axioms RecoveredStageHopfFiberInterface.reindex_cover_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.reindex_cover_projectiveCarrierFieldAt_eq_iff_of_surjective
#print axioms RecoveredStageHopfFiberInterface.reindex_cover_projectiveCarrierFieldAt_samePauliBornData_iff_of_surjective
#print axioms RecoveredStageHopfFiberInterface.reindex_cover_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_surjective
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_cover_reindex_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
