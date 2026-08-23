/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCommonRefinement.lean

  Common-refinement covariance for recovered projective qubit carrier-field
  covers.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCover` proves that a
  jointly-surjective family of probes separates global carrier-field equality
  and Born-data equality.  `...CoverRefinement` proves invariance under
  surjective reindexing.  This file adds the next finite descent operation: two
  jointly-surjective probe covers have a fiber-product common refinement over
  the same site set, and that common refinement again separates global
  carrier-field equality and Born-data equality.

  Lean proves:

  * the fiber product of two jointly-surjective probe covers is
    jointly-surjective;
  * carrier-field equality on that common refinement is equivalent to global
    carrier-field equality;
  * Pauli/all-axis Born-data equality on that common refinement is equivalent
    to global Pauli/all-axis Born-data equality;
  * recovered-stage local `U(1)` gauge invisibility remains true on every probe
    of the common refinement.

  This is finite common-refinement covariance for local projective-qubit
  kinematics.  It is not detector dynamics, continuum QFT, spin/statistics,
  Standard Model recovery, quotient topology, a sheaf over a topological site,
  or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverRefinement

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w z t

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

/-- The index set of the common refinement of two probe covers. -/
abbrev CommonRefinementIndex (coverA : Type u) (coverB : Type v) :
    Type (max u v) :=
  coverA × coverB

/-- The fiber-product probe over a pair of cover indices. -/
def commonRefinementProbe
    {coverA : Type u} {coverB : Type v} {site : Type w}
    (probeA : coverA → Type z)
    (probeB : coverB → Type t)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site) :
    CommonRefinementIndex coverA coverB → Type (max z t) :=
  fun ij =>
    { pq : probeA ij.1 × probeB ij.2 // fA ij.1 pq.1 = fB ij.2 pq.2 }

/-- The common-refinement probe map, using the left representative. -/
def commonRefinementMap
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site) :
    (ij : CommonRefinementIndex coverA coverB) →
      commonRefinementProbe probeA probeB fA fB ij → site :=
  fun ij pq => fA ij.1 pq.val.1

theorem commonRefinementMap_eq_left
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (ij : CommonRefinementIndex coverA coverB)
    (pq : commonRefinementProbe probeA probeB fA fB ij) :
    commonRefinementMap fA fB ij pq = fA ij.1 pq.val.1 := by
  rfl

theorem commonRefinementMap_eq_right
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (ij : CommonRefinementIndex coverA coverB)
    (pq : commonRefinementProbe probeA probeB fA fB ij) :
    commonRefinementMap fA fB ij pq = fB ij.2 pq.val.2 := by
  exact pq.property

theorem commonRefinement_pullback_apply_left
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F : ProjectiveQubitCarrierField site)
    (ij : CommonRefinementIndex coverA coverB)
    (pq : commonRefinementProbe probeA probeB fA fB ij) :
    pullback (commonRefinementMap fA fB ij) F pq =
      F (fA ij.1 pq.val.1) := by
  rfl

theorem commonRefinement_pullback_apply_right
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (F : ProjectiveQubitCarrierField site)
    (ij : CommonRefinementIndex coverA coverB)
    (pq : commonRefinementProbe probeA probeB fA fB ij) :
    pullback (commonRefinementMap fA fB ij) F pq =
      F (fB ij.2 pq.val.2) := by
  exact congrArg F pq.property

theorem jointlySurjective_commonRefinement
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    {fA : (i : coverA) → probeA i → site}
    {fB : (j : coverB) → probeB j → site}
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB) :
    JointlySurjective
      (commonRefinementProbe probeA probeB fA fB)
      (commonRefinementMap fA fB) := by
  intro x
  rcases hA x with ⟨i, p, hp⟩
  rcases hB x with ⟨j, q, hq⟩
  exact ⟨(i, j), ⟨(p, q), hp.trans hq.symm⟩, hp⟩

theorem equalOnCommonRefinement_iff_eq_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔
      F = G := by
  exact equalOnCover_iff_eq_of_jointlySurjective
    (commonRefinementProbe probeA probeB fA fB)
    (commonRefinementMap fA fB)
    (jointlySurjective_commonRefinement hA hB) F G

theorem samePauliBornDataOnCommonRefinement_iff_samePauliBornData_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔
      SamePauliBornData F G := by
  exact samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
    (commonRefinementProbe probeA probeB fA fB)
    (commonRefinementMap fA fB)
    (jointlySurjective_commonRefinement hA hB) F G

theorem sameAllAxisBornDataOnCommonRefinement_iff_sameAllAxisBornData_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔
      SameAllAxisBornData F G := by
  exact sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
    (commonRefinementProbe probeA probeB fA fB)
    (commonRefinementMap fA fB)
    (jointlySurjective_commonRefinement hA hB) F G

/-- Bundled common-refinement theorem for projective carrier-field covers. -/
theorem commonRefinement_projective_qubit_carrier_field_interface
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    JointlySurjective
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) ∧
    (EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔ F = G) ∧
    (SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔ SamePauliBornData F G) ∧
    (SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G ↔ SameAllAxisBornData F G) := by
  exact
    ⟨jointlySurjective_commonRefinement hA hB,
      equalOnCommonRefinement_iff_eq_of_jointlySurjective fA fB hA hB F G,
      samePauliBornDataOnCommonRefinement_iff_samePauliBornData_of_jointlySurjective
        fA fB hA hB F G,
      sameAllAxisBornDataOnCommonRefinement_iff_sameAllAxisBornData_of_jointlySurjective
        fA fB hA hB F G⟩

#print axioms ProjectiveQubitCarrierField.jointlySurjective_commonRefinement
#print axioms ProjectiveQubitCarrierField.equalOnCommonRefinement_iff_eq_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.samePauliBornDataOnCommonRefinement_iff_samePauliBornData_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornDataOnCommonRefinement_iff_sameAllAxisBornData_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.commonRefinement_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v w z t

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u}
variable {coverA : Type v} {coverB : Type w}
variable {probeA : coverA → Type z} {probeB : coverB → Type t}

theorem commonRefinement_projectiveCarrierFieldAt_reconstructed_eq
    (I : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (n : ℕ) :
    ∀ ij : ProjectiveQubitCarrierField.CommonRefinementIndex coverA coverB,
      ProjectiveQubitCarrierField.reconstructed
          (ProjectiveQubitCarrierField.pullback
            (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
            (I.projectiveCarrierFieldAt n)) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
          (I.projectiveCarrierFieldAt n) := by
  intro ij
  exact pullback_projectiveCarrierFieldAt_reconstructed_eq I
    (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij) n

/-- Local stagewise `U(1)` gauge invisibility remains true on every probe in the
common refinement. -/
theorem commonRefinement_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    ∀ ij : ProjectiveQubitCarrierField.CommonRefinementIndex coverA coverB,
      ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback
          (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
          (I.projectiveCarrierFieldAt n) := by
  intro ij
  exact pullback_phaseRotate_projectiveCarrierFieldAt_eq I
    (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij) P n

theorem commonRefinement_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.EqualOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m := by
  exact
    ProjectiveQubitCarrierField.equalOnCommonRefinement_iff_eq_of_jointlySurjective
      fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem commonRefinement_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.SamePauliBornDataOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) := by
  exact
    ProjectiveQubitCarrierField.samePauliBornDataOnCommonRefinement_iff_samePauliBornData_of_jointlySurjective
      fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem commonRefinement_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.SameAllAxisBornDataOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) := by
  exact
    ProjectiveQubitCarrierField.sameAllAxisBornDataOnCommonRefinement_iff_sameAllAxisBornData_of_jointlySurjective
      fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

/-- Bundled recovered-stage common-refinement theorem for projective carrier
field covers. -/
theorem recoveredStage_projective_qubit_carrier_field_commonRefinement_interface
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.JointlySurjective
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB) ∧
    (∀ P : ℕ → UnitPhaseField site,
      ∀ ij : ProjectiveQubitCarrierField.CommonRefinementIndex coverA coverB,
        ProjectiveQubitCarrierField.pullback
            (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
            ((I.phaseRotate P).projectiveCarrierFieldAt n) =
          ProjectiveQubitCarrierField.pullback
            (ProjectiveQubitCarrierField.commonRefinementMap fA fB ij)
            (I.projectiveCarrierFieldAt n)) ∧
    (ProjectiveQubitCarrierField.EqualOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m) ∧
    (ProjectiveQubitCarrierField.SamePauliBornDataOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      ProjectiveQubitCarrierField.SamePauliBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)) ∧
    (ProjectiveQubitCarrierField.SameAllAxisBornDataOnCover
        (ProjectiveQubitCarrierField.commonRefinementProbe probeA probeB fA fB)
        (ProjectiveQubitCarrierField.commonRefinementMap fA fB)
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m) ↔
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)) := by
  exact
    ⟨ProjectiveQubitCarrierField.jointlySurjective_commonRefinement hA hB,
      fun P => commonRefinement_phaseRotate_projectiveCarrierFieldAt_eq I fA fB P n,
      commonRefinement_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective
        I J fA fB hA hB n m,
      commonRefinement_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
        I J fA fB hA hB n m,
      commonRefinement_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
        I J fA fB hA hB n m⟩

#print axioms RecoveredStageHopfFiberInterface.commonRefinement_projectiveCarrierFieldAt_reconstructed_eq
#print axioms RecoveredStageHopfFiberInterface.commonRefinement_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.commonRefinement_projectiveCarrierFieldAt_eq_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.commonRefinement_projectiveCarrierFieldAt_samePauliBornData_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.commonRefinement_projectiveCarrierFieldAt_sameAllAxisBornData_iff_of_jointlySurjective
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_commonRefinement_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
