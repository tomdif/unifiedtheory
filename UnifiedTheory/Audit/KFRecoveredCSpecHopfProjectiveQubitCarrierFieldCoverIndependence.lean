/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCoverIndependence.lean

  Cover-independence for recovered projective qubit carrier fields.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCommonRefinement` proves that
  two jointly-surjective probe covers have a fiber-product common refinement.
  This file packages the direct consequence: any two jointly-surjective probe
  covers give the same equality and Born-data tests for a recovered carrier
  field.

  Lean proves:

  * carrier-field equality on one jointly-surjective cover is equivalent to
    carrier-field equality on any other jointly-surjective cover;
  * Pauli/all-axis Born-data equality on one jointly-surjective cover is
    equivalent to the corresponding Born-data equality on any other;
  * both cover tests are equivalent to the common-refinement test;
  * recovered-stage local `U(1)` gauge invisibility remains true on both
    jointly-surjective covers.

  This is finite cover-choice independence for local projective-qubit
  kinematics.  It is not detector dynamics, continuum QFT, spin/statistics,
  Standard Model recovery, quotient topology, a sheaf over a topological site,
  or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldCommonRefinement

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w z t

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

theorem equalOnCover_left_iff_right_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    EqualOnCover probeA fA F G ↔ EqualOnCover probeB fB F G := by
  exact
    (equalOnCover_iff_eq_of_jointlySurjective probeA fA hA F G).trans
      ((equalOnCover_iff_eq_of_jointlySurjective probeB fB hB F G).symm)

theorem samePauliBornDataOnCover_left_iff_right_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover probeB fB F G := by
  exact
    (samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
      probeA fA hA F G).trans
      ((samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
        probeB fB hB F G).symm)

theorem sameAllAxisBornDataOnCover_left_iff_right_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover probeB fB F G := by
  exact
    (sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
      probeA fA hA F G).trans
      ((sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
        probeB fB hB F G).symm)

theorem equalOnCover_iff_commonRefinement_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    EqualOnCover probeA fA F G ↔
      EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G := by
  exact
    (equalOnCover_iff_eq_of_jointlySurjective probeA fA hA F G).trans
      ((equalOnCommonRefinement_iff_eq_of_jointlySurjective
        fA fB hA hB F G).symm)

theorem samePauliBornDataOnCover_iff_commonRefinement_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G := by
  exact
    (samePauliBornDataOnCover_iff_samePauliBornData_of_jointlySurjective
      probeA fA hA F G).trans
      ((samePauliBornDataOnCommonRefinement_iff_samePauliBornData_of_jointlySurjective
        fA fB hA hB F G).symm)

theorem sameAllAxisBornDataOnCover_iff_commonRefinement_of_jointlySurjective
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G := by
  exact
    (sameAllAxisBornDataOnCover_iff_sameAllAxisBornData_of_jointlySurjective
      probeA fA hA F G).trans
      ((sameAllAxisBornDataOnCommonRefinement_iff_sameAllAxisBornData_of_jointlySurjective
        fA fB hA hB F G).symm)

/-- Bundled cover-choice independence theorem for projective carrier fields. -/
theorem coverIndependence_projective_qubit_carrier_field_interface
    {coverA : Type u} {coverB : Type v} {site : Type w}
    {probeA : coverA → Type z}
    {probeB : coverB → Type t}
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : JointlySurjective probeA fA)
    (hB : JointlySurjective probeB fB)
    (F G : ProjectiveQubitCarrierField site) :
    (EqualOnCover probeA fA F G ↔ EqualOnCover probeB fB F G) ∧
    (SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover probeB fB F G) ∧
    (SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover probeB fB F G) ∧
    (EqualOnCover probeA fA F G ↔
      EqualOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) ∧
    (SamePauliBornDataOnCover probeA fA F G ↔
      SamePauliBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) ∧
    (SameAllAxisBornDataOnCover probeA fA F G ↔
      SameAllAxisBornDataOnCover
        (commonRefinementProbe probeA probeB fA fB)
        (commonRefinementMap fA fB) F G) := by
  exact
    ⟨equalOnCover_left_iff_right_of_jointlySurjective fA fB hA hB F G,
      samePauliBornDataOnCover_left_iff_right_of_jointlySurjective fA fB hA hB F G,
      sameAllAxisBornDataOnCover_left_iff_right_of_jointlySurjective fA fB hA hB F G,
      equalOnCover_iff_commonRefinement_of_jointlySurjective fA fB hA hB F G,
      samePauliBornDataOnCover_iff_commonRefinement_of_jointlySurjective
        fA fB hA hB F G,
      sameAllAxisBornDataOnCover_iff_commonRefinement_of_jointlySurjective
        fA fB hA hB F G⟩

#print axioms ProjectiveQubitCarrierField.equalOnCover_left_iff_right_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.samePauliBornDataOnCover_left_iff_right_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_left_iff_right_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.equalOnCover_iff_commonRefinement_of_jointlySurjective
#print axioms ProjectiveQubitCarrierField.coverIndependence_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v w z t

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u}
variable {coverA : Type v} {coverB : Type w}
variable {probeA : coverA → Type z} {probeB : coverB → Type t}

theorem coverIndependence_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    (∀ i : coverA,
      ProjectiveQubitCarrierField.pullback (fA i)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n)) ∧
    (∀ j : coverB,
      ProjectiveQubitCarrierField.pullback (fB j)
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n)) := by
  exact
    ⟨fun i => pullback_phaseRotate_projectiveCarrierFieldAt_eq I (fA i) P n,
      fun j => pullback_phaseRotate_projectiveCarrierFieldAt_eq I (fB j) P n⟩

theorem coverIndependence_projectiveCarrierFieldAt_eq_iff
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    (∀ i : coverA,
      ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m)) ↔
    (∀ j : coverB,
      ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m)) := by
  exact ProjectiveQubitCarrierField.equalOnCover_left_iff_right_of_jointlySurjective
    fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem coverIndependence_projectiveCarrierFieldAt_samePauliBornData_iff
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    (∀ i : coverA,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m))) ↔
    (∀ j : coverB,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m))) := by
  exact
    ProjectiveQubitCarrierField.samePauliBornDataOnCover_left_iff_right_of_jointlySurjective
      fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

theorem coverIndependence_projectiveCarrierFieldAt_sameAllAxisBornData_iff
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    (∀ i : coverA,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m))) ↔
    (∀ j : coverB,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m))) := by
  exact
    ProjectiveQubitCarrierField.sameAllAxisBornDataOnCover_left_iff_right_of_jointlySurjective
      fA fB hA hB (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

/-- Bundled recovered-stage cover-choice independence theorem for projective
carrier fields. -/
theorem recoveredStage_projective_qubit_carrier_field_coverIndependence_interface
    (I J : RecoveredStageHopfFiberInterface site)
    (fA : (i : coverA) → probeA i → site)
    (fB : (j : coverB) → probeB j → site)
    (hA : ProjectiveQubitCarrierField.JointlySurjective probeA fA)
    (hB : ProjectiveQubitCarrierField.JointlySurjective probeB fB)
    (n m : ℕ) :
    ((∀ i : coverA,
      ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m)) ↔
      (∀ j : coverB,
        ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n) =
          ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m))) ∧
    ((∀ i : coverA,
      ProjectiveQubitCarrierField.SamePauliBornData
        (ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m))) ↔
      (∀ j : coverB,
        ProjectiveQubitCarrierField.SamePauliBornData
          (ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n))
          (ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m)))) ∧
    ((∀ i : coverA,
      ProjectiveQubitCarrierField.SameAllAxisBornData
        (ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n))
        (ProjectiveQubitCarrierField.pullback (fA i) (J.projectiveCarrierFieldAt m))) ↔
      (∀ j : coverB,
        ProjectiveQubitCarrierField.SameAllAxisBornData
          (ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n))
          (ProjectiveQubitCarrierField.pullback (fB j) (J.projectiveCarrierFieldAt m)))) ∧
    (∀ P : ℕ → UnitPhaseField site,
      (∀ i : coverA,
        ProjectiveQubitCarrierField.pullback (fA i)
            ((I.phaseRotate P).projectiveCarrierFieldAt n) =
          ProjectiveQubitCarrierField.pullback (fA i) (I.projectiveCarrierFieldAt n)) ∧
      (∀ j : coverB,
        ProjectiveQubitCarrierField.pullback (fB j)
            ((I.phaseRotate P).projectiveCarrierFieldAt n) =
          ProjectiveQubitCarrierField.pullback (fB j) (I.projectiveCarrierFieldAt n))) := by
  exact
    ⟨coverIndependence_projectiveCarrierFieldAt_eq_iff I J fA fB hA hB n m,
      coverIndependence_projectiveCarrierFieldAt_samePauliBornData_iff
        I J fA fB hA hB n m,
      coverIndependence_projectiveCarrierFieldAt_sameAllAxisBornData_iff
        I J fA fB hA hB n m,
      fun P => coverIndependence_phaseRotate_projectiveCarrierFieldAt_eq I fA fB P n⟩

#print axioms RecoveredStageHopfFiberInterface.coverIndependence_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.coverIndependence_projectiveCarrierFieldAt_eq_iff
#print axioms RecoveredStageHopfFiberInterface.coverIndependence_projectiveCarrierFieldAt_samePauliBornData_iff
#print axioms RecoveredStageHopfFiberInterface.coverIndependence_projectiveCarrierFieldAt_sameAllAxisBornData_iff
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_coverIndependence_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
