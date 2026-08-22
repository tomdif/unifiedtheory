/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRelabel.lean

  Site-relabel covariance for recovered projective qubit carrier fields.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierField` packages one recovered
  projective qubit carrier at every site of a recovered stage.  This file
  proves that the carrier-field interface is covariant under finite site
  bijections:

  * a carrier field can be pushed forward along a site equivalence;
  * reconstruction commutes with that relabeling;
  * Pauli/all-axis Born-data equality is preserved and reflected by relabeling;
  * relabeling is injective on carrier fields;
  * recovered-stage local `U(1)` gauge invariance remains true after relabeling.

  This is finite site-label covariance for local projective-qubit kinematics.
  It is not detector dynamics, continuum QFT, spin/statistics, Standard Model
  recovery, quotient topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

/-- Push a carrier field forward along a site equivalence. -/
def relabel
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F : ProjectiveQubitCarrierField site) :
    ProjectiveQubitCarrierField site' :=
  fun y => F (e.symm y)

theorem relabel_apply
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F : ProjectiveQubitCarrierField site)
    (y : site') :
    relabel e F y = F (e.symm y) := by
  rfl

theorem relabel_refl
    {site : Type u}
    (F : ProjectiveQubitCarrierField site) :
    relabel (Equiv.refl site) F = F := by
  apply ext_site
  intro x
  rfl

theorem relabel_trans
    {site : Type u} {site' : Type v} {site'' : Type w}
    (e : site ≃ site') (f : site' ≃ site'')
    (F : ProjectiveQubitCarrierField site) :
    relabel f (relabel e F) = relabel (e.trans f) F := by
  apply ext_site
  intro z
  rfl

theorem relabel_symm_relabel
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F : ProjectiveQubitCarrierField site) :
    relabel e.symm (relabel e F) = F := by
  apply ext_site
  intro x
  simp [relabel]

theorem relabel_relabel_symm
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F : ProjectiveQubitCarrierField site') :
    relabel e (relabel e.symm F) = F := by
  apply ext_site
  intro y
  simp [relabel]

/-- Pointwise Pauli Born reconstruction commutes with site relabeling. -/
theorem reconstructed_relabel
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F : ProjectiveQubitCarrierField site) :
    reconstructed (relabel e F) = relabel e (reconstructed F) := by
  apply ext_site
  intro y
  rfl

theorem samePauliBornData_relabel_iff
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornData (relabel e F) (relabel e G) ↔
      SamePauliBornData F G := by
  constructor
  · intro h x
    simpa [relabel] using h (e x)
  · intro h y
    simpa [relabel] using h (e.symm y)

theorem sameAllAxisBornData_relabel_iff
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornData (relabel e F) (relabel e G) ↔
      SameAllAxisBornData F G := by
  constructor
  · intro h x
    simpa [relabel] using h (e x)
  · intro h y
    simpa [relabel] using h (e.symm y)

theorem relabel_eq_iff
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F G : ProjectiveQubitCarrierField site) :
    relabel e F = relabel e G ↔ F = G := by
  constructor
  · intro h
    apply ext_site
    intro x
    have hx := congrFun h (e x)
    simpa [relabel] using hx
  · intro h
    subst h
    rfl

/-- Bundled relabeled carrier-field interface. -/
theorem relabel_projective_qubit_carrier_field_interface
    {site : Type u} {site' : Type v}
    (e : site ≃ site')
    (F G : ProjectiveQubitCarrierField site) :
    reconstructed (relabel e F) = relabel e F ∧
    (SamePauliBornData (relabel e F) (relabel e G) ↔
      relabel e F = relabel e G) ∧
    (SameAllAxisBornData (relabel e F) (relabel e G) ↔
      relabel e F = relabel e G) ∧
    reconstructed (relabel e F) = relabel e (reconstructed F) := by
  exact
    ⟨reconstructed_eq (relabel e F),
      samePauliBornData_iff_eq (relabel e F) (relabel e G),
      sameAllAxisBornData_iff_eq (relabel e F) (relabel e G),
      reconstructed_relabel e F⟩

#print axioms ProjectiveQubitCarrierField.relabel_eq_iff
#print axioms ProjectiveQubitCarrierField.reconstructed_relabel
#print axioms ProjectiveQubitCarrierField.samePauliBornData_relabel_iff
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornData_relabel_iff
#print axioms ProjectiveQubitCarrierField.relabel_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u} {site' : Type v}

theorem relabel_projectiveCarrierFieldAt_reconstructed_eq
    (I : RecoveredStageHopfFiberInterface site)
    (e : site ≃ site')
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n) := by
  exact ProjectiveQubitCarrierField.reconstructed_eq
    (ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n))

/-- Local stagewise `U(1)` gauge invisibility remains true after any site
relabeling. -/
theorem relabel_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (e : site ≃ site')
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.relabel e
        ((I.phaseRotate P).projectiveCarrierFieldAt n) =
      ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n) := by
  exact congrArg (ProjectiveQubitCarrierField.relabel e)
    (phaseRotate_projectiveCarrierFieldAt_eq I P n)

/-- Bundled recovered-stage relabel covariance theorem for projective carrier
fields. -/
theorem recoveredStage_projective_qubit_carrier_field_relabel_interface
    (I : RecoveredStageHopfFiberInterface site)
    (e : site ≃ site')
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n) ∧
    ∀ P : ℕ → UnitPhaseField site,
      ProjectiveQubitCarrierField.relabel e
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.relabel e (I.projectiveCarrierFieldAt n) := by
  exact
    ⟨relabel_projectiveCarrierFieldAt_reconstructed_eq I e n,
      fun P => relabel_phaseRotate_projectiveCarrierFieldAt_eq I e P n⟩

#print axioms RecoveredStageHopfFiberInterface.relabel_projectiveCarrierFieldAt_reconstructed_eq
#print axioms RecoveredStageHopfFiberInterface.relabel_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_relabel_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
