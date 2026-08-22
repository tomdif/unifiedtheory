/-
  Audit/KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRestriction.lean

  Restriction/pullback covariance for recovered projective qubit carrier fields.

  `KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRelabel` handles bijective
  changes of finite site labels.  This file adds the non-bijective companion:
  carrier fields can be pulled back along any probe map into the site set.

  Lean proves:

  * carrier-field pullback is functorial for identity maps and composition;
  * Pauli reconstruction commutes with pullback;
  * Pauli/all-axis Born-data equality is preserved by every pullback;
  * if the probe map is surjective, pullback reflects carrier-field equality
    and Pauli/all-axis Born-data equality;
  * recovered-stage local `U(1)` gauge invisibility remains true after any
    probe restriction.

  This is finite probe/restriction covariance for local projective-qubit
  kinematics.  It is not detector dynamics, continuum QFT, spin/statistics,
  Standard Model recovery, quotient topology, or a physical spin-bundle
  theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierFieldRelabel

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

universe u v w

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace ProjectiveQubitCarrierField

/-- Pull a carrier field back along a probe map into the site set. -/
def pullback
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (F : ProjectiveQubitCarrierField site) :
    ProjectiveQubitCarrierField probe :=
  fun p => F (f p)

theorem pullback_apply
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (F : ProjectiveQubitCarrierField site)
    (p : probe) :
    pullback f F p = F (f p) := by
  rfl

theorem pullback_id
    {site : Type u}
    (F : ProjectiveQubitCarrierField site) :
    pullback (fun x : site => x) F = F := by
  apply ext_site
  intro x
  rfl

theorem pullback_comp
    {source : Type u} {middle : Type v} {target : Type w}
    (f : middle → target) (g : source → middle)
    (F : ProjectiveQubitCarrierField target) :
    pullback g (pullback f F) = pullback (fun x : source => f (g x)) F := by
  apply ext_site
  intro x
  rfl

/-- Pointwise Pauli Born reconstruction commutes with probe pullback. -/
theorem reconstructed_pullback
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (F : ProjectiveQubitCarrierField site) :
    reconstructed (pullback f F) = pullback f (reconstructed F) := by
  apply ext_site
  intro p
  rfl

theorem samePauliBornData_pullback
    {site : Type u} {probe : Type v}
    (f : probe → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornData F G) :
    SamePauliBornData (pullback f F) (pullback f G) := by
  intro p
  exact h (f p)

theorem sameAllAxisBornData_pullback
    {site : Type u} {probe : Type v}
    (f : probe → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornData F G) :
    SameAllAxisBornData (pullback f F) (pullback f G) := by
  intro p
  exact h (f p)

theorem pullback_eq_of_eq
    {site : Type u} {probe : Type v}
    (f : probe → site)
    {F G : ProjectiveQubitCarrierField site}
    (h : F = G) :
    pullback f F = pullback f G := by
  subst h
  rfl

theorem eq_of_pullback_eq_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    {F G : ProjectiveQubitCarrierField site}
    (h : pullback f F = pullback f G) :
    F = G := by
  apply ext_site
  intro x
  rcases hf x with ⟨p, rfl⟩
  exact congrFun h p

theorem pullback_eq_iff_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    (F G : ProjectiveQubitCarrierField site) :
    pullback f F = pullback f G ↔ F = G := by
  constructor
  · intro h
    exact eq_of_pullback_eq_of_surjective f hf h
  · intro h
    exact pullback_eq_of_eq f h

theorem samePauliBornData_of_pullback_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    {F G : ProjectiveQubitCarrierField site}
    (h : SamePauliBornData (pullback f F) (pullback f G)) :
    SamePauliBornData F G := by
  intro x
  rcases hf x with ⟨p, rfl⟩
  exact h p

theorem sameAllAxisBornData_of_pullback_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    {F G : ProjectiveQubitCarrierField site}
    (h : SameAllAxisBornData (pullback f F) (pullback f G)) :
    SameAllAxisBornData F G := by
  intro x
  rcases hf x with ⟨p, rfl⟩
  exact h p

theorem samePauliBornData_pullback_iff_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    (F G : ProjectiveQubitCarrierField site) :
    SamePauliBornData (pullback f F) (pullback f G) ↔
      SamePauliBornData F G := by
  constructor
  · intro h
    exact samePauliBornData_of_pullback_of_surjective f hf h
  · intro h
    exact samePauliBornData_pullback f h

theorem sameAllAxisBornData_pullback_iff_of_surjective
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    (F G : ProjectiveQubitCarrierField site) :
    SameAllAxisBornData (pullback f F) (pullback f G) ↔
      SameAllAxisBornData F G := by
  constructor
  · intro h
    exact sameAllAxisBornData_of_pullback_of_surjective f hf h
  · intro h
    exact sameAllAxisBornData_pullback f h

/-- Bundled pulled-back carrier-field interface. -/
theorem pullback_projective_qubit_carrier_field_interface
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (F G : ProjectiveQubitCarrierField site) :
    reconstructed (pullback f F) = pullback f F ∧
    (SamePauliBornData (pullback f F) (pullback f G) ↔
      pullback f F = pullback f G) ∧
    (SameAllAxisBornData (pullback f F) (pullback f G) ↔
      pullback f F = pullback f G) ∧
    reconstructed (pullback f F) = pullback f (reconstructed F) := by
  exact
    ⟨reconstructed_eq (pullback f F),
      samePauliBornData_iff_eq (pullback f F) (pullback f G),
      sameAllAxisBornData_iff_eq (pullback f F) (pullback f G),
      reconstructed_pullback f F⟩

/-- Bundled surjective-probe reflection theorem for carrier fields. -/
theorem surjective_pullback_projective_qubit_carrier_field_interface
    {site : Type u} {probe : Type v}
    (f : probe → site)
    (hf : Function.Surjective f)
    (F G : ProjectiveQubitCarrierField site) :
    (pullback f F = pullback f G ↔ F = G) ∧
    (SamePauliBornData (pullback f F) (pullback f G) ↔
      SamePauliBornData F G) ∧
    (SameAllAxisBornData (pullback f F) (pullback f G) ↔
      SameAllAxisBornData F G) := by
  exact
    ⟨pullback_eq_iff_of_surjective f hf F G,
      samePauliBornData_pullback_iff_of_surjective f hf F G,
      sameAllAxisBornData_pullback_iff_of_surjective f hf F G⟩

#print axioms ProjectiveQubitCarrierField.pullback_eq_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.reconstructed_pullback
#print axioms ProjectiveQubitCarrierField.samePauliBornData_pullback_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.sameAllAxisBornData_pullback_iff_of_surjective
#print axioms ProjectiveQubitCarrierField.pullback_projective_qubit_carrier_field_interface
#print axioms ProjectiveQubitCarrierField.surjective_pullback_projective_qubit_carrier_field_interface

end ProjectiveQubitCarrierField

end UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

universe u v

open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrierField.ProjectiveQubitCarrierField

variable {site : Type u} {probe : Type v}

theorem pullback_projectiveCarrierFieldAt_reconstructed_eq
    (I : RecoveredStageHopfFiberInterface site)
    (f : probe → site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n) := by
  exact ProjectiveQubitCarrierField.reconstructed_eq
    (ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n))

theorem pullback_projectiveCarrierFieldAt_reconstructed_commute
    (I : RecoveredStageHopfFiberInterface site)
    (f : probe → site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.pullback f
        (ProjectiveQubitCarrierField.reconstructed (I.projectiveCarrierFieldAt n)) := by
  exact ProjectiveQubitCarrierField.reconstructed_pullback f (I.projectiveCarrierFieldAt n)

/-- Local stagewise `U(1)` gauge invisibility remains true after any probe
restriction. -/
theorem pullback_phaseRotate_projectiveCarrierFieldAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (f : probe → site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.pullback f
        ((I.phaseRotate P).projectiveCarrierFieldAt n) =
      ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n) := by
  exact congrArg (ProjectiveQubitCarrierField.pullback f)
    (phaseRotate_projectiveCarrierFieldAt_eq I P n)

theorem pullback_projectiveCarrierFieldAt_eq_iff_of_surjective
    (I J : RecoveredStageHopfFiberInterface site)
    (f : probe → site)
    (hf : Function.Surjective f)
    (n m : ℕ) :
    ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback f (J.projectiveCarrierFieldAt m) ↔
      I.projectiveCarrierFieldAt n = J.projectiveCarrierFieldAt m := by
  exact ProjectiveQubitCarrierField.pullback_eq_iff_of_surjective f hf
    (I.projectiveCarrierFieldAt n) (J.projectiveCarrierFieldAt m)

/-- Bundled recovered-stage probe-restriction theorem for projective carrier
fields. -/
theorem recoveredStage_projective_qubit_carrier_field_pullback_interface
    (I : RecoveredStageHopfFiberInterface site)
    (f : probe → site)
    (n : ℕ) :
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n) ∧
    ProjectiveQubitCarrierField.reconstructed
        (ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n)) =
      ProjectiveQubitCarrierField.pullback f
        (ProjectiveQubitCarrierField.reconstructed (I.projectiveCarrierFieldAt n)) ∧
    ∀ P : ℕ → UnitPhaseField site,
      ProjectiveQubitCarrierField.pullback f
          ((I.phaseRotate P).projectiveCarrierFieldAt n) =
        ProjectiveQubitCarrierField.pullback f (I.projectiveCarrierFieldAt n) := by
  exact
    ⟨pullback_projectiveCarrierFieldAt_reconstructed_eq I f n,
      pullback_projectiveCarrierFieldAt_reconstructed_commute I f n,
      fun P => pullback_phaseRotate_projectiveCarrierFieldAt_eq I f P n⟩

#print axioms RecoveredStageHopfFiberInterface.pullback_projectiveCarrierFieldAt_reconstructed_eq
#print axioms RecoveredStageHopfFiberInterface.pullback_projectiveCarrierFieldAt_reconstructed_commute
#print axioms RecoveredStageHopfFiberInterface.pullback_phaseRotate_projectiveCarrierFieldAt_eq
#print axioms RecoveredStageHopfFiberInterface.pullback_projectiveCarrierFieldAt_eq_iff_of_surjective
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_qubit_carrier_field_pullback_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
