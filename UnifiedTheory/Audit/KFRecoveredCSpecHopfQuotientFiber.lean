/-
  Audit/KFRecoveredCSpecHopfQuotientFiber.lean

  Recovered-stage Hopf fibers as projective/unit-sphere data.

  `KFRecoveredCSpecHopfFiber` attaches normalized local spinors to each
  recovered stage/site.  `KFHopfUnitSphereQuotient` proves that normalized
  spinors modulo common `U(1)` phase carry a well-defined unit Bloch-sphere
  observable.  This file connects those two layers.

  Lean proves:

  * every local recovered-stage spinor determines a normalized phase class;
  * its quotient Bloch observable is unit-normalized and agrees with the local
    Hopf/Bloch coordinates;
  * stagewise local `U(1)` phase rotations leave the phase class and quotient
    Bloch observable unchanged.

  This is still not continuum QFT dynamics or Standard Model recovery.  It is
  the finite projective local quantum-fiber interface that those later gates
  must use.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfUnitSphereQuotient
import UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfPhaseQuotient
open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.LocalHopfSpinorField

variable {site : Type*}

/-- The normalized spinor coordinates carried by a local recovered-stage
spinor field at one site. -/
def unitSpinorAt (F : LocalHopfSpinorField site) (x : site) :
    UnitSpinorCoords where
  coords :=
    { a := F.a x
      b := F.b x
      c := F.c x
      d := F.d x }
  normalized := by
    simpa [SpinorCoords.normSq] using F.normalized x

/-- The sitewise unit phase as a scalar phase for the quotient interface. -/
def unitPhaseAt (P : UnitPhaseField site) (x : site) :
    UnitPhase where
  p := P.p x
  q := P.q x
  unit := P.unit x

/-- The normalized projective phase class carried at one site. -/
noncomputable def phaseClassAt
    (F : LocalHopfSpinorField site) (x : site) :
    UnitSpinorCoords.UnitPhaseSpinorQuotient :=
  Quot.mk UnitSpinorCoords.phaseSetoid (F.unitSpinorAt x)

/-- The quotient Bloch-sphere observable carried at one site. -/
noncomputable def quotientBlochAt
    (F : LocalHopfSpinorField site) (x : site) :
    UnitBlochCoords :=
  UnitSpinorCoords.quotientUnitBloch (F.phaseClassAt x)

/-- The quotient Bloch observable is unit-normalized at every site. -/
theorem quotientBlochAt_unit
    (F : LocalHopfSpinorField site) (x : site) :
    (F.quotientBlochAt x).x ^ 2 +
        (F.quotientBlochAt x).y ^ 2 +
        (F.quotientBlochAt x).z ^ 2 = 1 := by
  exact UnitSpinorCoords.quotientUnitBloch_unit (F.phaseClassAt x)

/-- The quotient Bloch observable has the same coordinates as the local Hopf
observable. -/
theorem quotientBlochAt_eq_localBloch
    (F : LocalHopfSpinorField site) (x : site) :
    (F.quotientBlochAt x).x = F.blochX x ∧
    (F.quotientBlochAt x).y = F.blochY x ∧
    (F.quotientBlochAt x).z = F.blochZ x := by
  simp [
    quotientBlochAt,
    phaseClassAt,
    unitSpinorAt,
    UnitSpinorCoords.unitBlochOfSpinor,
    SpinorCoords.blochX,
    SpinorCoords.blochY,
    SpinorCoords.blochZ,
    KFRecoveredCSpecHopfFiber.LocalHopfSpinorField.blochX,
    KFRecoveredCSpecHopfFiber.LocalHopfSpinorField.blochY,
    KFRecoveredCSpecHopfFiber.LocalHopfSpinorField.blochZ
  ]

/-- The repo Bloch vector agrees with the local quotient Bloch-sphere
observable. -/
theorem repo_blochVector_eq_quotientBlochAt
    (F : LocalHopfSpinorField site) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (F.spinor x) 0 = (F.quotientBlochAt x).x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (F.spinor x) 1 = (F.quotientBlochAt x).y ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        (F.spinor x) 2 = (F.quotientBlochAt x).z := by
  simpa [
    KFRecoveredCSpecHopfFiber.LocalHopfSpinorField.spinor,
    quotientBlochAt,
    phaseClassAt,
    unitSpinorAt,
    UnitSpinorCoords.spinor
  ] using
    UnitSpinorCoords.repo_blochVector_eq_unitBloch (F.unitSpinorAt x)

/-- A local phase rotation relates the original and rotated normalized spinors
in the normalized phase quotient. -/
theorem phaseRotate_unitSpinor_phaseRelated
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    UnitSpinorCoords.PhaseRelated
      (F.unitSpinorAt x) ((F.phaseRotate P).unitSpinorAt x) := by
  unfold UnitSpinorCoords.PhaseRelated SpinorCoords.PhaseRelated
  refine ⟨unitPhaseAt P x, ?_⟩
  rfl

/-- Local phase rotation leaves the normalized projective phase class
unchanged. -/
theorem phaseRotate_phaseClassAt_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    (F.phaseRotate P).phaseClassAt x = F.phaseClassAt x := by
  have h := phaseRotate_unitSpinor_phaseRelated F P x
  simpa [phaseClassAt] using (Quot.sound h).symm

/-- Local phase rotation leaves the quotient Bloch-sphere observable
unchanged. -/
theorem phaseRotate_quotientBlochAt_eq
    (F : LocalHopfSpinorField site) (P : UnitPhaseField site) (x : site) :
    (F.phaseRotate P).quotientBlochAt x = F.quotientBlochAt x := by
  exact congrArg UnitSpinorCoords.quotientUnitBloch
    (phaseRotate_phaseClassAt_eq F P x)

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.LocalHopfSpinorField

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

variable {site : Type*}

/-- The normalized projective phase class at a recovered stage/site. -/
noncomputable def phaseClassAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnitSpinorCoords.UnitPhaseSpinorQuotient :=
  (I.spinorField n).phaseClassAt x

/-- The quotient Bloch-sphere observable at a recovered stage/site. -/
noncomputable def quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnitBlochCoords :=
  (I.spinorField n).quotientBlochAt x

/-- The recovered-stage quotient Bloch observable is unit-normalized. -/
theorem quotientBlochAt_unit
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.quotientBlochAt n x).x ^ 2 +
        (I.quotientBlochAt n x).y ^ 2 +
        (I.quotientBlochAt n x).z ^ 2 = 1 := by
  exact LocalHopfSpinorField.quotientBlochAt_unit (I.spinorField n) x

/-- The recovered-stage quotient Bloch observable has the same coordinates as
the local Hopf observable. -/
theorem quotientBlochAt_eq_localBloch
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (I.quotientBlochAt n x).x = (I.spinorField n).blochX x ∧
    (I.quotientBlochAt n x).y = (I.spinorField n).blochY x ∧
    (I.quotientBlochAt n x).z = (I.spinorField n).blochZ x := by
  exact LocalHopfSpinorField.quotientBlochAt_eq_localBloch (I.spinorField n) x

/-- The repo Bloch vector agrees with the recovered-stage quotient
Bloch-sphere observable. -/
theorem repo_blochVector_eq_quotientBlochAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 0 = (I.quotientBlochAt n x).x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 1 = (I.quotientBlochAt n x).y ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector
        ((I.spinorField n).spinor x) 2 = (I.quotientBlochAt n x).z := by
  exact LocalHopfSpinorField.repo_blochVector_eq_quotientBlochAt
    (I.spinorField n) x

/-- Stagewise local phase rotation leaves the recovered-stage phase class
unchanged. -/
theorem phaseRotate_phaseClassAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).phaseClassAt n x = I.phaseClassAt n x := by
  exact LocalHopfSpinorField.phaseRotate_phaseClassAt_eq
    (I.spinorField n) (P n) x

/-- Stagewise local phase rotation leaves the recovered-stage quotient
Bloch-sphere observable unchanged. -/
theorem phaseRotate_quotientBlochAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).quotientBlochAt n x = I.quotientBlochAt n x := by
  exact LocalHopfSpinorField.phaseRotate_quotientBlochAt_eq
    (I.spinorField n) (P n) x

/-- Bundled recovered-stage projective observable statement. -/
theorem recoveredStage_projective_unit_bloch_observable
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    ∃ q : UnitSpinorCoords.UnitPhaseSpinorQuotient,
    ∃ B : UnitBlochCoords,
      I.phaseClassAt n x = q ∧
      I.quotientBlochAt n x = B ∧
      B.x ^ 2 + B.y ^ 2 + B.z ^ 2 = 1 := by
  exact
    ⟨I.phaseClassAt n x, I.quotientBlochAt n x, rfl, rfl,
      quotientBlochAt_unit I n x⟩

#print axioms LocalHopfSpinorField.unitSpinorAt
#print axioms LocalHopfSpinorField.quotientBlochAt_unit
#print axioms LocalHopfSpinorField.repo_blochVector_eq_quotientBlochAt
#print axioms LocalHopfSpinorField.phaseRotate_phaseClassAt_eq
#print axioms LocalHopfSpinorField.phaseRotate_quotientBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.quotientBlochAt_unit
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_phaseClassAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_quotientBlochAt_eq
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_projective_unit_bloch_observable

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
