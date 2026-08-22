/-
  Audit/KFRecoveredCSpecHopfBornObservable.lean

  Local Pauli-axis Born observables from recovered-stage Hopf quotient fibers.

  The Hopf quotient stack now supplies a gauge-invariant unit Bloch-sphere
  observable at every recovered stage/site.  This file turns that observable
  into binary Pauli-axis Born probabilities:

      P_±(X) = (1 ± x)/2,  P_±(Y) = (1 ± y)/2,  P_±(Z) = (1 ± z)/2.

  Lean proves these are valid probability pairs and that local stagewise
  `U(1)` phase rotations leave them unchanged.

  This is a finite local measurement interface.  It does not derive continuum
  QFT dynamics, a detector model, spin/statistics, or Standard Model parameters.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfQuotientFiber

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

/-- A binary Born probability pair. -/
structure BinaryBornPair where
  plus : Real
  minus : Real
  plus_nonneg : 0 ≤ plus
  plus_le_one : plus ≤ 1
  minus_nonneg : 0 ≤ minus
  minus_le_one : minus ≤ 1
  total : plus + minus = 1

namespace BinaryBornPair

@[ext] theorem ext_probs {A B : BinaryBornPair}
    (hplus : A.plus = B.plus) (hminus : A.minus = B.minus) :
    A = B := by
  cases A
  cases B
  simp_all

end BinaryBornPair

end UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitBlochCoords

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

/-- The first coordinate has absolute value at most one. -/
theorem x_sq_le_one (B : UnitBlochCoords) :
    B.x ^ 2 ≤ 1 := by
  have hy : 0 ≤ B.y ^ 2 := sq_nonneg B.y
  have hz : 0 ≤ B.z ^ 2 := sq_nonneg B.z
  nlinarith [B.unit]

theorem x_le_one (B : UnitBlochCoords) :
    B.x ≤ 1 := by
  have hx2 := x_sq_le_one B
  have hsq : 0 ≤ (B.x - 1) ^ 2 := sq_nonneg (B.x - 1)
  nlinarith

theorem neg_one_le_x (B : UnitBlochCoords) :
    -1 ≤ B.x := by
  have hx2 := x_sq_le_one B
  have hsq : 0 ≤ (B.x + 1) ^ 2 := sq_nonneg (B.x + 1)
  nlinarith

/-- The second coordinate has absolute value at most one. -/
theorem y_sq_le_one (B : UnitBlochCoords) :
    B.y ^ 2 ≤ 1 := by
  have hx : 0 ≤ B.x ^ 2 := sq_nonneg B.x
  have hz : 0 ≤ B.z ^ 2 := sq_nonneg B.z
  nlinarith [B.unit]

theorem y_le_one (B : UnitBlochCoords) :
    B.y ≤ 1 := by
  have hy2 := y_sq_le_one B
  have hsq : 0 ≤ (B.y - 1) ^ 2 := sq_nonneg (B.y - 1)
  nlinarith

theorem neg_one_le_y (B : UnitBlochCoords) :
    -1 ≤ B.y := by
  have hy2 := y_sq_le_one B
  have hsq : 0 ≤ (B.y + 1) ^ 2 := sq_nonneg (B.y + 1)
  nlinarith

/-- The third coordinate has absolute value at most one. -/
theorem z_sq_le_one (B : UnitBlochCoords) :
    B.z ^ 2 ≤ 1 := by
  have hx : 0 ≤ B.x ^ 2 := sq_nonneg B.x
  have hy : 0 ≤ B.y ^ 2 := sq_nonneg B.y
  nlinarith [B.unit]

theorem z_le_one (B : UnitBlochCoords) :
    B.z ≤ 1 := by
  have hz2 := z_sq_le_one B
  have hsq : 0 ≤ (B.z - 1) ^ 2 := sq_nonneg (B.z - 1)
  nlinarith

theorem neg_one_le_z (B : UnitBlochCoords) :
    -1 ≤ B.z := by
  have hz2 := z_sq_le_one B
  have hsq : 0 ≤ (B.z + 1) ^ 2 := sq_nonneg (B.z + 1)
  nlinarith

noncomputable def bornPlusX (B : UnitBlochCoords) : Real :=
  (1 + B.x) / 2

noncomputable def bornMinusX (B : UnitBlochCoords) : Real :=
  (1 - B.x) / 2

noncomputable def bornPlusY (B : UnitBlochCoords) : Real :=
  (1 + B.y) / 2

noncomputable def bornMinusY (B : UnitBlochCoords) : Real :=
  (1 - B.y) / 2

noncomputable def bornPlusZ (B : UnitBlochCoords) : Real :=
  (1 + B.z) / 2

noncomputable def bornMinusZ (B : UnitBlochCoords) : Real :=
  (1 - B.z) / 2

theorem bornPlusX_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornPlusX := by
  have hx := neg_one_le_x B
  unfold bornPlusX
  nlinarith

theorem bornPlusX_le_one (B : UnitBlochCoords) :
    B.bornPlusX ≤ 1 := by
  have hx := x_le_one B
  unfold bornPlusX
  nlinarith

theorem bornMinusX_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornMinusX := by
  have hx := x_le_one B
  unfold bornMinusX
  nlinarith

theorem bornMinusX_le_one (B : UnitBlochCoords) :
    B.bornMinusX ≤ 1 := by
  have hx := neg_one_le_x B
  unfold bornMinusX
  nlinarith

theorem bornX_total (B : UnitBlochCoords) :
    B.bornPlusX + B.bornMinusX = 1 := by
  unfold bornPlusX bornMinusX
  ring

theorem bornPlusY_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornPlusY := by
  have hy := neg_one_le_y B
  unfold bornPlusY
  nlinarith

theorem bornPlusY_le_one (B : UnitBlochCoords) :
    B.bornPlusY ≤ 1 := by
  have hy := y_le_one B
  unfold bornPlusY
  nlinarith

theorem bornMinusY_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornMinusY := by
  have hy := y_le_one B
  unfold bornMinusY
  nlinarith

theorem bornMinusY_le_one (B : UnitBlochCoords) :
    B.bornMinusY ≤ 1 := by
  have hy := neg_one_le_y B
  unfold bornMinusY
  nlinarith

theorem bornY_total (B : UnitBlochCoords) :
    B.bornPlusY + B.bornMinusY = 1 := by
  unfold bornPlusY bornMinusY
  ring

theorem bornPlusZ_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornPlusZ := by
  have hz := neg_one_le_z B
  unfold bornPlusZ
  nlinarith

theorem bornPlusZ_le_one (B : UnitBlochCoords) :
    B.bornPlusZ ≤ 1 := by
  have hz := z_le_one B
  unfold bornPlusZ
  nlinarith

theorem bornMinusZ_nonneg (B : UnitBlochCoords) :
    0 ≤ B.bornMinusZ := by
  have hz := z_le_one B
  unfold bornMinusZ
  nlinarith

theorem bornMinusZ_le_one (B : UnitBlochCoords) :
    B.bornMinusZ ≤ 1 := by
  have hz := neg_one_le_z B
  unfold bornMinusZ
  nlinarith

theorem bornZ_total (B : UnitBlochCoords) :
    B.bornPlusZ + B.bornMinusZ = 1 := by
  unfold bornPlusZ bornMinusZ
  ring

/-- The Pauli-X Born probability pair. -/
noncomputable def bornX (B : UnitBlochCoords) : BinaryBornPair where
  plus := B.bornPlusX
  minus := B.bornMinusX
  plus_nonneg := bornPlusX_nonneg B
  plus_le_one := bornPlusX_le_one B
  minus_nonneg := bornMinusX_nonneg B
  minus_le_one := bornMinusX_le_one B
  total := bornX_total B

/-- The Pauli-Y Born probability pair. -/
noncomputable def bornY (B : UnitBlochCoords) : BinaryBornPair where
  plus := B.bornPlusY
  minus := B.bornMinusY
  plus_nonneg := bornPlusY_nonneg B
  plus_le_one := bornPlusY_le_one B
  minus_nonneg := bornMinusY_nonneg B
  minus_le_one := bornMinusY_le_one B
  total := bornY_total B

/-- The Pauli-Z Born probability pair. -/
noncomputable def bornZ (B : UnitBlochCoords) : BinaryBornPair where
  plus := B.bornPlusZ
  minus := B.bornMinusZ
  plus_nonneg := bornPlusZ_nonneg B
  plus_le_one := bornPlusZ_le_one B
  minus_nonneg := bornMinusZ_nonneg B
  minus_le_one := bornMinusZ_le_one B
  total := bornZ_total B

theorem bornX_valid (B : UnitBlochCoords) :
    0 ≤ (B.bornX).plus ∧ (B.bornX).plus ≤ 1 ∧
    0 ≤ (B.bornX).minus ∧ (B.bornX).minus ≤ 1 ∧
    (B.bornX).plus + (B.bornX).minus = 1 := by
  exact
    ⟨(B.bornX).plus_nonneg, (B.bornX).plus_le_one,
      (B.bornX).minus_nonneg, (B.bornX).minus_le_one,
      (B.bornX).total⟩

theorem bornY_valid (B : UnitBlochCoords) :
    0 ≤ (B.bornY).plus ∧ (B.bornY).plus ≤ 1 ∧
    0 ≤ (B.bornY).minus ∧ (B.bornY).minus ≤ 1 ∧
    (B.bornY).plus + (B.bornY).minus = 1 := by
  exact
    ⟨(B.bornY).plus_nonneg, (B.bornY).plus_le_one,
      (B.bornY).minus_nonneg, (B.bornY).minus_le_one,
      (B.bornY).total⟩

theorem bornZ_valid (B : UnitBlochCoords) :
    0 ≤ (B.bornZ).plus ∧ (B.bornZ).plus ≤ 1 ∧
    0 ≤ (B.bornZ).minus ∧ (B.bornZ).minus ≤ 1 ∧
    (B.bornZ).plus + (B.bornZ).minus = 1 := by
  exact
    ⟨(B.bornZ).plus_nonneg, (B.bornZ).plus_le_one,
      (B.bornZ).minus_nonneg, (B.bornZ).minus_le_one,
      (B.bornZ).total⟩

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitBlochCoords

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

variable {site : Type*}

noncomputable def bornXAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    BinaryBornPair :=
  (I.quotientBlochAt n x).bornX

noncomputable def bornYAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    BinaryBornPair :=
  (I.quotientBlochAt n x).bornY

noncomputable def bornZAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    BinaryBornPair :=
  (I.quotientBlochAt n x).bornZ

theorem bornXAt_valid
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    0 ≤ (I.bornXAt n x).plus ∧ (I.bornXAt n x).plus ≤ 1 ∧
    0 ≤ (I.bornXAt n x).minus ∧ (I.bornXAt n x).minus ≤ 1 ∧
    (I.bornXAt n x).plus + (I.bornXAt n x).minus = 1 := by
  exact UnitBlochCoords.bornX_valid (I.quotientBlochAt n x)

theorem bornYAt_valid
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    0 ≤ (I.bornYAt n x).plus ∧ (I.bornYAt n x).plus ≤ 1 ∧
    0 ≤ (I.bornYAt n x).minus ∧ (I.bornYAt n x).minus ≤ 1 ∧
    (I.bornYAt n x).plus + (I.bornYAt n x).minus = 1 := by
  exact UnitBlochCoords.bornY_valid (I.quotientBlochAt n x)

theorem bornZAt_valid
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    0 ≤ (I.bornZAt n x).plus ∧ (I.bornZAt n x).plus ≤ 1 ∧
    0 ≤ (I.bornZAt n x).minus ∧ (I.bornZAt n x).minus ≤ 1 ∧
    (I.bornZAt n x).plus + (I.bornZAt n x).minus = 1 := by
  exact UnitBlochCoords.bornZ_valid (I.quotientBlochAt n x)

theorem phaseRotate_bornXAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).bornXAt n x = I.bornXAt n x := by
  exact congrArg UnitBlochCoords.bornX
    (phaseRotate_quotientBlochAt_eq I P n x)

theorem phaseRotate_bornYAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).bornYAt n x = I.bornYAt n x := by
  exact congrArg UnitBlochCoords.bornY
    (phaseRotate_quotientBlochAt_eq I P n x)

theorem phaseRotate_bornZAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).bornZAt n x = I.bornZAt n x := by
  exact congrArg UnitBlochCoords.bornZ
    (phaseRotate_quotientBlochAt_eq I P n x)

/-- Bundled recovered-stage local Pauli Born interface. -/
theorem recoveredStage_local_pauli_born_interface
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    (0 ≤ (I.bornXAt n x).plus ∧ (I.bornXAt n x).plus ≤ 1 ∧
      0 ≤ (I.bornXAt n x).minus ∧ (I.bornXAt n x).minus ≤ 1 ∧
      (I.bornXAt n x).plus + (I.bornXAt n x).minus = 1) ∧
    (0 ≤ (I.bornYAt n x).plus ∧ (I.bornYAt n x).plus ≤ 1 ∧
      0 ≤ (I.bornYAt n x).minus ∧ (I.bornYAt n x).minus ≤ 1 ∧
      (I.bornYAt n x).plus + (I.bornYAt n x).minus = 1) ∧
    (0 ≤ (I.bornZAt n x).plus ∧ (I.bornZAt n x).plus ≤ 1 ∧
      0 ≤ (I.bornZAt n x).minus ∧ (I.bornZAt n x).minus ≤ 1 ∧
      (I.bornZAt n x).plus + (I.bornZAt n x).minus = 1) := by
  exact
    ⟨bornXAt_valid I n x, bornYAt_valid I n x, bornZAt_valid I n x⟩

#print axioms UnitBlochCoords.x_sq_le_one
#print axioms UnitBlochCoords.bornX_valid
#print axioms UnitBlochCoords.bornY_valid
#print axioms UnitBlochCoords.bornZ_valid
#print axioms RecoveredStageHopfFiberInterface.bornXAt_valid
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_bornXAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_bornYAt_eq
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_bornZAt_eq
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_pauli_born_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
