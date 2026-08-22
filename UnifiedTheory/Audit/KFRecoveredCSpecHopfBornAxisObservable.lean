/-
  Audit/KFRecoveredCSpecHopfBornAxisObservable.lean

  Arbitrary-axis Born observables from recovered-stage Hopf quotient fibers.

  `KFRecoveredCSpecHopfBornObservable` proves valid Pauli-X/Y/Z binary Born
  probabilities from the local quotient Bloch observable.  This file upgrades
  that finite measurement interface to any unit axis on the Bloch sphere:

      P_±(a | B) = (1 ± a · B)/2.

  Lean proves:

  * for a unit axis `a` and unit Bloch observable `B`, `a · B ∈ [-1,1]`;
  * the corresponding plus/minus pair is a valid probability pair;
  * stagewise local `U(1)` gauge rotations leave these arbitrary-axis Born
    probabilities unchanged;
  * the coordinate axes recover the previous Pauli-X/Y/Z Born pairs.

  This is still a finite local measurement interface.  It does not derive
  detector dynamics, continuum QFT, spin/statistics, or Standard Model
  parameters.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber

/-- A unit measurement axis on the Bloch sphere. -/
structure UnitBlochAxis where
  nx : Real
  ny : Real
  nz : Real
  unit : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1

namespace UnitBlochAxis

@[ext] theorem ext_coords {A C : UnitBlochAxis}
    (hx : A.nx = C.nx) (hy : A.ny = C.ny) (hz : A.nz = C.nz) :
    A = C := by
  cases A
  cases C
  simp_all

/-- Dot product of a measurement axis with a unit Bloch observable. -/
def dot (A : UnitBlochAxis) (B : UnitBlochCoords) : Real :=
  A.nx * B.x + A.ny * B.y + A.nz * B.z

/-- Lagrange's identity in the three real coordinates used by the Bloch
observable. -/
theorem lagrange_identity (A : UnitBlochAxis) (B : UnitBlochCoords) :
    (B.x ^ 2 + B.y ^ 2 + B.z ^ 2) *
        (A.nx ^ 2 + A.ny ^ 2 + A.nz ^ 2) -
      A.dot B ^ 2 =
    (B.x * A.ny - B.y * A.nx) ^ 2 +
      (B.x * A.nz - B.z * A.nx) ^ 2 +
      (B.y * A.nz - B.z * A.ny) ^ 2 := by
  unfold dot
  ring

/-- A unit-axis expectation value lies in the closed interval `[-1,1]` in
the squared form. -/
theorem dot_sq_le_one (A : UnitBlochAxis) (B : UnitBlochCoords) :
    A.dot B ^ 2 ≤ 1 := by
  have hlag := lagrange_identity A B
  have hnonneg :
      0 ≤
        (B.x * A.ny - B.y * A.nx) ^ 2 +
          (B.x * A.nz - B.z * A.nx) ^ 2 +
          (B.y * A.nz - B.z * A.ny) ^ 2 := by
    nlinarith [
      sq_nonneg (B.x * A.ny - B.y * A.nx),
      sq_nonneg (B.x * A.nz - B.z * A.nx),
      sq_nonneg (B.y * A.nz - B.z * A.ny)]
  have hprod :
      (B.x ^ 2 + B.y ^ 2 + B.z ^ 2) *
          (A.nx ^ 2 + A.ny ^ 2 + A.nz ^ 2) = 1 := by
    rw [B.unit, A.unit]
    norm_num
  nlinarith

theorem dot_le_one (A : UnitBlochAxis) (B : UnitBlochCoords) :
    A.dot B ≤ 1 := by
  have hsq := dot_sq_le_one A B
  have hnonneg : 0 ≤ (A.dot B - 1) ^ 2 := sq_nonneg (A.dot B - 1)
  nlinarith

theorem neg_one_le_dot (A : UnitBlochAxis) (B : UnitBlochCoords) :
    -1 ≤ A.dot B := by
  have hsq := dot_sq_le_one A B
  have hnonneg : 0 ≤ (A.dot B + 1) ^ 2 := sq_nonneg (A.dot B + 1)
  nlinarith

noncomputable def bornPlusAlong
    (A : UnitBlochAxis) (B : UnitBlochCoords) : Real :=
  (1 + A.dot B) / 2

noncomputable def bornMinusAlong
    (A : UnitBlochAxis) (B : UnitBlochCoords) : Real :=
  (1 - A.dot B) / 2

theorem bornPlusAlong_nonneg
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    0 ≤ A.bornPlusAlong B := by
  have hdot := neg_one_le_dot A B
  unfold bornPlusAlong
  nlinarith

theorem bornPlusAlong_le_one
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    A.bornPlusAlong B ≤ 1 := by
  have hdot := dot_le_one A B
  unfold bornPlusAlong
  nlinarith

theorem bornMinusAlong_nonneg
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    0 ≤ A.bornMinusAlong B := by
  have hdot := dot_le_one A B
  unfold bornMinusAlong
  nlinarith

theorem bornMinusAlong_le_one
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    A.bornMinusAlong B ≤ 1 := by
  have hdot := neg_one_le_dot A B
  unfold bornMinusAlong
  nlinarith

theorem bornAlong_total
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    A.bornPlusAlong B + A.bornMinusAlong B = 1 := by
  unfold bornPlusAlong bornMinusAlong
  ring

/-- Binary Born probability pair for measurement along an arbitrary unit axis. -/
noncomputable def bornAlong
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    BinaryBornPair where
  plus := A.bornPlusAlong B
  minus := A.bornMinusAlong B
  plus_nonneg := bornPlusAlong_nonneg A B
  plus_le_one := bornPlusAlong_le_one A B
  minus_nonneg := bornMinusAlong_nonneg A B
  minus_le_one := bornMinusAlong_le_one A B
  total := bornAlong_total A B

theorem bornAlong_valid
    (A : UnitBlochAxis) (B : UnitBlochCoords) :
    0 ≤ (A.bornAlong B).plus ∧ (A.bornAlong B).plus ≤ 1 ∧
    0 ≤ (A.bornAlong B).minus ∧ (A.bornAlong B).minus ≤ 1 ∧
    (A.bornAlong B).plus + (A.bornAlong B).minus = 1 := by
  exact
    ⟨(A.bornAlong B).plus_nonneg, (A.bornAlong B).plus_le_one,
      (A.bornAlong B).minus_nonneg, (A.bornAlong B).minus_le_one,
      (A.bornAlong B).total⟩

/-- The Pauli-X measurement axis. -/
def pauliX : UnitBlochAxis where
  nx := 1
  ny := 0
  nz := 0
  unit := by norm_num

/-- The Pauli-Y measurement axis. -/
def pauliY : UnitBlochAxis where
  nx := 0
  ny := 1
  nz := 0
  unit := by norm_num

/-- The Pauli-Z measurement axis. -/
def pauliZ : UnitBlochAxis where
  nx := 0
  ny := 0
  nz := 1
  unit := by norm_num

theorem pauliX_bornAlong_eq_bornX (B : UnitBlochCoords) :
    pauliX.bornAlong B = B.bornX := by
  apply BinaryBornPair.ext_probs
  · simp [
      bornAlong, bornPlusAlong, dot, pauliX,
      UnitBlochCoords.bornX, UnitBlochCoords.bornPlusX]
  · simp [
      bornAlong, bornMinusAlong, dot, pauliX,
      UnitBlochCoords.bornX, UnitBlochCoords.bornMinusX]

theorem pauliY_bornAlong_eq_bornY (B : UnitBlochCoords) :
    pauliY.bornAlong B = B.bornY := by
  apply BinaryBornPair.ext_probs
  · simp [
      bornAlong, bornPlusAlong, dot, pauliY,
      UnitBlochCoords.bornY, UnitBlochCoords.bornPlusY]
  · simp [
      bornAlong, bornMinusAlong, dot, pauliY,
      UnitBlochCoords.bornY, UnitBlochCoords.bornMinusY]

theorem pauliZ_bornAlong_eq_bornZ (B : UnitBlochCoords) :
    pauliZ.bornAlong B = B.bornZ := by
  apply BinaryBornPair.ext_probs
  · simp [
      bornAlong, bornPlusAlong, dot, pauliZ,
      UnitBlochCoords.bornZ, UnitBlochCoords.bornPlusZ]
  · simp [
      bornAlong, bornMinusAlong, dot, pauliZ,
      UnitBlochCoords.bornZ, UnitBlochCoords.bornMinusZ]

end UnitBlochAxis

end UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

namespace UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface

open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

variable {site : Type*}

/-- Local arbitrary-axis Born probabilities at a recovered stage/site. -/
noncomputable def bornAlongAt
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    BinaryBornPair :=
  A.bornAlong (I.quotientBlochAt n x)

theorem bornAlongAt_valid
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    0 ≤ (I.bornAlongAt A n x).plus ∧
    (I.bornAlongAt A n x).plus ≤ 1 ∧
    0 ≤ (I.bornAlongAt A n x).minus ∧
    (I.bornAlongAt A n x).minus ≤ 1 ∧
    (I.bornAlongAt A n x).plus + (I.bornAlongAt A n x).minus = 1 := by
  exact UnitBlochAxis.bornAlong_valid A (I.quotientBlochAt n x)

theorem phaseRotate_bornAlongAt_eq
    (I : RecoveredStageHopfFiberInterface site)
    (P : ℕ → UnitPhaseField site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (I.phaseRotate P).bornAlongAt A n x = I.bornAlongAt A n x := by
  exact congrArg (UnitBlochAxis.bornAlong A)
    (phaseRotate_quotientBlochAt_eq I P n x)

theorem bornAlongAt_pauliX_eq_bornXAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.bornAlongAt UnitBlochAxis.pauliX n x = I.bornXAt n x := by
  exact UnitBlochAxis.pauliX_bornAlong_eq_bornX (I.quotientBlochAt n x)

theorem bornAlongAt_pauliY_eq_bornYAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.bornAlongAt UnitBlochAxis.pauliY n x = I.bornYAt n x := by
  exact UnitBlochAxis.pauliY_bornAlong_eq_bornY (I.quotientBlochAt n x)

theorem bornAlongAt_pauliZ_eq_bornZAt
    (I : RecoveredStageHopfFiberInterface site)
    (n : ℕ) (x : site) :
    I.bornAlongAt UnitBlochAxis.pauliZ n x = I.bornZAt n x := by
  exact UnitBlochAxis.pauliZ_bornAlong_eq_bornZ (I.quotientBlochAt n x)

/-- Bundled recovered-stage arbitrary-axis Born interface. -/
theorem recoveredStage_local_axis_born_interface
    (I : RecoveredStageHopfFiberInterface site)
    (A : UnitBlochAxis)
    (n : ℕ) (x : site) :
    (0 ≤ (I.bornAlongAt A n x).plus ∧
      (I.bornAlongAt A n x).plus ≤ 1 ∧
      0 ≤ (I.bornAlongAt A n x).minus ∧
      (I.bornAlongAt A n x).minus ≤ 1 ∧
      (I.bornAlongAt A n x).plus + (I.bornAlongAt A n x).minus = 1) ∧
    (∀ P : ℕ → UnitPhaseField site,
      (I.phaseRotate P).bornAlongAt A n x = I.bornAlongAt A n x) := by
  exact
    ⟨bornAlongAt_valid I A n x,
      fun P => phaseRotate_bornAlongAt_eq I P A n x⟩

#print axioms UnitBlochAxis.lagrange_identity
#print axioms UnitBlochAxis.dot_sq_le_one
#print axioms UnitBlochAxis.bornAlong_valid
#print axioms UnitBlochAxis.pauliX_bornAlong_eq_bornX
#print axioms RecoveredStageHopfFiberInterface.bornAlongAt_valid
#print axioms RecoveredStageHopfFiberInterface.phaseRotate_bornAlongAt_eq
#print axioms RecoveredStageHopfFiberInterface.bornAlongAt_pauliX_eq_bornXAt
#print axioms RecoveredStageHopfFiberInterface.recoveredStage_local_axis_born_interface

end UnifiedTheory.Audit.KFRecoveredCSpecHopfFiber.RecoveredStageHopfFiberInterface
