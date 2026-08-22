/-
  Audit/KFHopfProjectiveQubitState.lean

  Stable finite projective-qubit state interface for the Hopf/Born bridge.

  The Hopf quotient stack proves that normalized spinors modulo common `U(1)`
  phase are in bijection with the unit Bloch sphere, and the Born stack proves
  Pauli/all-axis tomography.  This file packages those results behind one
  algebraic API:

  * a `ProjectiveQubitState` is the normalized Hopf phase quotient;
  * each state has a Bloch point, Pauli Born pairs, and arbitrary-axis Born
    pairs;
  * Pauli Born expectations reconstruct the state;
  * equality of states is equivalent to equality of Pauli Born data, and also
    to equality of all-axis Born data.

  This is a finite local projective-qubit interface.  It is not detector
  dynamics, continuum QFT, spin/statistics, Standard Model recovery, quotient
  topology, or a physical spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfQuotientInverse
import UnifiedTheory.Audit.KFRecoveredCSpecHopfBornTomography

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFHopfProjectiveQubitState

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornAxisObservable

/-- A finite projective qubit state: a normalized two-component spinor modulo
common `U(1)` phase. -/
abbrev ProjectiveQubitState : Type :=
  UnitSpinorCoords.UnitPhaseSpinorQuotient

namespace ProjectiveQubitState

/-- The Bloch point associated to a projective qubit state. -/
noncomputable def bloch (ψ : ProjectiveQubitState) : UnitBlochCoords :=
  UnitSpinorCoords.quotientUnitBloch ψ

/-- The projective qubit state associated to a unit Bloch point by the chosen
algebraic inverse. -/
noncomputable def ofBloch (B : UnitBlochCoords) : ProjectiveQubitState :=
  UnitSpinorCoords.phaseClassOfUnitBloch B

theorem bloch_ofBloch (B : UnitBlochCoords) :
    (ofBloch B).bloch = B := by
  exact UnitSpinorCoords.quotientUnitBloch_phaseClassOfUnitBloch B

theorem ofBloch_bloch (ψ : ProjectiveQubitState) :
    ofBloch ψ.bloch = ψ := by
  exact UnitSpinorCoords.phaseClassOfUnitBloch_quotientUnitBloch ψ

/-- Equality of projective qubit states is exactly equality of their Bloch
points. -/
theorem eq_iff_bloch_eq (ψ φ : ProjectiveQubitState) :
    ψ = φ ↔ ψ.bloch = φ.bloch := by
  constructor
  · intro h
    exact congrArg bloch h
  · intro h
    exact UnitSpinorCoords.quotientUnitBloch_injective h

/-- Pauli-X Born probabilities of a projective qubit state. -/
noncomputable def bornX (ψ : ProjectiveQubitState) : BinaryBornPair :=
  ψ.bloch.bornX

/-- Pauli-Y Born probabilities of a projective qubit state. -/
noncomputable def bornY (ψ : ProjectiveQubitState) : BinaryBornPair :=
  ψ.bloch.bornY

/-- Pauli-Z Born probabilities of a projective qubit state. -/
noncomputable def bornZ (ψ : ProjectiveQubitState) : BinaryBornPair :=
  ψ.bloch.bornZ

/-- Arbitrary-axis Born probabilities of a projective qubit state. -/
noncomputable def bornAlong
    (ψ : ProjectiveQubitState) (A : UnitBlochAxis) : BinaryBornPair :=
  A.bornAlong ψ.bloch

/-- Equality of the three Pauli-axis Born probability pairs. -/
def SamePauliBornData (ψ φ : ProjectiveQubitState) : Prop :=
  ψ.bornX = φ.bornX ∧
  ψ.bornY = φ.bornY ∧
  ψ.bornZ = φ.bornZ

/-- Equality of all arbitrary-axis Born probability pairs. -/
def SameAllAxisBornData (ψ φ : ProjectiveQubitState) : Prop :=
  ∀ A : UnitBlochAxis, ψ.bornAlong A = φ.bornAlong A

/-- The Bloch point reconstructed from a state's three Pauli Born expectations. -/
noncomputable def reconstructedBloch
    (ψ : ProjectiveQubitState) : UnitBlochCoords where
  x := ψ.bornX.expectation
  y := ψ.bornY.expectation
  z := ψ.bornZ.expectation
  unit := by
    rw [
      bornX,
      bornY,
      bornZ,
      UnitBlochCoords.bornX_expectation_eq_x,
      UnitBlochCoords.bornY_expectation_eq_y,
      UnitBlochCoords.bornZ_expectation_eq_z]
    exact ψ.bloch.unit

theorem bornX_expectation_eq_bloch_x (ψ : ProjectiveQubitState) :
    ψ.bornX.expectation = ψ.bloch.x := by
  exact UnitBlochCoords.bornX_expectation_eq_x ψ.bloch

theorem bornY_expectation_eq_bloch_y (ψ : ProjectiveQubitState) :
    ψ.bornY.expectation = ψ.bloch.y := by
  exact UnitBlochCoords.bornY_expectation_eq_y ψ.bloch

theorem bornZ_expectation_eq_bloch_z (ψ : ProjectiveQubitState) :
    ψ.bornZ.expectation = ψ.bloch.z := by
  exact UnitBlochCoords.bornZ_expectation_eq_z ψ.bloch

theorem bornAlong_expectation_eq_dot
    (ψ : ProjectiveQubitState) (A : UnitBlochAxis) :
    (ψ.bornAlong A).expectation = A.dot ψ.bloch := by
  exact UnitBlochAxis.bornAlong_expectation_eq_dot A ψ.bloch

theorem reconstructedBloch_eq_bloch (ψ : ProjectiveQubitState) :
    ψ.reconstructedBloch = ψ.bloch := by
  apply UnitBlochCoords.ext_coords
  · exact bornX_expectation_eq_bloch_x ψ
  · exact bornY_expectation_eq_bloch_y ψ
  · exact bornZ_expectation_eq_bloch_z ψ

/-- The projective qubit state reconstructed from Pauli Born expectations. -/
noncomputable def reconstructedState
    (ψ : ProjectiveQubitState) : ProjectiveQubitState :=
  ofBloch ψ.reconstructedBloch

theorem reconstructedState_eq (ψ : ProjectiveQubitState) :
    ψ.reconstructedState = ψ := by
  unfold reconstructedState
  rw [reconstructedBloch_eq_bloch]
  exact ofBloch_bloch ψ

theorem samePauliBornData_of_eq
    {ψ φ : ProjectiveQubitState} (h : ψ = φ) :
    SamePauliBornData ψ φ := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem bloch_eq_of_samePauliBornData
    {ψ φ : ProjectiveQubitState}
    (h : SamePauliBornData ψ φ) :
    ψ.bloch = φ.bloch := by
  rcases h with ⟨hX, hY, hZ⟩
  apply UnitBlochCoords.ext_coords
  · calc
      ψ.bloch.x = ψ.bornX.expectation :=
        (bornX_expectation_eq_bloch_x ψ).symm
      _ = φ.bornX.expectation :=
        congrArg BinaryBornPair.expectation hX
      _ = φ.bloch.x :=
        bornX_expectation_eq_bloch_x φ
  · calc
      ψ.bloch.y = ψ.bornY.expectation :=
        (bornY_expectation_eq_bloch_y ψ).symm
      _ = φ.bornY.expectation :=
        congrArg BinaryBornPair.expectation hY
      _ = φ.bloch.y :=
        bornY_expectation_eq_bloch_y φ
  · calc
      ψ.bloch.z = ψ.bornZ.expectation :=
        (bornZ_expectation_eq_bloch_z ψ).symm
      _ = φ.bornZ.expectation :=
        congrArg BinaryBornPair.expectation hZ
      _ = φ.bloch.z :=
        bornZ_expectation_eq_bloch_z φ

theorem eq_of_samePauliBornData
    {ψ φ : ProjectiveQubitState}
    (h : SamePauliBornData ψ φ) :
    ψ = φ := by
  exact (eq_iff_bloch_eq ψ φ).mpr (bloch_eq_of_samePauliBornData h)

theorem samePauliBornData_iff_eq (ψ φ : ProjectiveQubitState) :
    SamePauliBornData ψ φ ↔ ψ = φ := by
  constructor
  · exact eq_of_samePauliBornData
  · exact samePauliBornData_of_eq

theorem sameAllAxisBornData_of_eq
    {ψ φ : ProjectiveQubitState} (h : ψ = φ) :
    SameAllAxisBornData ψ φ := by
  subst h
  intro A
  rfl

theorem samePauliBornData_of_sameAllAxisBornData
    {ψ φ : ProjectiveQubitState}
    (h : SameAllAxisBornData ψ φ) :
    SamePauliBornData ψ φ := by
  unfold SamePauliBornData
  exact
    ⟨by
      calc
        ψ.bornX = ψ.bornAlong UnitBlochAxis.pauliX := by
          simp [bornAlong, bornX, UnitBlochAxis.pauliX_bornAlong_eq_bornX]
        _ = φ.bornAlong UnitBlochAxis.pauliX :=
          h UnitBlochAxis.pauliX
        _ = φ.bornX := by
          simp [bornAlong, bornX, UnitBlochAxis.pauliX_bornAlong_eq_bornX],
      by
      calc
        ψ.bornY = ψ.bornAlong UnitBlochAxis.pauliY := by
          simp [bornAlong, bornY, UnitBlochAxis.pauliY_bornAlong_eq_bornY]
        _ = φ.bornAlong UnitBlochAxis.pauliY :=
          h UnitBlochAxis.pauliY
        _ = φ.bornY := by
          simp [bornAlong, bornY, UnitBlochAxis.pauliY_bornAlong_eq_bornY],
      by
      calc
        ψ.bornZ = ψ.bornAlong UnitBlochAxis.pauliZ := by
          simp [bornAlong, bornZ, UnitBlochAxis.pauliZ_bornAlong_eq_bornZ]
        _ = φ.bornAlong UnitBlochAxis.pauliZ :=
          h UnitBlochAxis.pauliZ
        _ = φ.bornZ := by
          simp [bornAlong, bornZ, UnitBlochAxis.pauliZ_bornAlong_eq_bornZ]⟩

theorem eq_of_sameAllAxisBornData
    {ψ φ : ProjectiveQubitState}
    (h : SameAllAxisBornData ψ φ) :
    ψ = φ :=
  eq_of_samePauliBornData (samePauliBornData_of_sameAllAxisBornData h)

theorem sameAllAxisBornData_iff_eq (ψ φ : ProjectiveQubitState) :
    SameAllAxisBornData ψ φ ↔ ψ = φ := by
  constructor
  · exact eq_of_sameAllAxisBornData
  · exact sameAllAxisBornData_of_eq

/-- Bundled finite projective-qubit interface theorem. -/
theorem projective_qubit_state_interface
    (ψ φ : ProjectiveQubitState) :
    ψ.reconstructedState = ψ ∧
    (SamePauliBornData ψ φ ↔ ψ = φ) ∧
    (SameAllAxisBornData ψ φ ↔ ψ = φ) ∧
    (ψ.bloch = φ.bloch ↔ ψ = φ) := by
  exact
    ⟨reconstructedState_eq ψ,
      samePauliBornData_iff_eq ψ φ,
      sameAllAxisBornData_iff_eq ψ φ,
      (eq_iff_bloch_eq ψ φ).symm⟩

#print axioms ProjectiveQubitState.reconstructedState_eq
#print axioms ProjectiveQubitState.samePauliBornData_iff_eq
#print axioms ProjectiveQubitState.sameAllAxisBornData_iff_eq
#print axioms ProjectiveQubitState.projective_qubit_state_interface

end ProjectiveQubitState

end UnifiedTheory.Audit.KFHopfProjectiveQubitState
