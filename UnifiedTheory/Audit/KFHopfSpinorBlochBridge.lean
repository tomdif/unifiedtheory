/-
  Audit/KFHopfSpinorBlochBridge.lean

  Algebraic Hopf bridge between the repo's spinor/qubit and Bloch/projective
  sides.

  Existing files already contain adjacent ingredients:

  * `LayerB/BellTheorem.lean` uses two-component spin states from SU(2);
  * `LayerB/BlochO3Classification.lean` uses Bloch-sphere/projective qubit
    geometry;
  * `LayerA/DiscreteBundles.lean` and `LayerA/GaugeConnection.lean` expose the
    principal-bundle/gauge-language side.

  This file supplies the algebraic core of the Hopf map in real coordinates.
  A spinor `(a + ib, c + id)` is sent to the Bloch vector

    (2(ac+bd), 2(ad-bc), a^2+b^2-c^2-d^2).

  Lean proves:

  * these coordinates agree with the repo's `WignerHardQubit.blochVector`;
  * the Bloch norm squared is the square of the spinor norm squared;
  * a unit spinor therefore maps to a unit Bloch vector;
  * multiplying both spinor components by the same unit phase leaves the Bloch
    vector unchanged.

  This is not yet the full topological Hopf fibration: no quotient topology,
  local trivialization, Chern class, or Hopf invariant is claimed here.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Tactic
import UnifiedTheory.LayerB.WignerHardQubit

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFHopfSpinorBlochBridge

open UnifiedTheory.LayerB.WignerHardQubit

/-- Squared norm of the two-component complex spinor `(a + ib, c + id)`,
written in real coordinates. -/
def spinorNormSq (a b c d : Real) : Real :=
  a^2 + b^2 + c^2 + d^2

/-- First Bloch coordinate of the algebraic Hopf map. -/
def hopfX (a b c d : Real) : Real :=
  2 * (a * c + b * d)

/-- Second Bloch coordinate of the algebraic Hopf map. -/
def hopfY (a b c d : Real) : Real :=
  2 * (a * d - b * c)

/-- Third Bloch coordinate of the algebraic Hopf map. -/
def hopfZ (a b c d : Real) : Real :=
  a^2 + b^2 - c^2 - d^2

/-- Squared Euclidean norm of the Hopf/Bloch vector. -/
def blochNormSq (a b c d : Real) : Real :=
  hopfX a b c d ^ 2 + hopfY a b c d ^ 2 + hopfZ a b c d ^ 2

/-- The repo qubit spinor `(a + ib, c + id)` written in real coordinates. -/
noncomputable def spinorOfCoords (a b c d : Real) : Fin 2 → Complex :=
  fun i =>
    if i = 0 then
      ((a : Real) : Complex) + Complex.I * ((b : Real) : Complex)
    else
      ((c : Real) : Complex) + Complex.I * ((d : Real) : Complex)

@[simp] theorem spinorOfCoords_zero (a b c d : Real) :
    spinorOfCoords a b c d 0 =
      ((a : Real) : Complex) + Complex.I * ((b : Real) : Complex) := by
  simp [spinorOfCoords]

@[simp] theorem spinorOfCoords_one (a b c d : Real) :
    spinorOfCoords a b c d 1 =
      ((c : Real) : Complex) + Complex.I * ((d : Real) : Complex) := by
  simp [spinorOfCoords]

/-- The first real-coordinate Hopf coordinate agrees with the repo's
`WignerHardQubit.blochVector` on `(a+ib,c+id)`. -/
theorem repo_blochVector_zero_eq_hopfX (a b c d : Real) :
    blochVector (spinorOfCoords a b c d) 0 = hopfX a b c d := by
  rw [blochVector_zero]
  simp [spinorOfCoords, hopfX]

/-- The second real-coordinate Hopf coordinate agrees with the repo's
`WignerHardQubit.blochVector` on `(a+ib,c+id)`. -/
theorem repo_blochVector_one_eq_hopfY (a b c d : Real) :
    blochVector (spinorOfCoords a b c d) 1 = hopfY a b c d := by
  rw [blochVector_one]
  simp [spinorOfCoords, hopfY]
  ring

/-- The third real-coordinate Hopf coordinate agrees with the repo's
`WignerHardQubit.blochVector` on `(a+ib,c+id)`. -/
theorem repo_blochVector_two_eq_hopfZ (a b c d : Real) :
    blochVector (spinorOfCoords a b c d) 2 = hopfZ a b c d := by
  rw [blochVector_two]
  simp [spinorOfCoords, hopfZ, Complex.normSq]
  ring

/-- The algebraic Hopf map is exactly the repo's unnormalised Bloch vector on
the real-coordinate spinor `(a+ib,c+id)`. -/
theorem repo_blochVector_eq_hopf (a b c d : Real) :
    blochVector (spinorOfCoords a b c d) 0 = hopfX a b c d ∧
    blochVector (spinorOfCoords a b c d) 1 = hopfY a b c d ∧
    blochVector (spinorOfCoords a b c d) 2 = hopfZ a b c d := by
  exact
    ⟨repo_blochVector_zero_eq_hopfX a b c d,
      repo_blochVector_one_eq_hopfY a b c d,
      repo_blochVector_two_eq_hopfZ a b c d⟩

/-- The algebraic Hopf identity: the Bloch vector has norm
`||psi||^2` squared. -/
theorem hopf_bloch_normSq (a b c d : Real) :
    blochNormSq a b c d = spinorNormSq a b c d ^ 2 := by
  unfold blochNormSq hopfX hopfY hopfZ spinorNormSq
  ring

/-- A normalized spinor maps to the unit Bloch sphere. -/
theorem hopf_unit_spinor_unit_bloch
    (a b c d : Real)
    (hunit : spinorNormSq a b c d = 1) :
    blochNormSq a b c d = 1 := by
  rw [hopf_bloch_normSq, hunit]
  norm_num

/-- Real part of multiplying `x + iy` by the phase `p + iq`. -/
def phaseRe (p q x y : Real) : Real :=
  p * x - q * y

/-- Imaginary part of multiplying `x + iy` by the phase `p + iq`. -/
def phaseIm (p q x y : Real) : Real :=
  p * y + q * x

/-- A unit phase preserves the squared norm of one complex component. -/
theorem phase_preserves_component_normSq
    (p q x y : Real)
    (hphase : p^2 + q^2 = 1) :
    phaseRe p q x y ^ 2 + phaseIm p q x y ^ 2 = x^2 + y^2 := by
  unfold phaseRe phaseIm
  nlinarith [hphase]

/-- A unit phase preserves the squared norm of the two-component spinor. -/
theorem phase_preserves_spinorNormSq
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1) :
    spinorNormSq
        (phaseRe p q a b) (phaseIm p q a b)
        (phaseRe p q c d) (phaseIm p q c d) =
      spinorNormSq a b c d := by
  unfold spinorNormSq phaseRe phaseIm
  nlinarith [hphase]

/-- Predicate saying the algebraic Hopf/Bloch vector is unchanged by a common
unit phase on both spinor components. -/
def hopfPhaseInvariant (p q a b c d : Real) : Prop :=
  hopfX
      (phaseRe p q a b) (phaseIm p q a b)
      (phaseRe p q c d) (phaseIm p q c d) =
    hopfX a b c d ∧
  hopfY
      (phaseRe p q a b) (phaseIm p q a b)
      (phaseRe p q c d) (phaseIm p q c d) =
    hopfY a b c d ∧
  hopfZ
      (phaseRe p q a b) (phaseIm p q a b)
      (phaseRe p q c d) (phaseIm p q c d) =
    hopfZ a b c d

/-- The first Hopf/Bloch coordinate is invariant under a common unit phase. -/
theorem hopfX_phase_invariant
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1) :
    hopfX
        (phaseRe p q a b) (phaseIm p q a b)
        (phaseRe p q c d) (phaseIm p q c d) =
      hopfX a b c d := by
  have hp2 : p^2 = 1 - q^2 := by
    nlinarith [hphase]
  unfold hopfX phaseRe phaseIm
  ring_nf
  rw [hp2]
  ring

/-- The second Hopf/Bloch coordinate is invariant under a common unit phase. -/
theorem hopfY_phase_invariant
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1) :
    hopfY
        (phaseRe p q a b) (phaseIm p q a b)
        (phaseRe p q c d) (phaseIm p q c d) =
      hopfY a b c d := by
  have hp2 : p^2 = 1 - q^2 := by
    nlinarith [hphase]
  unfold hopfY phaseRe phaseIm
  ring_nf
  rw [hp2]
  ring

/-- The third Hopf/Bloch coordinate is invariant under a common unit phase. -/
theorem hopfZ_phase_invariant
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1) :
    hopfZ
        (phaseRe p q a b) (phaseIm p q a b)
        (phaseRe p q c d) (phaseIm p q c d) =
      hopfZ a b c d := by
  unfold hopfZ phaseRe phaseIm
  nlinarith [hphase]

/-- The algebraic Hopf map factors through the common unit-phase quotient:
all three Bloch coordinates are unchanged by the same phase on both spinor
components. -/
theorem hopf_phase_invariant
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1) :
    hopfPhaseInvariant p q a b c d := by
  unfold hopfPhaseInvariant
  exact
    ⟨hopfX_phase_invariant p q a b c d hphase,
      hopfY_phase_invariant p q a b c d hphase,
      hopfZ_phase_invariant p q a b c d hphase⟩

/-- A bundled statement exposing the exact bridge in one theorem: normalized
spinors map to the unit Bloch sphere and the map is insensitive to common
unit phase. -/
theorem hopf_spinor_bloch_bridge
    (p q a b c d : Real)
    (hphase : p^2 + q^2 = 1)
    (hunit : spinorNormSq a b c d = 1) :
    blochNormSq a b c d = 1 ∧
    spinorNormSq
        (phaseRe p q a b) (phaseIm p q a b)
        (phaseRe p q c d) (phaseIm p q c d) = 1 ∧
    hopfPhaseInvariant p q a b c d := by
  exact
    ⟨hopf_unit_spinor_unit_bloch a b c d hunit,
      by rw [phase_preserves_spinorNormSq p q a b c d hphase, hunit],
      hopf_phase_invariant p q a b c d hphase⟩

#print axioms hopf_bloch_normSq
#print axioms hopf_unit_spinor_unit_bloch
#print axioms repo_blochVector_eq_hopf
#print axioms phase_preserves_spinorNormSq
#print axioms hopf_phase_invariant
#print axioms hopf_spinor_bloch_bridge

end UnifiedTheory.Audit.KFHopfSpinorBlochBridge
