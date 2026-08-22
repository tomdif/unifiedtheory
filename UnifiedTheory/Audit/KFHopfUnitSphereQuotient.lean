/-
  Audit/KFHopfUnitSphereQuotient.lean

  Unit Hopf quotient landing in the unit Bloch sphere.

  `KFHopfPhaseQuotient` names the algebraic common-phase quotient on
  real-coordinate spinors.  This file restricts that quotient to normalized
  spinors and proves that the quotient Bloch observable lands in the unit
  two-sphere.

  This is the set-level/algebraic core usually drawn as

      S^3 / U(1) -> S^2.

  It is still not a topological Hopf fibration theorem: no quotient topology,
  local trivialization, smooth bundle, Chern class, or Hopf invariant is claimed.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfPhaseQuotient

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient

open UnifiedTheory.Audit.KFHopfSpinorBlochBridge
open UnifiedTheory.Audit.KFHopfPhaseQuotient

/-- A normalized two-component spinor in real coordinates. -/
structure UnitSpinorCoords where
  coords : SpinorCoords
  normalized : coords.normSq = 1

/-- A point of the unit Bloch sphere, in real coordinates. -/
structure UnitBlochCoords where
  x : Real
  y : Real
  z : Real
  unit : x ^ 2 + y ^ 2 + z ^ 2 = 1

namespace UnitBlochCoords

@[ext] theorem ext_coords {u v : UnitBlochCoords}
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) :
    u = v := by
  cases u
  cases v
  simp_all

end UnitBlochCoords

namespace UnitSpinorCoords

/-- The repo qubit spinor represented by a normalized real-coordinate spinor. -/
noncomputable def spinor (u : UnitSpinorCoords) : Fin 2 → Complex :=
  spinorOfCoords u.coords.a u.coords.b u.coords.c u.coords.d

/-- Phase equivalence restricted to normalized spinors. -/
def PhaseRelated (u v : UnitSpinorCoords) : Prop :=
  SpinorCoords.PhaseRelated u.coords v.coords

theorem phaseRelated_refl (u : UnitSpinorCoords) :
    PhaseRelated u u := by
  exact SpinorCoords.phaseRelated_refl u.coords

theorem phaseRelated_symm {u v : UnitSpinorCoords}
    (h : PhaseRelated u v) :
    PhaseRelated v u := by
  exact SpinorCoords.phaseRelated_symm h

theorem phaseRelated_trans {u v w : UnitSpinorCoords}
    (huv : PhaseRelated u v)
    (hvw : PhaseRelated v w) :
    PhaseRelated u w := by
  exact SpinorCoords.phaseRelated_trans huv hvw

/-- The normalized spinor phase quotient as a Lean setoid. -/
def phaseSetoid : Setoid UnitSpinorCoords where
  r := PhaseRelated
  iseqv := ⟨phaseRelated_refl, phaseRelated_symm, phaseRelated_trans⟩

/-- The Bloch point associated to a normalized spinor. -/
noncomputable def unitBlochOfSpinor (u : UnitSpinorCoords) :
    UnitBlochCoords where
  x := u.coords.blochX
  y := u.coords.blochY
  z := u.coords.blochZ
  unit := by
    have hunit :
        spinorNormSq u.coords.a u.coords.b u.coords.c u.coords.d = 1 := by
      simpa [SpinorCoords.normSq] using u.normalized
    have hb :=
      hopf_unit_spinor_unit_bloch
        u.coords.a u.coords.b u.coords.c u.coords.d hunit
    simpa [
      SpinorCoords.blochX,
      SpinorCoords.blochY,
      SpinorCoords.blochZ,
      KFHopfSpinorBlochBridge.blochNormSq
    ] using hb

/-- The unit Bloch point is constant on normalized phase-equivalence classes. -/
theorem unitBlochOfSpinor_eq_of_phaseRelated {u v : UnitSpinorCoords}
    (h : PhaseRelated u v) :
    unitBlochOfSpinor u = unitBlochOfSpinor v := by
  apply UnitBlochCoords.ext_coords
  · exact (SpinorCoords.phaseRelated_blochX_eq h).symm
  · exact (SpinorCoords.phaseRelated_blochY_eq h).symm
  · exact (SpinorCoords.phaseRelated_blochZ_eq h).symm

/-- The associated repo Bloch vector agrees with the unit Bloch coordinates. -/
theorem repo_blochVector_eq_unitBloch
    (u : UnitSpinorCoords) :
    UnifiedTheory.LayerB.WignerHardQubit.blochVector u.spinor 0 =
        (unitBlochOfSpinor u).x ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector u.spinor 1 =
        (unitBlochOfSpinor u).y ∧
    UnifiedTheory.LayerB.WignerHardQubit.blochVector u.spinor 2 =
        (unitBlochOfSpinor u).z := by
  simpa [
    spinor,
    unitBlochOfSpinor,
    SpinorCoords.blochX,
    SpinorCoords.blochY,
    SpinorCoords.blochZ
  ] using
    repo_blochVector_eq_hopf
      u.coords.a u.coords.b u.coords.c u.coords.d

/-- The normalized algebraic phase quotient. -/
def UnitPhaseSpinorQuotient : Type :=
  Quot phaseSetoid

/-- The well-defined Bloch-sphere point carried by a normalized phase class. -/
noncomputable def quotientUnitBloch :
    UnitPhaseSpinorQuotient → UnitBlochCoords :=
  Quot.lift unitBlochOfSpinor (by
    intro u v h
    exact unitBlochOfSpinor_eq_of_phaseRelated h)

@[simp] theorem quotientUnitBloch_mk (u : UnitSpinorCoords) :
    quotientUnitBloch (Quot.mk phaseSetoid u) = unitBlochOfSpinor u :=
  rfl

/-- The quotient observable lands on the unit Bloch sphere. -/
theorem quotientUnitBloch_unit
    (q : UnitPhaseSpinorQuotient) :
    (quotientUnitBloch q).x ^ 2 +
        (quotientUnitBloch q).y ^ 2 +
        (quotientUnitBloch q).z ^ 2 = 1 := by
  exact (quotientUnitBloch q).unit

/-- Bundled algebraic Hopf quotient statement: normalized spinor phase classes
carry a well-defined unit Bloch observable. -/
theorem unit_hopf_quotient_to_bloch_sphere
    (q : UnitPhaseSpinorQuotient) :
    ∃ B : UnitBlochCoords, quotientUnitBloch q = B ∧
      B.x ^ 2 + B.y ^ 2 + B.z ^ 2 = 1 := by
  exact ⟨quotientUnitBloch q, rfl, quotientUnitBloch_unit q⟩

#print axioms UnitSpinorCoords.phaseSetoid
#print axioms UnitSpinorCoords.unitBlochOfSpinor
#print axioms UnitSpinorCoords.unitBlochOfSpinor_eq_of_phaseRelated
#print axioms UnitSpinorCoords.repo_blochVector_eq_unitBloch
#print axioms UnitSpinorCoords.quotientUnitBloch
#print axioms UnitSpinorCoords.unit_hopf_quotient_to_bloch_sphere

end UnitSpinorCoords

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient
