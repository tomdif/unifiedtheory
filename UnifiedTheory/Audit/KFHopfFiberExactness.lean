/-
  Audit/KFHopfFiberExactness.lean

  Algebraic exactness of the Hopf fibers on normalized spinors.

  Earlier Hopf modules prove that normalized spinor phase classes carry a
  well-defined unit Bloch observable.  This file proves the converse at the
  same set-level algebraic scope:

  * if two normalized spinors have the same Bloch point, then they differ by a
    common unit phase;
  * therefore equality of normalized phase classes is equivalent to equality of
    their unit Bloch observables.

  This is the fiber-exact/injective half of the set-level algebraic quotient.
  Surjectivity onto every unit Bloch point is a separate chart construction,
  not proved here.  This is not a quotient-topology, principal-bundle,
  Chern-class, Hopf-invariant, or continuum spin-bundle theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfUnitSphereQuotient

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfSpinorBlochBridge
open UnifiedTheory.Audit.KFHopfPhaseQuotient

namespace UnifiedTheory.Audit.KFHopfPhaseQuotient.SpinorCoords

/-- Squared norm of the first complex component. -/
def firstComponentNormSq (u : SpinorCoords) : Real :=
  u.a ^ 2 + u.b ^ 2

/-- Squared norm of the second complex component. -/
def secondComponentNormSq (u : SpinorCoords) : Real :=
  u.c ^ 2 + u.d ^ 2

theorem firstComponentNormSq_nonneg (u : SpinorCoords) :
    0 ≤ firstComponentNormSq u := by
  unfold firstComponentNormSq
  nlinarith [sq_nonneg u.a, sq_nonneg u.b]

theorem secondComponentNormSq_nonneg (u : SpinorCoords) :
    0 ≤ secondComponentNormSq u := by
  unfold secondComponentNormSq
  nlinarith [sq_nonneg u.c, sq_nonneg u.d]

end UnifiedTheory.Audit.KFHopfPhaseQuotient.SpinorCoords

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFHopfPhaseQuotient.SpinorCoords

variable (u v : UnitSpinorCoords)

private theorem component_norms_eq_of_unitBloch_eq
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v) :
    v.coords.firstComponentNormSq = u.coords.firstComponentNormSq ∧
    v.coords.secondComponentNormSq = u.coords.secondComponentNormSq := by
  have hz :
      u.coords.a ^ 2 + u.coords.b ^ 2 -
          u.coords.c ^ 2 - u.coords.d ^ 2 =
        v.coords.a ^ 2 + v.coords.b ^ 2 -
          v.coords.c ^ 2 - v.coords.d ^ 2 := by
    simpa [unitBlochOfSpinor, SpinorCoords.blochZ, hopfZ] using
      congrArg UnitBlochCoords.z hB
  have hu :
      u.coords.a ^ 2 + u.coords.b ^ 2 +
          u.coords.c ^ 2 + u.coords.d ^ 2 = 1 := by
    simpa [SpinorCoords.normSq, spinorNormSq] using u.normalized
  have hv :
      v.coords.a ^ 2 + v.coords.b ^ 2 +
          v.coords.c ^ 2 + v.coords.d ^ 2 = 1 := by
    simpa [SpinorCoords.normSq, spinorNormSq] using v.normalized
  constructor
  · unfold SpinorCoords.firstComponentNormSq
    nlinarith
  · unfold SpinorCoords.secondComponentNormSq
    nlinarith

private theorem hopfX_core_eq_of_unitBloch_eq
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v) :
    u.coords.a * u.coords.c + u.coords.b * u.coords.d =
      v.coords.a * v.coords.c + v.coords.b * v.coords.d := by
  have hx :
      2 * (u.coords.a * u.coords.c + u.coords.b * u.coords.d) =
        2 * (v.coords.a * v.coords.c + v.coords.b * v.coords.d) := by
    simpa [unitBlochOfSpinor, SpinorCoords.blochX, hopfX] using
      congrArg UnitBlochCoords.x hB
  nlinarith

private theorem hopfY_core_eq_of_unitBloch_eq
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v) :
    u.coords.a * u.coords.d - u.coords.b * u.coords.c =
      v.coords.a * v.coords.d - v.coords.b * v.coords.c := by
  have hy :
      2 * (u.coords.a * u.coords.d - u.coords.b * u.coords.c) =
        2 * (v.coords.a * v.coords.d - v.coords.b * v.coords.c) := by
    simpa [unitBlochOfSpinor, SpinorCoords.blochY, hopfY] using
      congrArg UnitBlochCoords.y hB
  nlinarith

/-- In the first affine chart, equal Bloch data reconstructs the unique common
phase carrying `u` to `v`. -/
theorem phaseRelated_of_unitBloch_eq_of_firstComponent_pos
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v)
    (hpos : 0 < u.coords.firstComponentNormSq) :
    PhaseRelated u v := by
  have hnorms := component_norms_eq_of_unitBloch_eq u v hB
  have hfirst :
      v.coords.a ^ 2 + v.coords.b ^ 2 =
        u.coords.a ^ 2 + u.coords.b ^ 2 := by
    simpa [SpinorCoords.firstComponentNormSq] using hnorms.1
  have hX := hopfX_core_eq_of_unitBloch_eq u v hB
  have hY := hopfY_core_eq_of_unitBloch_eq u v hB
  have hden :
      u.coords.a ^ 2 + u.coords.b ^ 2 ≠ 0 := by
    exact ne_of_gt (by simpa [SpinorCoords.firstComponentNormSq] using hpos)
  have hc_num :
      (u.coords.a * v.coords.a + u.coords.b * v.coords.b) * u.coords.c -
          (u.coords.a * v.coords.b - u.coords.b * v.coords.a) * u.coords.d =
        v.coords.c * (u.coords.a ^ 2 + u.coords.b ^ 2) := by
    calc
      (u.coords.a * v.coords.a + u.coords.b * v.coords.b) * u.coords.c -
          (u.coords.a * v.coords.b - u.coords.b * v.coords.a) * u.coords.d =
        v.coords.a * (u.coords.a * u.coords.c + u.coords.b * u.coords.d) -
          v.coords.b * (u.coords.a * u.coords.d - u.coords.b * u.coords.c) := by
          ring
      _ =
        v.coords.a * (v.coords.a * v.coords.c + v.coords.b * v.coords.d) -
          v.coords.b * (v.coords.a * v.coords.d - v.coords.b * v.coords.c) := by
          rw [hX, hY]
      _ = v.coords.c * (v.coords.a ^ 2 + v.coords.b ^ 2) := by
          ring
      _ = v.coords.c * (u.coords.a ^ 2 + u.coords.b ^ 2) := by
          rw [hfirst]
  have hd_num :
      (u.coords.a * v.coords.a + u.coords.b * v.coords.b) * u.coords.d +
          (u.coords.a * v.coords.b - u.coords.b * v.coords.a) * u.coords.c =
        v.coords.d * (u.coords.a ^ 2 + u.coords.b ^ 2) := by
    calc
      (u.coords.a * v.coords.a + u.coords.b * v.coords.b) * u.coords.d +
          (u.coords.a * v.coords.b - u.coords.b * v.coords.a) * u.coords.c =
        v.coords.a * (u.coords.a * u.coords.d - u.coords.b * u.coords.c) +
          v.coords.b * (u.coords.a * u.coords.c + u.coords.b * u.coords.d) := by
          ring
      _ =
        v.coords.a * (v.coords.a * v.coords.d - v.coords.b * v.coords.c) +
          v.coords.b * (v.coords.a * v.coords.c + v.coords.b * v.coords.d) := by
          rw [hX, hY]
      _ = v.coords.d * (v.coords.a ^ 2 + v.coords.b ^ 2) := by
          ring
      _ = v.coords.d * (u.coords.a ^ 2 + u.coords.b ^ 2) := by
          rw [hfirst]
  let P : UnitPhase :=
    { p :=
        (u.coords.a * v.coords.a + u.coords.b * v.coords.b) /
          (u.coords.a ^ 2 + u.coords.b ^ 2)
      q :=
        (u.coords.a * v.coords.b - u.coords.b * v.coords.a) /
          (u.coords.a ^ 2 + u.coords.b ^ 2)
      unit := by
        field_simp [hden]
        nlinarith [hfirst] }
  exact
    ⟨P, by
      apply SpinorCoords.ext_coords
      · dsimp [P, SpinorCoords.phaseAct, phaseRe]
        field_simp [hden]
        ring
      · dsimp [P, SpinorCoords.phaseAct, phaseIm]
        field_simp [hden]
        ring
      · dsimp [P, SpinorCoords.phaseAct, phaseRe]
        field_simp [hden]
        nlinarith [hc_num]
      · dsimp [P, SpinorCoords.phaseAct, phaseIm]
        field_simp [hden]
        nlinarith [hd_num]⟩

/-- In the second affine chart, equal Bloch data reconstructs the unique common
phase carrying `u` to `v`. -/
theorem phaseRelated_of_unitBloch_eq_of_secondComponent_pos
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v)
    (hpos : 0 < u.coords.secondComponentNormSq) :
    PhaseRelated u v := by
  have hnorms := component_norms_eq_of_unitBloch_eq u v hB
  have hsecond :
      v.coords.c ^ 2 + v.coords.d ^ 2 =
        u.coords.c ^ 2 + u.coords.d ^ 2 := by
    simpa [SpinorCoords.secondComponentNormSq] using hnorms.2
  have hX := hopfX_core_eq_of_unitBloch_eq u v hB
  have hY := hopfY_core_eq_of_unitBloch_eq u v hB
  have hden :
      u.coords.c ^ 2 + u.coords.d ^ 2 ≠ 0 := by
    exact ne_of_gt (by simpa [SpinorCoords.secondComponentNormSq] using hpos)
  have ha_num :
      (u.coords.c * v.coords.c + u.coords.d * v.coords.d) * u.coords.a -
          (u.coords.c * v.coords.d - u.coords.d * v.coords.c) * u.coords.b =
        v.coords.a * (u.coords.c ^ 2 + u.coords.d ^ 2) := by
    calc
      (u.coords.c * v.coords.c + u.coords.d * v.coords.d) * u.coords.a -
          (u.coords.c * v.coords.d - u.coords.d * v.coords.c) * u.coords.b =
        v.coords.c * (u.coords.a * u.coords.c + u.coords.b * u.coords.d) +
          v.coords.d * (u.coords.a * u.coords.d - u.coords.b * u.coords.c) := by
          ring
      _ =
        v.coords.c * (v.coords.a * v.coords.c + v.coords.b * v.coords.d) +
          v.coords.d * (v.coords.a * v.coords.d - v.coords.b * v.coords.c) := by
          rw [hX, hY]
      _ = v.coords.a * (v.coords.c ^ 2 + v.coords.d ^ 2) := by
          ring
      _ = v.coords.a * (u.coords.c ^ 2 + u.coords.d ^ 2) := by
          rw [hsecond]
  have hb_num :
      (u.coords.c * v.coords.c + u.coords.d * v.coords.d) * u.coords.b +
          (u.coords.c * v.coords.d - u.coords.d * v.coords.c) * u.coords.a =
        v.coords.b * (u.coords.c ^ 2 + u.coords.d ^ 2) := by
    calc
      (u.coords.c * v.coords.c + u.coords.d * v.coords.d) * u.coords.b +
          (u.coords.c * v.coords.d - u.coords.d * v.coords.c) * u.coords.a =
        v.coords.d * (u.coords.a * u.coords.c + u.coords.b * u.coords.d) -
          v.coords.c * (u.coords.a * u.coords.d - u.coords.b * u.coords.c) := by
          ring
      _ =
        v.coords.d * (v.coords.a * v.coords.c + v.coords.b * v.coords.d) -
          v.coords.c * (v.coords.a * v.coords.d - v.coords.b * v.coords.c) := by
          rw [hX, hY]
      _ = v.coords.b * (v.coords.c ^ 2 + v.coords.d ^ 2) := by
          ring
      _ = v.coords.b * (u.coords.c ^ 2 + u.coords.d ^ 2) := by
          rw [hsecond]
  let P : UnitPhase :=
    { p :=
        (u.coords.c * v.coords.c + u.coords.d * v.coords.d) /
          (u.coords.c ^ 2 + u.coords.d ^ 2)
      q :=
        (u.coords.c * v.coords.d - u.coords.d * v.coords.c) /
          (u.coords.c ^ 2 + u.coords.d ^ 2)
      unit := by
        field_simp [hden]
        nlinarith [hsecond] }
  exact
    ⟨P, by
      apply SpinorCoords.ext_coords
      · dsimp [P, SpinorCoords.phaseAct, phaseRe]
        field_simp [hden]
        nlinarith [ha_num]
      · dsimp [P, SpinorCoords.phaseAct, phaseIm]
        field_simp [hden]
        nlinarith [hb_num]
      · dsimp [P, SpinorCoords.phaseAct, phaseRe]
        field_simp [hden]
        ring
      · dsimp [P, SpinorCoords.phaseAct, phaseIm]
        field_simp [hden]
        ring⟩

/-- Equal unit Bloch observables have exactly one algebraic meaning upstairs:
the normalized spinors differ by a common unit phase. -/
theorem phaseRelated_of_unitBloch_eq
    (hB : unitBlochOfSpinor u = unitBlochOfSpinor v) :
    PhaseRelated u v := by
  by_cases hfirst : 0 < u.coords.firstComponentNormSq
  · exact phaseRelated_of_unitBloch_eq_of_firstComponent_pos u v hB hfirst
  · have hfirst_nonneg : 0 ≤ u.coords.firstComponentNormSq :=
      SpinorCoords.firstComponentNormSq_nonneg u.coords
    have hfirst_zero : u.coords.firstComponentNormSq = 0 := by
      exact le_antisymm (le_of_not_gt hfirst) hfirst_nonneg
    have hu :
        u.coords.firstComponentNormSq + u.coords.secondComponentNormSq = 1 := by
      have hu_raw :
          u.coords.a ^ 2 + u.coords.b ^ 2 +
              u.coords.c ^ 2 + u.coords.d ^ 2 = 1 := by
        simpa [SpinorCoords.normSq, spinorNormSq] using u.normalized
      unfold SpinorCoords.firstComponentNormSq
        SpinorCoords.secondComponentNormSq
      nlinarith
    have hsecond : 0 < u.coords.secondComponentNormSq := by
      nlinarith
    exact phaseRelated_of_unitBloch_eq_of_secondComponent_pos u v hB hsecond

/-- Phase related normalized spinors have the same unit Bloch observable. -/
theorem unitBloch_eq_of_phaseRelated {u v : UnitSpinorCoords}
    (h : PhaseRelated u v) :
    unitBlochOfSpinor u = unitBlochOfSpinor v :=
  unitBlochOfSpinor_eq_of_phaseRelated h

/-- On normalized spinors, the Hopf/Bloch observable is exactly the phase
quotient relation. -/
theorem unitBloch_eq_iff_phaseRelated :
    unitBlochOfSpinor u = unitBlochOfSpinor v ↔ PhaseRelated u v := by
  constructor
  · exact phaseRelated_of_unitBloch_eq u v
  · exact unitBloch_eq_of_phaseRelated

/-- The quotient map from normalized phase classes to the unit Bloch sphere is
injective: algebraically, `S^3 / U(1)` has no extra finite identifications
beyond the Hopf fibers. -/
theorem quotientUnitBloch_injective :
    Function.Injective quotientUnitBloch := by
  intro q r hB
  revert r
  refine Quot.inductionOn q ?_
  intro u r hB
  revert hB
  refine Quot.inductionOn r ?_
  intro v hBuv
  exact Quot.sound (phaseRelated_of_unitBloch_eq u v hBuv)

/-- Bundled set-level exactness theorem for the algebraic Hopf quotient. -/
theorem unit_hopf_quotient_to_bloch_sphere_exact
    (q r : UnitPhaseSpinorQuotient) :
    quotientUnitBloch q = quotientUnitBloch r ↔ q = r := by
  constructor
  · intro h
    exact quotientUnitBloch_injective h
  · intro h
    exact congrArg quotientUnitBloch h

#print axioms UnitSpinorCoords.phaseRelated_of_unitBloch_eq
#print axioms UnitSpinorCoords.unitBloch_eq_iff_phaseRelated
#print axioms UnitSpinorCoords.quotientUnitBloch_injective
#print axioms UnitSpinorCoords.unit_hopf_quotient_to_bloch_sphere_exact

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords
