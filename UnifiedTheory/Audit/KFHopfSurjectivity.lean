/-
  Audit/KFHopfSurjectivity.lean

  Set-level algebraic surjectivity of the Hopf quotient map.

  `KFHopfFiberExactness` proves that the normalized phase quotient has exact
  fibers: equal unit Bloch observables are exactly common-`U(1)` phase related
  normalized spinors.  This file proves the other set-level half:

  * every unit Bloch point has a normalized spinor representative;
  * therefore the normalized phase-quotient-to-Bloch map is bijective as a
    set-level algebraic map.

  The proof uses the usual north chart away from `z = -1` and the explicit
  south-pole representative at `z = -1`.  This is still not a quotient-topology,
  principal-bundle, Chern-class, Hopf-invariant, or continuum spin-bundle
  theorem.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFHopfFiberExactness

set_option autoImplicit false

open UnifiedTheory.Audit.KFHopfSpinorBlochBridge
open UnifiedTheory.Audit.KFHopfPhaseQuotient

namespace UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient

private theorem unitBloch_z_sq_le_one (B : UnitBlochCoords) :
    B.z ^ 2 ≤ 1 := by
  nlinarith [B.unit, sq_nonneg B.x, sq_nonneg B.y]

private theorem unitBloch_neg_one_le_z (B : UnitBlochCoords) :
    -1 ≤ B.z := by
  have hz := unitBloch_z_sq_le_one B
  nlinarith [sq_nonneg (B.z + 1)]

private theorem unitBloch_south_coords
    (B : UnitBlochCoords) (hz : B.z = -1) :
    B.x = 0 ∧ B.y = 0 := by
  have hunit : B.x ^ 2 + B.y ^ 2 + B.z ^ 2 = 1 := B.unit
  rw [hz] at hunit
  have hx2 : B.x ^ 2 = 0 := by
    nlinarith [hunit, sq_nonneg B.x, sq_nonneg B.y]
  have hy2 : B.y ^ 2 = 0 := by
    nlinarith [hunit, sq_nonneg B.x, sq_nonneg B.y]
  exact ⟨sq_eq_zero_iff.mp hx2, sq_eq_zero_iff.mp hy2⟩

/-- The explicit south-pole spinor representative. -/
def southPoleSpinor : UnitSpinorCoords where
  coords := { a := 0, b := 0, c := 0, d := 1 }
  normalized := by
    simp [SpinorCoords.normSq, spinorNormSq]

theorem unitBlochOfSpinor_southPole :
    unitBlochOfSpinor southPoleSpinor =
      ({ x := 0, y := 0, z := -1, unit := by norm_num } : UnitBlochCoords) := by
  apply UnitBlochCoords.ext_coords <;>
    simp [southPoleSpinor, unitBlochOfSpinor, SpinorCoords.blochX,
      SpinorCoords.blochY, SpinorCoords.blochZ, hopfX, hopfY, hopfZ]

theorem exists_unitSpinor_of_unitBloch_south
    (B : UnitBlochCoords) (hz : B.z = -1) :
    ∃ u : UnitSpinorCoords, unitBlochOfSpinor u = B := by
  have hxy := unitBloch_south_coords B hz
  refine ⟨southPoleSpinor, ?_⟩
  apply UnitBlochCoords.ext_coords
  · simpa [unitBlochOfSpinor_southPole] using hxy.1.symm
  · simpa [unitBlochOfSpinor_southPole] using hxy.2.symm
  · simpa [unitBlochOfSpinor_southPole] using hz.symm

/-- Away from the south pole, the usual north chart gives a normalized spinor
representative of the unit Bloch point. -/
theorem exists_unitSpinor_of_unitBloch_north
    (B : UnitBlochCoords) (hz_ne : B.z ≠ -1) :
    ∃ u : UnitSpinorCoords, unitBlochOfSpinor u = B := by
  have hz_ge : -1 ≤ B.z := unitBloch_neg_one_le_z B
  have hzp : 0 < 1 + B.z := by
    have hlt : -1 < B.z := by
      exact lt_of_le_of_ne hz_ge (by intro h; exact hz_ne h.symm)
    linarith
  let a : Real := Real.sqrt ((1 + B.z) / 2)
  have ht_nonneg : 0 ≤ (1 + B.z) / 2 := by linarith
  have ht_pos : 0 < (1 + B.z) / 2 := by linarith
  have ha_sq : a ^ 2 = (1 + B.z) / 2 := by
    dsimp [a]
    exact Real.sq_sqrt ht_nonneg
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr ht_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hxy : B.x ^ 2 + B.y ^ 2 + B.z ^ 2 = 1 := B.unit
  let candidate : UnitSpinorCoords :=
    { coords :=
        { a := a
          b := 0
          c := B.x / (2 * a)
          d := B.y / (2 * a) }
      normalized := by
        show spinorNormSq a 0 (B.x / (2 * a)) (B.y / (2 * a)) = 1
        unfold spinorNormSq
        field_simp [ha_ne]
        nlinarith [hxy, ha_sq] }
  refine ⟨candidate, ?_⟩
  apply UnitBlochCoords.ext_coords
  · show hopfX a 0 (B.x / (2 * a)) (B.y / (2 * a)) = B.x
    unfold hopfX
    field_simp [ha_ne]
    ring
  · show hopfY a 0 (B.x / (2 * a)) (B.y / (2 * a)) = B.y
    unfold hopfY
    field_simp [ha_ne]
    ring
  · show hopfZ a 0 (B.x / (2 * a)) (B.y / (2 * a)) = B.z
    unfold hopfZ
    field_simp [ha_ne]
    nlinarith [hxy, ha_sq]

/-- Every unit Bloch point has a normalized spinor representative. -/
theorem exists_unitSpinor_of_unitBloch
    (B : UnitBlochCoords) :
    ∃ u : UnitSpinorCoords, unitBlochOfSpinor u = B := by
  by_cases hz : B.z = -1
  · exact exists_unitSpinor_of_unitBloch_south B hz
  · exact exists_unitSpinor_of_unitBloch_north B hz

/-- The normalized phase quotient covers the whole unit Bloch sphere. -/
theorem quotientUnitBloch_surjective :
    Function.Surjective quotientUnitBloch := by
  intro B
  rcases exists_unitSpinor_of_unitBloch B with ⟨u, hu⟩
  exact ⟨Quot.mk phaseSetoid u, by simpa using hu⟩

/-- The normalized algebraic Hopf quotient is bijective onto the unit Bloch
sphere at set level. -/
theorem quotientUnitBloch_bijective :
    Function.Bijective quotientUnitBloch :=
  ⟨quotientUnitBloch_injective, quotientUnitBloch_surjective⟩

/-- Bundled set-level algebraic quotient theorem:
normalized spinors modulo common `U(1)` phase are in bijection with unit Bloch
coordinates. -/
theorem unit_hopf_quotient_to_bloch_sphere_bijective :
    Function.Bijective quotientUnitBloch :=
  quotientUnitBloch_bijective

#print axioms UnitSpinorCoords.exists_unitSpinor_of_unitBloch
#print axioms UnitSpinorCoords.quotientUnitBloch_surjective
#print axioms UnitSpinorCoords.quotientUnitBloch_bijective
#print axioms UnitSpinorCoords.unit_hopf_quotient_to_bloch_sphere_bijective

end UnifiedTheory.Audit.KFHopfUnitSphereQuotient.UnitSpinorCoords
