/-
  Audit/KFCausalProduct3SheetBridge.lean

  THE REGULAR THREE-DIRECTION TANGENT-CUBE BRIDGE

  The elementary Boolean cube `Set (Fin 3)` has an intrinsic sheet type: its
  order atoms.  This file proves that those atoms are exactly three primitive
  directions and that every order automorphism of the cube is uniquely a
  permutation of them.  Thus the order-automorphism type is equivalent to
  `S3`, not merely mapped into it.

  Centering a directional birth-incidence profile gives a canonical vector in
  the existing zero-sum carrier.  One active direction gives the corresponding
  simplex vertex, two active directions give minus the missing vertex, and
  zero or three active directions give zero.

  Finally, chart-transition automorphisms instantiate the abstract twisted
  transfer interface.  The remaining geometric input is deliberately exposed:
  this file does not prove that causal/CSpec neighborhoods admit such regular
  locally product charts, nor that their overlaps have nontrivial monodromy.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Order.Atoms
import Mathlib.Order.Hom.CompleteLattice
import UnifiedTheory.Audit.KFCubicTwistedTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalProduct3SheetBridge

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
open UnifiedTheory.Audit.KFCubicTwistedTransfer

universe u v

/-! ## 1. Primitive directions of the elementary three-cube -/

/-- The elementary local three-dimensional causal chart, represented as its
Boolean lattice of active coordinate directions. -/
abbrev TangentCube3 := Set (Fin 3)

/-- Intrinsic primitive directions: order atoms of the tangent cube. -/
abbrev TangentSheet3 := {cell : TangentCube3 // IsAtom cell}

/-- Each coordinate direction determines one intrinsic atom. -/
def directionAtom (direction : Fin 3) : TangentSheet3 :=
  ⟨{direction}, Set.isAtom_singleton direction⟩

/-- The atoms of the three-cube are canonically equivalent to `Fin 3`. -/
def directionAtomEquiv : Fin 3 ≃ TangentSheet3 :=
  Equiv.ofBijective directionAtom (by
    constructor
    · intro first second hEqual
      have hSingleton : ({first} : Set (Fin 3)) = {second} :=
        congrArg Subtype.val hEqual
      exact Set.singleton_injective hSingleton
    · rintro ⟨cell, hAtom⟩
      obtain ⟨direction, rfl⟩ := Set.isAtom_iff.mp hAtom
      exact ⟨direction, rfl⟩)

/-- The intrinsic atom type inherits its finite structure from the three
coordinate atoms. -/
noncomputable instance tangentSheet3Fintype : Fintype TangentSheet3 :=
  Fintype.ofEquiv (Fin 3) directionAtomEquiv

noncomputable instance tangentSheet3DecidableEq : DecidableEq TangentSheet3 :=
  Classical.decEq TangentSheet3

@[simp]
theorem directionAtomEquiv_apply (direction : Fin 3) :
    directionAtomEquiv direction = directionAtom direction :=
  rfl

/-- There are exactly three intrinsic primitive directions. -/
theorem tangentSheet3_card_eq_three : Fintype.card TangentSheet3 = 3 := by
  simpa using Fintype.card_congr directionAtomEquiv

/-! ## 2. Every order automorphism is exactly a sheet permutation -/

/-- Restriction of a tangent-cube order automorphism to its intrinsic atoms. -/
def tangentSheetTransport
    (automorphism : TangentCube3 ≃o TangentCube3) :
    Equiv.Perm TangentSheet3 where
  toFun sheet :=
    ⟨automorphism sheet.1,
      (automorphism.isAtom_iff sheet.1).2 sheet.2⟩
  invFun sheet :=
    ⟨automorphism.symm sheet.1,
      (automorphism.symm.isAtom_iff sheet.1).2 sheet.2⟩
  left_inv sheet := by
    apply Subtype.ext
    exact automorphism.symm_apply_apply sheet.1
  right_inv sheet := by
    apply Subtype.ext
    exact automorphism.apply_symm_apply sheet.1

@[simp]
theorem tangentSheetTransport_refl :
    tangentSheetTransport (OrderIso.refl TangentCube3) = Equiv.refl TangentSheet3 := by
  ext sheet
  rfl

@[simp]
theorem tangentSheetTransport_trans
    (first second : TangentCube3 ≃o TangentCube3) :
    tangentSheetTransport (first.trans second) =
      (tangentSheetTransport first).trans (tangentSheetTransport second) := by
  ext sheet
  rfl

/-- Coordinate form of the intrinsic atom permutation. -/
def orderAutToDirectionPerm
    (automorphism : TangentCube3 ≃o TangentCube3) :
    Equiv.Perm (Fin 3) :=
  directionAtomEquiv.trans
    ((tangentSheetTransport automorphism).trans directionAtomEquiv.symm)

/-- Every permutation of the primitive directions extends to a unique order
automorphism of the Boolean cube by direct image. -/
def directionPermToOrderAut
    (permutation : Equiv.Perm (Fin 3)) :
    TangentCube3 ≃o TangentCube3 :=
  Equiv.toOrderIsoSet permutation

/-- The atom restriction respects composition, so the classification is a
group classification rather than only a bijection of underlying types. -/
theorem orderAutToDirectionPerm_trans
    (first second : TangentCube3 ≃o TangentCube3) :
    orderAutToDirectionPerm (first.trans second) =
      (orderAutToDirectionPerm first).trans
        (orderAutToDirectionPerm second) := by
  apply Equiv.ext
  intro direction
  apply directionAtomEquiv.injective
  simp [orderAutToDirectionPerm, tangentSheetTransport_trans]

/-- An order automorphism sends a coordinate atom to the atom indexed by its
induced direction permutation. -/
theorem orderAut_image_singleton
    (automorphism : TangentCube3 ≃o TangentCube3) (direction : Fin 3) :
    automorphism ({direction} : Set (Fin 3)) =
      {orderAutToDirectionPerm automorphism direction} := by
  have hSheet :
      tangentSheetTransport automorphism (directionAtomEquiv direction) =
        directionAtomEquiv (orderAutToDirectionPerm automorphism direction) := by
    simp [orderAutToDirectionPerm]
  exact congrArg Subtype.val hSheet

/-- Extending a direction permutation and restricting back to atoms recovers
the original permutation. -/
theorem orderAutToDirectionPerm_directionPermToOrderAut
    (permutation : Equiv.Perm (Fin 3)) :
    orderAutToDirectionPerm (directionPermToOrderAut permutation) = permutation := by
  apply Equiv.ext
  intro direction
  have hImage := orderAut_image_singleton
    (directionPermToOrderAut permutation) direction
  have hSingleton :
      ({permutation direction} : Set (Fin 3)) =
        {orderAutToDirectionPerm (directionPermToOrderAut permutation) direction} := by
    simpa [directionPermToOrderAut] using hImage
  exact (Set.singleton_injective hSingleton).symm

/-- Restricting an order automorphism to atoms and extending that permutation
recovers the original automorphism.  Hence no hidden cube automorphisms remain
beyond `S3`. -/
theorem directionPermToOrderAut_orderAutToDirectionPerm
    (automorphism : TangentCube3 ≃o TangentCube3) :
    directionPermToOrderAut (orderAutToDirectionPerm automorphism) = automorphism := by
  apply OrderIso.ext
  funext cell
  apply Set.ext
  intro direction
  let permutation := orderAutToDirectionPerm automorphism
  change direction ∈ permutation '' cell ↔ direction ∈ automorphism cell
  constructor
  · rintro ⟨source, hSource, rfl⟩
    have hSubset : automorphism ({source} : Set (Fin 3)) ⊆ automorphism cell :=
      automorphism.monotone (Set.singleton_subset_iff.mpr hSource)
    rw [orderAut_image_singleton] at hSubset
    exact hSubset (Set.mem_singleton (permutation source))
  · intro hDirection
    let source := permutation.symm direction
    have hAtomImage :
        automorphism ({source} : Set (Fin 3)) = {direction} := by
      rw [orderAut_image_singleton]
      simp [source, permutation]
    have hSubset : automorphism ({source} : Set (Fin 3)) ⊆ automorphism cell := by
      rw [hAtomImage]
      exact Set.singleton_subset_iff.mpr hDirection
    have hSource : source ∈ cell := Set.singleton_subset_iff.mp
      ((automorphism.le_iff_le).mp hSubset)
    exact ⟨source, hSource, by simp [source]⟩

/-- **Tangent-cube automorphism theorem.**  The order automorphisms of the
regular elementary three-cube are exactly the permutations of its three
primitive directions. -/
def tangentCube3OrderAutEquivS3 :
    (TangentCube3 ≃o TangentCube3) ≃ Equiv.Perm (Fin 3) where
  toFun := orderAutToDirectionPerm
  invFun := directionPermToOrderAut
  left_inv := directionPermToOrderAut_orderAutToDirectionPerm
  right_inv := orderAutToDirectionPerm_directionPermToOrderAut

/-! ## 3. Centered directional birth current -/

/-- Remove the uniform part of an arbitrary directional incidence profile.
The result lies canonically in the intrinsic rank-two carrier. -/
def centeredDirectionalBirthCurrent
    (incidence : TangentSheet3 → ℂ) : ZeroSumCarrier TangentSheet3 :=
  ∑ sheet, incidence sheet •
    sheetVertex tangentSheet3_card_eq_three sheet

/-- Coordinate formula: the carrier current is incidence minus its mean. -/
theorem centeredDirectionalBirthCurrent_apply
    (incidence : TangentSheet3 → ℂ) (direction : TangentSheet3) :
    (centeredDirectionalBirthCurrent incidence).1 direction =
      incidence direction - (∑ sheet, incidence sheet) / 3 := by
  classical
  unfold centeredDirectionalBirthCurrent
  simp only [Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
    sheetVertex, sheetVertexFunction]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  simp
  ring

/-- The centered current is equivariant, not invariant, under relabeling of
the primitive directions. -/
theorem centeredDirectionalBirthCurrent_equivariant
    (relabeling : Equiv.Perm TangentSheet3)
    (incidence : TangentSheet3 → ℂ) :
    transportZeroSumCarrier relabeling
        (centeredDirectionalBirthCurrent incidence) =
      centeredDirectionalBirthCurrent (fun sheet => incidence (relabeling.symm sheet)) := by
  classical
  apply Subtype.ext
  funext direction
  change (centeredDirectionalBirthCurrent incidence).1 (relabeling.symm direction) = _
  rw [centeredDirectionalBirthCurrent_apply,
    centeredDirectionalBirthCurrent_apply]
  rw [Equiv.sum_comp relabeling.symm incidence]

/-- Binary incidence profile of an elementary birth. -/
def binaryDirectionalIncidence
    (active : Finset TangentSheet3) (sheet : TangentSheet3) : ℂ :=
  if sheet ∈ active then 1 else 0

/-- Trace-free directional current of a binary-incidence birth. -/
def binaryDirectionalBirthCurrent
    (active : Finset TangentSheet3) : ZeroSumCarrier TangentSheet3 :=
  centeredDirectionalBirthCurrent (binaryDirectionalIncidence active)

/-- A birth active in exactly one primitive direction produces precisely its
canonical simplex vertex. -/
theorem binaryBirthCurrent_single_direction (sheet : TangentSheet3) :
    binaryDirectionalBirthCurrent {sheet} =
      sheetVertex tangentSheet3_card_eq_three sheet := by
  classical
  simp [binaryDirectionalBirthCurrent, centeredDirectionalBirthCurrent,
    binaryDirectionalIncidence]

/-- A birth active in two directions produces minus the vertex of the missing
direction. -/
theorem binaryBirthCurrent_two_directions (missing : TangentSheet3) :
    binaryDirectionalBirthCurrent (Finset.univ.erase missing) =
      -sheetVertex tangentSheet3_card_eq_three missing := by
  classical
  apply Subtype.ext
  funext direction
  change
    (centeredDirectionalBirthCurrent
      (binaryDirectionalIncidence (Finset.univ.erase missing))).1 direction =
        (-sheetVertex tangentSheet3_card_eq_three missing).1 direction
  rw [centeredDirectionalBirthCurrent_apply]
  have hIncidenceSum :
      (∑ sheet, binaryDirectionalIncidence (Finset.univ.erase missing) sheet) =
        (2 : ℂ) := by
    have hTotal : (∑ _sheet : TangentSheet3, (1 : ℂ)) = 3 := by
      simp [tangentSheet3_card_eq_three]
    have hMissing :
        (∑ sheet : TangentSheet3,
          if sheet = missing then (1 : ℂ) else 0) = 1 := by
      simp
    simp only [binaryDirectionalIncidence, Finset.mem_erase,
      Finset.mem_univ, and_true]
    calc
      (∑ sheet : TangentSheet3,
          if sheet ≠ missing then (1 : ℂ) else 0) =
          (∑ _sheet : TangentSheet3, (1 : ℂ)) -
            ∑ sheet : TangentSheet3,
              if sheet = missing then (1 : ℂ) else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro sheet _hSheet
        by_cases hSheet : sheet = missing <;> simp [hSheet]
      _ = 2 := by rw [hTotal, hMissing]; ring
  rw [hIncidenceSum]
  by_cases hDirection : direction = missing
  · subst direction
    simp [binaryDirectionalIncidence, sheetVertex, sheetVertexFunction]
    ring
  · simp [binaryDirectionalIncidence, hDirection, sheetVertex,
      sheetVertexFunction]
    ring

/-- No active direction produces no trace-free excitation. -/
theorem binaryBirthCurrent_no_direction :
    binaryDirectionalBirthCurrent ∅ = 0 := by
  classical
  simp [binaryDirectionalBirthCurrent, centeredDirectionalBirthCurrent,
    binaryDirectionalIncidence]

/-- Equal activity in all three directions is isotropic and has no trace-free
excitation. -/
theorem binaryBirthCurrent_all_directions :
    binaryDirectionalBirthCurrent Finset.univ = 0 := by
  classical
  simpa [binaryDirectionalBirthCurrent, centeredDirectionalBirthCurrent,
    binaryDirectionalIncidence] using
      sheetVertex_sum_zero tangentSheet3_card_eq_three

/-- One-direction births have the universal squared carrier norm `2/3`. -/
theorem binaryBirthCurrent_single_norm (sheet : TangentSheet3) :
    zeroSumCarrierInner (binaryDirectionalBirthCurrent {sheet})
        (binaryDirectionalBirthCurrent {sheet}) = 2 / 3 := by
  rw [binaryBirthCurrent_single_direction,
    sheetVertex_inner tangentSheet3_card_eq_three]
  simp

/-- Two-direction births have the same universal squared norm `2/3`; their
current is the negative missing-sheet vertex. -/
theorem binaryBirthCurrent_two_norm (missing : TangentSheet3) :
    zeroSumCarrierInner
        (binaryDirectionalBirthCurrent (Finset.univ.erase missing))
        (binaryDirectionalBirthCurrent (Finset.univ.erase missing)) = 2 / 3 := by
  rw [binaryBirthCurrent_two_directions]
  have hNeg :
      zeroSumCarrierInner
          (-sheetVertex tangentSheet3_card_eq_three missing)
          (-sheetVertex tangentSheet3_card_eq_three missing) =
        zeroSumCarrierInner
          (sheetVertex tangentSheet3_card_eq_three missing)
          (sheetVertex tangentSheet3_card_eq_three missing) := by
    unfold zeroSumCarrierInner
    apply Finset.sum_congr rfl
    intro direction _hDirection
    simp
  rw [hNeg, sheetVertex_inner tangentSheet3_card_eq_three]
  simp

/-! ## 4. Regular chart transitions instantiate the twisted transfer -/

/-- Causal edges equipped with regular tangent-cube chart transitions.  This
is the exact new geometric input that a CSpec/growth model must construct. -/
structure RegularProduct3TransitionData
    (State : Type u) (Edge : State → Type v)
    [∀ state, Fintype (Edge state)] where
  target : ∀ state, Edge state → State
  weight : ∀ state, Edge state → ℂ
  chartTransition : ∀ state (_edge : Edge state),
    TangentCube3 ≃o TangentCube3

/-- Every regular product-chart transition law canonically instantiates the
abstract three-sheet twisted transfer data. -/
def RegularProduct3TransitionData.toTwistedSheetTransferData
    {State : Type u} {Edge : State → Type v}
    [∀ state, Fintype (Edge state)]
    (law : RegularProduct3TransitionData State Edge) :
    TwistedSheetTransferData State (fun _ => TangentSheet3) Edge where
  target := law.target
  weight := law.weight
  sheetTransport state edge :=
    tangentSheetTransport (law.chartTransition state edge)

/-- The preceding construction really produces an `S3`-valued edge law: its
coordinate action is the unique permutation classified by the cube
automorphism theorem. -/
theorem regularProduct3_sheetTransport_coordinate
    {State : Type u} {Edge : State → Type v}
    [∀ state, Fintype (Edge state)]
    (law : RegularProduct3TransitionData State Edge)
    (state : State) (edge : Edge state) :
    directionAtomEquiv.trans
        (((law.toTwistedSheetTransferData.sheetTransport state edge).trans
          directionAtomEquiv.symm)) =
      orderAutToDirectionPerm (law.chartTransition state edge) := by
  rfl

/-- **Regular-product bridge capstone.**  A nonzero unit twisted eigen-section
of chart-derived `S3` transport gives a normalized Hermitian strongly positive
branch functional.  All dynamics after the chart law is inherited from the
abstract twisted-transfer theorem. -/
theorem regularProduct3_eigenSection_induces_branchQuantumFunctional
    {State : Type u} {Edge : State → Type v}
    [∀ state, Fintype (Edge state)]
    (law : RegularProduct3TransitionData State Edge)
    (field : CarrierSection (fun _ : State => TangentSheet3))
    (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection
      law.toTwistedSheetTransferData field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) (state : State)
    (hUnit : zeroSumCarrierInner (field state) (field state) = 1) :
    IsHermitianGrowthFunctional
        (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates
            law.toTwistedSheetTransferData field eigenvalue state))
      ∧ IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates
            law.toTwistedSheetTransferData field eigenvalue state)))
      ∧ IsNormalizedGrowthFunctional
        (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates
            law.toTwistedSheetTransferData field eigenvalue state)) := by
  exact twistedTransferEigenSection_induces_branchQuantumFunctional
    law.toTwistedSheetTransferData field eigenvalue hEigen hEigenvalue state hUnit

#print axioms tangentSheet3_card_eq_three
#print axioms tangentSheetTransport_trans
#print axioms orderAutToDirectionPerm_trans
#print axioms tangentCube3OrderAutEquivS3
#print axioms centeredDirectionalBirthCurrent_equivariant
#print axioms binaryBirthCurrent_single_direction
#print axioms binaryBirthCurrent_two_directions
#print axioms binaryBirthCurrent_all_directions
#print axioms regularProduct3_eigenSection_induces_branchQuantumFunctional

end

end UnifiedTheory.Audit.KFCausalProduct3SheetBridge
