/-
  Audit/KFCausalCSpecSheetRealization.lean

  A NATIVE CAUSAL-ALGEBRA / CSPEC REALIZATION OF THE FINITE SHEET ATLAS

  The elementary Boolean tangent cube is made into an actual finite causal
  algebra using the independent `CausalAlgebraicGeometry` definitions.  Its
  three order atoms give three genuine points of that algebra's `CSpec` via
  strict principal upsets.  Every Boolean-chart order automorphism induces a
  causally-prime-set transport, and that transport acts on the three atom
  points by exactly the sheet permutation already used by the full-S3
  connection witness.

  Consequently the two witnessed triangle loops act on genuine CSpec points
  by the adjacent transpositions, and the six explicit loops realize every
  permutation of those three points.

  Honest boundary: native `CSpec` is currently a subtype of causally-prime
  upsets.  It does not itself provide a transition graph or chart-overlap
  connection.  This file therefore realizes the local charts and their
  overlap action in CSpec, but does not derive the four-state gluing from a
  single independently generated global CSpec.

  Zero sorry. Zero custom axioms.
-/

import CausalAlgebraicGeometry.BulletproofRecovery
import UnifiedTheory.Audit.KFCausalSheetHolonomyWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecSheetRealization

noncomputable section

open CausalAlgebraicGeometry.CausalAlgebra
open CausalAlgebraicGeometry.CausalPrimality
open CausalAlgebraicGeometry.CausalScheme
open CausalAlgebraicGeometry.BulletproofRecovery
open UnifiedTheory.Audit.KFCausalProduct3SheetBridge
open UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian
open UnifiedTheory.Audit.KFCausalSheetHolonomyWitness

/-! ## A sharp obstruction for the naive four-event causal diamond -/

/-- The four-cell Boolean causal diamond. -/
abbrev CausalDiamond4 := Set (Fin 2)

noncomputable instance causalDiamond4DecidableEq : DecidableEq CausalDiamond4 :=
  Classical.decEq CausalDiamond4

noncomputable instance causalDiamond4SubsetDecidable :
    DecidableRel (fun first second : CausalDiamond4 => first ⊆ second) :=
  Classical.decRel _

abbrev causalDiamondCausalAlgebra : CAlg ℂ :=
  fromFinitePoset CausalDiamond4 (fun first second => first ⊆ second)
    (fun _ => Set.Subset.rfl)
    (fun _ _ => Set.Subset.antisymm)
    (fun _ _ _ => Set.Subset.trans)

def causalDiamondCSpecPoint (cell : CausalDiamond4) :
    CSpec causalDiamondCausalAlgebra :=
  cspecPoint causalDiamondCausalAlgebra cell

/-- The two middle routes of the naive four-event diamond have the same
strict future, so the canonical principal-point map into native CSpec
identifies them. -/
theorem causalDiamond_middle_CSpec_points_equal :
    causalDiamondCSpecPoint ({0} : CausalDiamond4) =
      causalDiamondCSpecPoint ({1} : CausalDiamond4) := by
  apply Subtype.ext
  apply Set.ext
  intro future
  change CausalDiamond4 at future
  change (({0} : CausalDiamond4) ⊆ future ∧ ({0} : CausalDiamond4) ≠ future) ↔
    (({1} : CausalDiamond4) ⊆ future ∧ ({1} : CausalDiamond4) ≠ future)
  constructor
  · rintro ⟨hZeroSubset, hZeroNe⟩
    have hOne : (1 : Fin 2) ∈ future := by
      by_contra hOneNot
      apply hZeroNe
      apply Set.Subset.antisymm hZeroSubset
      intro direction hDirection
      fin_cases direction <;> simp_all
    constructor
    · exact Set.singleton_subset_iff.mpr hOne
    · intro hEqual
      have hZero := hZeroSubset (Set.mem_singleton (0 : Fin 2))
      rw [← hEqual] at hZero
      norm_num at hZero
  · rintro ⟨hOneSubset, hOneNe⟩
    have hZero : (0 : Fin 2) ∈ future := by
      by_contra hZeroNot
      apply hOneNe
      apply Set.Subset.antisymm hOneSubset
      intro direction hDirection
      fin_cases direction <;> simp_all
    constructor
    · exact Set.singleton_subset_iff.mpr hZero
    · intro hEqual
      have hOne := hOneSubset (Set.mem_singleton (1 : Fin 2))
      rw [← hEqual] at hOne
      norm_num at hOne

/-- Therefore the canonical four-event causal-diamond map into CSpec is not
faithful. A faithful global realization needs a future-distinguishing causal
base, non-principal spectrum data, or additional connection/atlas structure. -/
theorem causalDiamond_principalCSpecPoint_not_injective :
    ¬ Function.Injective causalDiamondCSpecPoint := by
  intro hInjective
  have hMiddle := hInjective causalDiamond_middle_CSpec_points_equal
  have hDirections : (0 : Fin 2) = 1 := Set.singleton_injective hMiddle
  norm_num at hDirections

/-! ## The Boolean tangent cube as a genuine causal algebra and CSpec -/

noncomputable instance tangentCube3DecidableEq : DecidableEq TangentCube3 :=
  Classical.decEq TangentCube3

noncomputable instance tangentCube3SubsetDecidable :
    DecidableRel (fun first second : TangentCube3 => first ⊆ second) :=
  Classical.decRel _

/-- The causal incidence algebra of the Boolean tangent cube. -/
abbrev tangentCubeCausalAlgebra : CAlg ℂ :=
  fromFinitePoset TangentCube3 (fun first second => first ⊆ second)
    (fun _ => Set.Subset.rfl)
    (fun _ _ => Set.Subset.antisymm)
    (fun _ _ _ => Set.Subset.trans)

@[simp]
theorem tangentCubeCausalAlgebra_le (first second : TangentCube3) :
    tangentCubeCausalAlgebra.le first second ↔ first ⊆ second :=
  Iff.rfl

/-- The complete native causal-scheme package generated by the Boolean
tangent cube. -/
noncomputable def tangentCubeCausalScheme : CausalSchemeData ℂ :=
  causalScheme_of_poset TangentCube3
    (fun first second => first ⊆ second)
    (fun _ => Set.Subset.rfl)
    (fun _ _ => Set.Subset.antisymm)
    (fun _ _ _ => Set.Subset.trans)

theorem tangentCubeCausalScheme_algebra :
    tangentCubeCausalScheme.algebra = tangentCubeCausalAlgebra := by
  rfl

/-- Every Boolean cell determines a genuine CSpec point by its strict future. -/
def tangentCubeCSpecPoint (cell : TangentCube3) :
    CSpec tangentCubeCausalAlgebra :=
  cspecPoint tangentCubeCausalAlgebra cell

/-- The three primitive directions as genuine points of the Boolean causal
algebra's CSpec. -/
def directionCSpecPoint (direction : Fin 3) :
    CSpec tangentCubeCausalAlgebra :=
  tangentCubeCSpecPoint ({direction} : TangentCube3)

/-- The three primitive directions remain distinct after passage to CSpec.
This is stronger than generic full-poset recovery, which need not be
injective without a future-distinguishing hypothesis. -/
theorem directionCSpecPoint_injective :
    Function.Injective directionCSpecPoint := by
  intro first second hEqual
  have hValues := congrArg Subtype.val hEqual
  fin_cases first <;> fin_cases second
  all_goals try rfl
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({0, 2} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    grind
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({0, 1} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    have hAt := Set.ext_iff.mp hMembership (1 : Fin 3)
    norm_num at hAt
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({1, 2} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    have hSet : ({(1 : Fin 3)} : TangentCube3) = {1, 2} := by
      simpa using hMembership
    have hAt := Set.ext_iff.mp hSet (2 : Fin 3)
    norm_num at hAt
    omega
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({0, 1} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    have hAt := Set.ext_iff.mp hMembership (0 : Fin 3)
    norm_num at hAt
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({1, 2} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    have hSet : ({(2 : Fin 3)} : TangentCube3) = {1, 2} := by
      simpa using hMembership
    have hAt := Set.ext_iff.mp hSet (1 : Fin 3)
    norm_num at hAt
    omega
  · exfalso
    have hMembership := Set.ext_iff.mp hValues ({0, 2} : TangentCube3)
    norm_num [directionCSpecPoint, tangentCubeCSpecPoint, cspecPoint,
      principalUpset, tangentCubeCausalAlgebra, fromFinitePoset] at hMembership
    have hSet : ({(2 : Fin 3)} : TangentCube3) = {0, 2} := by
      simpa using hMembership
    have hAt := Set.ext_iff.mp hSet (0 : Fin 3)
    norm_num at hAt
    omega

/-! ## CSpec transport induced by causal-chart order automorphisms -/

/-- Every Boolean order automorphism is an isomorphism of the associated
finite causal poset. -/
theorem tangentCubeOrderAut_isPosetIso
    (automorphism : TangentCube3 ≃o TangentCube3) :
    IsPosetIso tangentCubeCausalAlgebra tangentCubeCausalAlgebra automorphism := by
  refine ⟨automorphism.bijective, ?_⟩
  change ∀ first second : TangentCube3,
    first ⊆ second ↔ automorphism first ⊆ automorphism second
  intro first second
  exact automorphism.le_iff_le.symm

/-- Direct image along a causal-chart order automorphism transports native
CSpec points to native CSpec points. -/
def transportTangentCubeCSpec
    (automorphism : TangentCube3 ≃o TangentCube3) :
    CSpec tangentCubeCausalAlgebra → CSpec tangentCubeCausalAlgebra :=
  fun point =>
    ⟨automorphism '' point.1,
      rigidity_forward tangentCubeCausalAlgebra tangentCubeCausalAlgebra
        automorphism (tangentCubeOrderAut_isPosetIso automorphism)
        point.1 point.2⟩

/-- Native CSpec transport is an equivalence, with inverse induced by the
inverse causal-chart automorphism. -/
def tangentCubeCSpecEquiv
    (automorphism : TangentCube3 ≃o TangentCube3) :
    CSpec tangentCubeCausalAlgebra ≃ CSpec tangentCubeCausalAlgebra where
  toFun := transportTangentCubeCSpec automorphism
  invFun := transportTangentCubeCSpec automorphism.symm
  left_inv point := by
    apply Subtype.ext
    ext cell
    simp [transportTangentCubeCSpec]
  right_inv point := by
    apply Subtype.ext
    ext cell
    simp [transportTangentCubeCSpec]

/-- CSpec transport sends the strict-future point of a cell to the
strict-future point of its image. -/
theorem transportTangentCubeCSpec_point
    (automorphism : TangentCube3 ≃o TangentCube3)
    (cell : TangentCube3) :
    transportTangentCubeCSpec automorphism (tangentCubeCSpecPoint cell) =
      tangentCubeCSpecPoint (automorphism cell) := by
  apply Subtype.ext
  change automorphism '' principalUpset tangentCubeCausalAlgebra cell =
    principalUpset tangentCubeCausalAlgebra (automorphism cell)
  apply Set.ext
  intro target
  constructor
  · rintro ⟨source, hSource, rfl⟩
    exact ⟨automorphism.monotone hSource.1,
      fun hEqual => hSource.2 (automorphism.injective hEqual)⟩
  · intro hTarget
    refine ⟨automorphism.symm target, ?_, automorphism.apply_symm_apply target⟩
    constructor
    · apply (automorphism.le_iff_le).mp
      simpa using hTarget.1
    · intro hEqual
      apply hTarget.2
      simp [hEqual]

/-- On the three distinguished CSpec points, causal-chart transport is
exactly the induced primitive-direction permutation. -/
theorem transportTangentCubeCSpec_direction
    (automorphism : TangentCube3 ≃o TangentCube3)
    (direction : Fin 3) :
    transportTangentCubeCSpec automorphism (directionCSpecPoint direction) =
      directionCSpecPoint (orderAutToDirectionPerm automorphism direction) := by
  rw [directionCSpecPoint, transportTangentCubeCSpec_point,
    orderAut_image_singleton]
  rfl

/-! ## Realization of the explicit four-chart full-S3 witness -/

/-- The native CSpec transition induced by one witnessed Boolean-chart
overlap. -/
def witnessCSpecTransition (first second : WitnessState) :
    CSpec tangentCubeCausalAlgebra → CSpec tangentCubeCausalAlgebra :=
  transportTangentCubeCSpec (witnessChartTransition first second)

theorem witnessCSpecTransition_direction
    (first second : WitnessState) (direction : Fin 3) :
    witnessCSpecTransition first second (directionCSpecPoint direction) =
      directionCSpecPoint (witnessSheetTransport first second direction) := by
  rw [witnessCSpecTransition, transportTangentCubeCSpec_direction,
    witnessChartTransition_direction_permutation]

/-- Transport a native CSpec point from the endpoint chart back to the start
chart along a positive path of the witnessed connection. -/
def positivePathCSpecTransport
    {start finish : WitnessState} :
    PositiveConnectionPath fullS3WitnessConnection start finish →
      CSpec tangentCubeCausalAlgebra → CSpec tangentCubeCausalAlgebra
  | .nil _ => id
  | .cons start next _ tail =>
      witnessCSpecTransition start next ∘ positivePathCSpecTransport tail

/-- Path transport on the native CSpec atom points agrees exactly with sheet
holonomy. -/
theorem positivePathCSpecTransport_direction
    {start finish : WitnessState}
    (path : PositiveConnectionPath fullS3WitnessConnection start finish)
    (direction : Fin 3) :
    positivePathCSpecTransport path (directionCSpecPoint direction) =
      directionCSpecPoint
        (positivePathSheetTransport fullS3WitnessConnection path direction) := by
  induction path with
  | nil state => rfl
  | @cons start next finish hPositive tail ih =>
      simp only [positivePathCSpecTransport, Function.comp_apply]
      rw [ih, witnessCSpecTransition_direction]
      rfl

/-- The first witnessed triangle transposes the first two genuine CSpec atom
points. -/
theorem swapZeroOneLoop_CSpec_holonomy (direction : Fin 3) :
    positivePathCSpecTransport swapZeroOneLoop (directionCSpecPoint direction) =
      directionCSpecPoint (swapZeroOne direction) := by
  rw [positivePathCSpecTransport_direction, swapZeroOneLoop_holonomy]

/-- The second witnessed triangle transposes the last two genuine CSpec atom
points. -/
theorem swapOneTwoLoop_CSpec_holonomy (direction : Fin 3) :
    positivePathCSpecTransport swapOneTwoLoop (directionCSpecPoint direction) =
      directionCSpecPoint (swapOneTwo direction) := by
  rw [positivePathCSpecTransport_direction, swapOneTwoLoop_holonomy]

/-- **Native CSpec full-holonomy realization.** Every permutation of the
three primitive-direction CSpec points is realized by one of the explicit
positive closed paths of the four-chart witness. -/
theorem tangentCubeCSpecAtomPoints_haveFullS3Holonomy
    (relabeling : Equiv.Perm (Fin 3)) :
    ∃ path : PositiveConnectionPath fullS3WitnessConnection 0 0,
      ∀ direction,
        positivePathCSpecTransport path (directionCSpecPoint direction) =
          directionCSpecPoint (relabeling direction) := by
  obtain ⟨index, hIndex⟩ := fullS3WitnessHolonomy_surjective relabeling
  refine ⟨fullS3WitnessLoop index, ?_⟩
  intro direction
  rw [positivePathCSpecTransport_direction]
  change directionCSpecPoint (fullS3WitnessHolonomy index direction) =
    directionCSpecPoint (relabeling direction)
  rw [hIndex]

#print axioms tangentCubeOrderAut_isPosetIso
#print axioms causalDiamond_middle_CSpec_points_equal
#print axioms causalDiamond_principalCSpecPoint_not_injective
#print axioms directionCSpecPoint_injective
#print axioms transportTangentCubeCSpec_point
#print axioms transportTangentCubeCSpec_direction
#print axioms witnessCSpecTransition_direction
#print axioms swapZeroOneLoop_CSpec_holonomy
#print axioms swapOneTwoLoop_CSpec_holonomy
#print axioms tangentCubeCSpecAtomPoints_haveFullS3Holonomy

end

end UnifiedTheory.Audit.KFCausalCSpecSheetRealization
