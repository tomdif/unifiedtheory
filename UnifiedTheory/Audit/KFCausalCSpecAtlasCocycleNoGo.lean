/-
  Audit/KFCausalCSpecAtlasCocycleNoGo.lean

  FILLED-TRIANGLE HOLONOMY AND THE CSPEC FUTURE-SIGNATURE DEFECT

  A genuine common triple overlap carries restriction-derived transition
  maps satisfying the Cech cocycle law.  Its oriented boundary holonomy is
  therefore the identity.  The two transposition triangles of the explicit
  full-S3 witness cannot be filled regular triple overlaps: they must wind
  around a missing intersection or defect, or live as nontrivial cycles in
  the atlas nerve/groupoid completion.

  The same file makes the CSpec separation condition exact.  The principal
  CSpec-point map is injective exactly when strict causal futures distinguish
  events.  A finite family of directions lies on the CSpec defect locus
  exactly when two distinct directions have equal strict-future signatures.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecSheetRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecAtlasCocycleNoGo

noncomputable section

open CausalAlgebraicGeometry.CausalAlgebra
open CausalAlgebraicGeometry.CausalPrimality
open CausalAlgebraicGeometry.CausalScheme
open CausalAlgebraicGeometry.BulletproofRecovery
open UnifiedTheory.Audit.KFCausalProduct3SheetBridge
open UnifiedTheory.Audit.KFCausalSheetHolonomyWitness
open UnifiedTheory.Audit.KFCausalCSpecSheetRealization

universe u

/-! ## Filled regular triple overlaps have flat boundary holonomy -/

/-- Three direction fibers together with restriction-derived transition
equivalences on one genuine common regular overlap.  The convention is that
`transition first second` transports from the second chart to the first. -/
structure FilledRegularTripleOverlap (Direction : Fin 3 → Type u) where
  transition : ∀ first second, Direction second ≃ Direction first
  transition_refl : ∀ chart,
    transition chart chart = Equiv.refl (Direction chart)
  transition_cocycle : ∀ first second third,
    (transition second third).trans (transition first second) =
      transition first third

/-- Endpoint-to-start transport around the oriented boundary
`0 -> 1 -> 2 -> 0` of a filled chart triangle. -/
def filledTriangleHolonomy {Direction : Fin 3 → Type u}
    (atlas : FilledRegularTripleOverlap Direction) :
    Direction 0 ≃ Direction 0 :=
  ((atlas.transition 2 0).trans (atlas.transition 1 2)).trans
    (atlas.transition 0 1)

/-- **Filled-triangle tripwire.** Restriction functoriality makes the
holonomy around the boundary of every genuine common triple overlap equal to
the identity. -/
theorem filledTriangleHolonomy_eq_id {Direction : Fin 3 → Type u}
    (atlas : FilledRegularTripleOverlap Direction) :
    filledTriangleHolonomy atlas = Equiv.refl (Direction 0) := by
  unfold filledTriangleHolonomy
  rw [atlas.transition_cocycle 1 2 0]
  rw [atlas.transition_cocycle 0 1 0]
  exact atlas.transition_refl 0

/-! ## The two supplied transposition triangles cannot be filled -/

/-- Vertices of the first witnessed triangle `0 -> 1 -> 3 -> 0`. -/
def firstWitnessTriangleVertex : Fin 3 → WitnessState :=
  ![0, 1, 3]

/-- Vertices of the second witnessed triangle `0 -> 2 -> 3 -> 0`. -/
def secondWitnessTriangleVertex : Fin 3 → WitnessState :=
  ![0, 2, 3]

/-- Pull the supplied Boolean-chart transition table back to one triangle. -/
def witnessTriangleTransition (vertex : Fin 3 → WitnessState)
    (first second : Fin 3) : Equiv.Perm (Fin 3) :=
  witnessSheetTransport (vertex first) (vertex second)

/-- Boundary transport of a supplied three-chart triangle, in the same
endpoint-to-start convention as `filledTriangleHolonomy`. -/
def witnessTriangleHolonomy (vertex : Fin 3 → WitnessState) :
    Equiv.Perm (Fin 3) :=
  ((witnessTriangleTransition vertex 2 0).trans
    (witnessTriangleTransition vertex 1 2)).trans
      (witnessTriangleTransition vertex 0 1)

theorem firstWitnessTriangle_holonomy :
    witnessTriangleHolonomy firstWitnessTriangleVertex = swapZeroOne := by
  ext direction
  fin_cases direction <;> rfl

theorem secondWitnessTriangle_holonomy :
    witnessTriangleHolonomy secondWitnessTriangleVertex = swapOneTwo := by
  ext direction
  fin_cases direction <;> rfl

theorem swapZeroOne_ne_id :
    swapZeroOne ≠ Equiv.refl (Fin 3) := by
  intro hEqual
  have hAtZero := DFunLike.congr_fun hEqual (0 : Fin 3)
  norm_num [swapZeroOne] at hAtZero

theorem swapOneTwo_ne_id :
    swapOneTwo ≠ Equiv.refl (Fin 3) := by
  intro hEqual
  have hAtOne := DFunLike.congr_fun hEqual (1 : Fin 3)
  norm_num [swapOneTwo] at hAtOne
  omega

/-- The first transposition triangle cannot be the boundary of a common
regular triple overlap whose transition maps are the witnessed ones. -/
theorem firstWitnessTriangle_not_filledRegularOverlap :
    ¬ ∃ atlas : FilledRegularTripleOverlap (fun _ : Fin 3 => Fin 3),
      ∀ first second,
        atlas.transition first second =
          witnessTriangleTransition firstWitnessTriangleVertex first second := by
  rintro ⟨atlas, hRealizes⟩
  have hIdentity := filledTriangleHolonomy_eq_id atlas
  have hWitnessIdentity :
      witnessTriangleHolonomy firstWitnessTriangleVertex =
        Equiv.refl (Fin 3) := by
    simpa only [filledTriangleHolonomy, witnessTriangleHolonomy,
      hRealizes] using hIdentity
  apply swapZeroOne_ne_id
  rw [← firstWitnessTriangle_holonomy]
  exact hWitnessIdentity

/-- The second transposition triangle likewise cannot be filled by a common
regular triple overlap. -/
theorem secondWitnessTriangle_not_filledRegularOverlap :
    ¬ ∃ atlas : FilledRegularTripleOverlap (fun _ : Fin 3 => Fin 3),
      ∀ first second,
        atlas.transition first second =
          witnessTriangleTransition secondWitnessTriangleVertex first second := by
  rintro ⟨atlas, hRealizes⟩
  have hIdentity := filledTriangleHolonomy_eq_id atlas
  have hWitnessIdentity :
      witnessTriangleHolonomy secondWitnessTriangleVertex =
        Equiv.refl (Fin 3) := by
    simpa only [filledTriangleHolonomy, witnessTriangleHolonomy,
      hRealizes] using hIdentity
  apply swapOneTwo_ne_id
  rw [← secondWitnessTriangle_holonomy]
  exact hWitnessIdentity

/-! ## CSpec collision is exactly failure of future distinguishability -/

/-- Principal CSpec points are equal exactly when their strict principal
futures are equal. -/
theorem cspecPoint_eq_iff_principalUpset_eq
    {k : Type*} [Field k] (C : CAlg k) (first second : C.Λ) :
    cspecPoint C first = cspecPoint C second ↔
      principalUpset C first = principalUpset C second := by
  constructor
  · exact fun hEqual => congrArg Subtype.val hEqual
  · exact fun hEqual => Subtype.ext hEqual

/-- **Exact CSpec separation criterion.** The canonical principal-point map
embeds the causal events precisely for future-distinguishing causal orders. -/
theorem cspecPoint_injective_iff_futureDistinguishing
    {k : Type*} [Field k] (C : CAlg k) :
    Function.Injective (cspecPoint C) ↔ IsFutureDistinguishing C := by
  constructor
  · intro hInjective first second hDistinct hFutureEqual
    apply hDistinct
    apply hInjective
    exact (cspecPoint_eq_iff_principalUpset_eq C first second).2 hFutureEqual
  · exact bulletproof_recovery C

/-- A direction family is on the causal/CSpec discriminant when passage to
principal CSpec points fails to keep its directions distinct. -/
def HasCSpecDirectionDefect
    {k : Type*} [Field k] (C : CAlg k)
    {Direction : Type u} (event : Direction → C.Λ) : Prop :=
  ¬ Function.Injective (fun direction => cspecPoint C (event direction))

/-- The defect is exactly a collision of strict-future signatures. -/
theorem hasCSpecDirectionDefect_iff_futureSignature_collision
    {k : Type*} [Field k] (C : CAlg k)
    {Direction : Type u} (event : Direction → C.Λ) :
    HasCSpecDirectionDefect C event ↔
      ∃ first second,
        principalUpset C (event first) = principalUpset C (event second) ∧
          first ≠ second := by
  constructor
  · intro hDefect
    obtain ⟨first, second, hEqual, hDistinct⟩ :=
      Function.not_injective_iff.mp hDefect
    exact ⟨first, second, congrArg Subtype.val hEqual, hDistinct⟩
  · rintro ⟨first, second, hFutureEqual, hDistinct⟩
    apply Function.not_injective_iff.mpr
    exact ⟨first, second, Subtype.ext hFutureEqual, hDistinct⟩

/-- The two middle routes of the naive causal diamond lie on this defect
locus. -/
theorem causalDiamond_middle_hasCSpecDirectionDefect :
    HasCSpecDirectionDefect causalDiamondCausalAlgebra
      (fun direction : Fin 2 => ({direction} : CausalDiamond4)) := by
  apply Function.not_injective_iff.mpr
  refine ⟨0, 1, causalDiamond_middle_CSpec_points_equal, ?_⟩
  decide

/-- By contrast, the three Boolean tangent directions avoid the local CSpec
defect locus. -/
theorem tangentCube_directions_have_noCSpecDirectionDefect :
    ¬ HasCSpecDirectionDefect tangentCubeCausalAlgebra
      (fun direction : Fin 3 => ({direction} : TangentCube3)) := by
  intro hNotInjective
  apply hNotInjective
  intro first second hEqual
  exact directionCSpecPoint_injective hEqual

#print axioms filledTriangleHolonomy_eq_id
#print axioms firstWitnessTriangle_not_filledRegularOverlap
#print axioms secondWitnessTriangle_not_filledRegularOverlap
#print axioms cspecPoint_injective_iff_futureDistinguishing
#print axioms hasCSpecDirectionDefect_iff_futureSignature_collision
#print axioms causalDiamond_middle_hasCSpecDirectionDefect
#print axioms tangentCube_directions_have_noCSpecDirectionDefect

end

end UnifiedTheory.Audit.KFCausalCSpecAtlasCocycleNoGo
