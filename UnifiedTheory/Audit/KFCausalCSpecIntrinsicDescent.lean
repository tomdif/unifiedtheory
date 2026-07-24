/-
  Audit/KFCausalCSpecIntrinsicDescent.lean   (arc file 4/6)

  THE COCYCLE — AND THE RESTRICTION-STABILITY HYPOTHESIS IT REQUIRES (Gap 1)

  On a FILLED triple overlap the three charts share a common causal carrier.
  The cocycle σ_jk ∘ σ_ij = σ_ik is NOT automatic from the pairwise argmaxes: the
  scores are sums over the full pairwise overlaps, and restricting to the triple
  carrier can move an argmax.  The honest content is:

     RESTRICTION-STABILITY  ==  the three pairwise transitions factor through a
     single frame identification on the shared triple carrier.

  We make that the explicit hypothesis (`CommonFrame`) — it is the empirical thing
  the margins must be large enough to guarantee — and PROVE the cocycle from it.
  This localizes Gap 1 exactly: everything downstream is unconditional once
  restriction-stability holds; nothing hides the assumption.

  On UNFILLED overlaps there is no common carrier, so no common frame is forced —
  which is precisely what permits nontrivial monodromy (file 5).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecUniqueMatching

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecIntrinsicDescent

open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile

/-- A common frame identification on a shared triple carrier: each chart's three
directions are identified with a common frame `F` by an equivalence `φ i`.  The
transition i→j is then `φ i` followed by `(φ j)⁻¹`.  This bundles exactly the
restriction-stability certificate. -/
structure CommonFrame (ChartIdx F : Type*) where
  φ : ChartIdx → (Direction ≃ F)

namespace CommonFrame

variable {ChartIdx F : Type*} (cf : CommonFrame ChartIdx F)

/-- The transition induced by the common frame from chart `i` to chart `j`. -/
def transition (i j : ChartIdx) : Equiv.Perm Direction :=
  (cf.φ i).trans (cf.φ j).symm

/-- **Inverse law (frame form).** -/
theorem transition_symm (i j : ChartIdx) :
    (cf.transition i j).symm = cf.transition j i := by
  ext a
  simp [transition, Equiv.trans_apply]

/-- **Cocycle.** On a filled triple overlap the transitions compose:
`σ_ij` then `σ_jk` equals `σ_ik`.  Proof: the middle frame cancels. -/
theorem transition_cocycle (i j k : ChartIdx) :
    (cf.transition i j).trans (cf.transition j k) = cf.transition i k := by
  ext a
  simp [transition, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **Reflexivity.** The self-transition is the identity. -/
theorem transition_refl (i : ChartIdx) :
    cf.transition i i = Equiv.refl Direction := by
  ext a
  simp [transition, Equiv.trans_apply]

end CommonFrame

/-- **Intrinsic three-sheet local system.** A common frame on the filled overlaps
yields transitions satisfying reflexivity, the inverse law, and the cocycle — the
defining data of a `Direction`-valued local system, derived from one causal
carrier rather than posited.  (This is the theorem the current
`KFCausalSheetHolonomyWitness` states by hand; here it is a consequence of
restriction-stability.) -/
theorem localSystem_axioms {ChartIdx F : Type*} (cf : CommonFrame ChartIdx F) :
    (∀ i, cf.transition i i = Equiv.refl Direction) ∧
    (∀ i j, (cf.transition i j).symm = cf.transition j i) ∧
    (∀ i j k, (cf.transition i j).trans (cf.transition j k) = cf.transition i k) :=
  ⟨cf.transition_refl, cf.transition_symm, cf.transition_cocycle⟩

#print axioms CommonFrame.transition_cocycle
#print axioms localSystem_axioms

end UnifiedTheory.Audit.KFCausalCSpecIntrinsicDescent
