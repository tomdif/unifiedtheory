/- The finite combinatorial chessboard maximum theorem. A nonnegative
functional on finite block labels, invariant under affine lattice frames
and satisfying the literal half-copy Schwarz inequality, is bounded by a
constant-label value. Its Wilson block-deletion instantiation is not assumed. -/
import UnifiedTheory.Clay.YangMills.BlockLabelSymmetry
import UnifiedTheory.Clay.YangMills.WilsonReflectionExtremum

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.BlockChessboardExtremum
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry BlockReflectionVariation BlockLabelSymmetry
open WilsonReflectionExtremum

variable (n : ℕ) [NeZero n] {A : Type*} [Finite A] [Nonempty A]

/-- The iteration is replaced by a finite maximum with least variation.
A nonconstant maximizer would admit a strictly improving seam reflection. -/
theorem constant_maximum (J : (SpatialVertex (2 * n) → A) → ℝ)
    (hJ : ∀ f, 0 ≤ J f)
    (hsym : ∀ σ s f, J (pull n σ s f) = J f)
    (hcs : ∀ f, (J f) ^ 2 ≤ J (positiveCopy n f) * J (negativeCopy n f)) :
    ∃ a : A, ∀ f, J f ≤ J (fun _ => a) := by
  classical
  obtain ⟨g,hmax,hmin⟩ := finite_max_min_rank J (variation n)
  have hz : variation n g = 0 := by
    by_contra hn
    obtain ⟨e,hd⟩ := exists_disagreement n g (Nat.pos_of_ne_zero hn)
    obtain ⟨σ,s,hs⟩ := move_disagreement n g e hd
    let q := pull n σ s g
    have hj : J q = J g := hsym σ s g
    have hv : variation n q = variation n g := variation_pull n σ s g
    have hm (f : SpatialVertex (2 * n) → A) : J f ≤ J q := by rw [hj]; exact hmax f
    have he := schwarz_at_max (hJ q) (hJ (positiveCopy n q)) (hJ (negativeCopy n q))
      (hm _) (hm _) (hcs q)
    have hp := hmin (positiveCopy n q) (he.1.trans hj)
    have hn := hmin (negativeCopy n q) (he.2.trans hj)
    have ht := variation_strict n q (seamVertex n,0) (seam_crossing n) hs
    omega
  have hc := (variation_zero_iff n g).mp hz
  refine ⟨g 0,?_⟩
  intro f
  have hg : g = fun _ => g 0 := funext (fun x => hc x 0)
  exact (hmax f).trans_eq (congrArg J hg)

/-- For binary deletion labels, only the empty and completely disseminated
patterns remain in the extremal bound. The hypotheses must be instantiated. -/
theorem binary_bound (J : (SpatialVertex (2 * n) → Bool) → ℝ)
    (hJ : ∀ f, 0 ≤ J f)
    (hsym : ∀ σ s f, J (pull n σ s f) = J f)
    (hcs : ∀ f, (J f) ^ 2 ≤ J (positiveCopy n f) * J (negativeCopy n f))
    (f : SpatialVertex (2 * n) → Bool) :
    J f ≤ max (J (fun _ => false)) (J (fun _ => true)) := by
  obtain ⟨b,hb⟩ := constant_maximum n J hJ hsym hcs
  cases b with
  | false => exact (hb f).trans (le_max_left _ _)
  | true => exact (hb f).trans (le_max_right _ _)

end
end UnifiedTheory.Clay.YangMills.BlockChessboardExtremum
