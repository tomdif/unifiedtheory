/- Rooted connected-set entropy from explicit closed tours. Degree bounds
control every candidate without a factor depending on the ambient volume. -/
import UnifiedTheory.Clay.YangMills.FiniteConnectedTours
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteConnectedCount
noncomputable section
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

open Classical in
def rooted (r : V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun S => r ∈ S ∧ S.card = k ∧ (G.induce (S : Set V)).Preconnected)

theorem rooted_mem (r : V) (k : ℕ) (S : Finset V) :
    S ∈ rooted G r k ↔ r ∈ S ∧ S.card = k ∧ (G.induce (S : Set V)).Preconnected := by
  classical
  simp only [rooted, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rooted_zero (r : V) : rooted G r 0 = ∅ := by
  classical
  ext S
  simp only [rooted_mem, Finset.card_eq_zero, Finset.notMem_empty, iff_false]
  rintro ⟨hr,rfl,_⟩
  exact Finset.notMem_empty r hr

variable [DecidableRel G.Adj]

theorem walk_count (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (L : ℕ) (r t : V) :
    (G.finsetWalkLength L r t).card ≤ D^L := by
  classical
  induction L generalizing r t with
  | zero =>
    by_cases hrt : r = t
    · subst t
      simp [SimpleGraph.finsetWalkLength]
    · simp [SimpleGraph.finsetWalkLength, hrt]
  | succ L ih =>
    rw [SimpleGraph.finsetWalkLength]
    apply Finset.card_biUnion_le.trans
    simp only [Finset.card_map]
    calc
      (∑ w : G.neighborSet r, (G.finsetWalkLength L w t).card)
        ≤ ∑ _w : G.neighborSet r, D^L := Finset.sum_le_sum (fun w _ => ih w t)
      _ = G.degree r * D^L := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          SimpleGraph.card_neighborSet_eq_degree]
      _ ≤ D * D^L := Nat.mul_le_mul_right _ (hD r)
      _ = _ := by rw [pow_succ, Nat.mul_comm]

/-- Every connected k-set containing the fixed root is the support of
one of at most D^(2*(k-1)) closed tours. -/
theorem rooted_card (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (r : V) (k : ℕ) :
    (rooted G r k).card ≤ D^(2 * (k - 1)) := by
  classical
  have hsub : rooted G r k ⊆
      (G.finsetWalkLength (2 * (k - 1)) r r).image (fun w => w.support.toFinset) := by
    intro S hS
    obtain ⟨hr,hk,hconn⟩ := (rooted_mem G r k S).mp hS
    obtain ⟨w,hw,hs⟩ := FiniteConnectedTours.covering_tour G S r hr hconn
    exact Finset.mem_image.mpr ⟨w,SimpleGraph.mem_finsetWalkLength_iff.mpr (by rwa [hk] at hw),hs⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans (walk_count G D hD _ r r))

end
end UnifiedTheory.Clay.YangMills.FiniteConnectedCount
