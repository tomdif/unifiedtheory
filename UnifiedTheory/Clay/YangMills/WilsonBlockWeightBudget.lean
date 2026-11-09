/- Geometric source-weight accounting for independent Wilson link blocks.
Each affected plaquette is counted at most once; no block-cardinality factor
is introduced. These are finite-lattice identities and inequalities. -/
import UnifiedTheory.Clay.YangMills.WilsonSeparatedSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBlockWeightBudget
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks SingleLinkWilsonOscillation

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem affected_sum_eq_union (S : Finset (Link n)) (hS : Independent n S)
    (w : PlaquetteIndex n → ℝ) :
    (∑ a ∈ S, ∑ p ∈ affected n a.1 a.2, w p) =
      ∑ p ∈ S.biUnion (fun a => affected n a.1 a.2), w p := by
  classical
  exact (Finset.sum_biUnion (fun a ha b hb hab => hS a ha b hb hab)).symm

theorem affected_sum_le_total (S : Finset (Link n)) (hS : Independent n S)
    (w : PlaquetteIndex n → ℝ) (hw : ∀ p, 0 ≤ w p) :
    (∑ a ∈ S, ∑ p ∈ affected n a.1 a.2, w p) ≤ ∑ p, w p := by
  classical
  rw [affected_sum_eq_union n S hS w]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hw p)

theorem absolute_weight_budget (S : Finset (Link n)) (hS : Independent n S)
    (f : PlaquetteIndex n → ℝ) :
    (∑ a ∈ S, ∑ p ∈ affected n a.1 a.2, |f p|) ≤ ∑ p, |f p| :=
  affected_sum_le_total n S hS (fun p => |f p|) (fun p => abs_nonneg (f p))

theorem inside_weight_budget (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n))) (f : PlaquetteIndex n → ℝ) :
    (∑ e : {e : Edge (Vertex n) // e ∈ S},
      ∑ p ∈ affected n (edgeCoord n e.val).1 (edgeCoord n e.val).2, |f p|) ≤
        ∑ p, |f p| := by
  classical
  have h := absolute_weight_budget n (S.image (edgeCoord n)) hS f
  rw [Finset.sum_image (fun e _ e' _ he => WilsonSeparatedSources.edgeCoord_injective n he),
    ← Finset.sum_coe_sort] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonBlockWeightBudget
