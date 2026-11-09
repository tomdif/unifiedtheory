/- The graph distance between vertices in a finite connected induced
subgraph is smaller than its cardinality. -/
import UnifiedTheory.Clay.YangMills.FiniteConnectedTours
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteConnectedDistance
noncomputable section
open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

theorem distance_lt_card (S : Finset V) (p q : V) (hp : p ∈ S) (hq : q ∈ S)
    (hS : (G.induce (S : Set V)).Preconnected) : G.dist p q < S.card := by
  classical
  obtain ⟨w⟩ := hS ⟨p,hp⟩ ⟨q,hq⟩
  let inc : G.induce (S : Set V) →g G := ⟨Subtype.val,fun h => h⟩
  have hd := SimpleGraph.dist_le (w.toPath.val.map inc)
  rw [Walk.length_map] at hd
  have hc := w.toPath.property.length_lt
  change w.toPath.val.length < Fintype.card S at hc
  rw [Fintype.card_coe] at hc
  exact hd.trans_lt hc

end
end UnifiedTheory.Clay.YangMills.FiniteConnectedDistance
