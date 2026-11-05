/- The actual spatial plaquette graph: two distinct plaquettes are adjacent
when they share a spatial link. Its degree is bounded independently of the
period, including short periodic geometries with repeated link occurrences. -/
import UnifiedTheory.Clay.YangMills.FiniteConnectedCount
import UnifiedTheory.Clay.YangMills.WilsonSpatialGramNeighborhood

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteGraph
noncomputable section
open WilsonTimeSlab WilsonSpatialGramNeighborhood WilsonSlabLocalComparison

variable (N : ℕ) [NeZero N]

abbrev Plaquettes := SpatialVertex N × SpatialPlane

omit [NeZero N] in
theorem link_affected (p : Plaquettes N) (e : SpatialVertex N × Fin 3)
    (he : e ∈ plaquetteLinks N p) : p ∈ affected N e.1 e.2 := by
  classical
  simp only [plaquetteLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact base_mem N p.1 p.2.val.1 p.2 (Or.inl rfl)
  · have hn : p.2.val.1 ≠ p.2.val.2 := ne_of_lt p.2.property
    have h := shifted_mem N (spatialStep N p.1 p.2.val.1) p.2.val.2 p.2 (Or.inr rfl)
    simpa only [transverse, if_neg hn, spatialStep, add_sub_cancel_right] using h
  · have h := shifted_mem N (spatialStep N p.1 p.2.val.2) p.2.val.1 p.2 (Or.inl rfl)
    simpa [transverse, spatialStep] using h
  · exact base_mem N p.1 p.2.val.2 p.2 (Or.inr rfl)

open Classical in
def neighbors (p : Plaquettes N) : Finset (Plaquettes N) :=
  (plaquetteLinks N p).biUnion (fun e => affected N e.1 e.2)

omit [NeZero N] in
theorem neighbors_mem (p q : Plaquettes N) :
    q ∈ neighbors N p ↔ ∃ e ∈ plaquetteLinks N p, e ∈ plaquetteLinks N q := by
  classical
  constructor
  · intro h
    obtain ⟨e,he,hq⟩ := Finset.mem_biUnion.mp h
    exact ⟨e,he,affected_contains_link N e q hq⟩
  · rintro ⟨e,he,hq⟩
    exact Finset.mem_biUnion.mpr ⟨e,he,link_affected N q e hq⟩

omit [NeZero N] in
theorem neighbors_card (p : Plaquettes N) : (neighbors N p).card ≤ 16 := by
  classical
  calc
    _ ≤ ∑ e ∈ plaquetteLinks N p, (affected N e.1 e.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ plaquetteLinks N p, 4 := Finset.sum_le_sum (fun e _ => affected_card N e.1 e.2)
    _ = (plaquetteLinks N p).card * 4 := by simp
    _ ≤ 16 := by have h := plaquetteLinks_card N p; omega

def graph : SimpleGraph (Plaquettes N) where
  Adj p q := p ≠ q ∧ ∃ e ∈ plaquetteLinks N p, e ∈ plaquetteLinks N q
  symm := by rintro p q ⟨hpq,e,hep,heq⟩; exact ⟨hpq.symm,e,heq,hep⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

local instance graphDecidable : DecidableRel (graph N).Adj := Classical.decRel _

omit [NeZero N] in
theorem graph_adj (p q : Plaquettes N) :
    (graph N).Adj p q ↔ p ≠ q ∧ ∃ e ∈ plaquetteLinks N p, e ∈ plaquetteLinks N q := Iff.rfl

theorem degree_bound (p : Plaquettes N) : (graph N).degree p ≤ 16 := by
  classical
  apply (Finset.card_le_card (show (graph N).neighborFinset p ⊆ neighbors N p from ?_)).trans
    (neighbors_card N p)
  intro q hq
  exact (neighbors_mem N p q).mpr ((SimpleGraph.mem_neighborFinset _ _ _).mp hq).2

def rooted (p : Plaquettes N) (k : ℕ) : Finset (Finset (Plaquettes N)) :=
  FiniteConnectedCount.rooted (graph N) p k

/-- Every connected k-plaquette set through a fixed plaquette is counted.
No factor depending on the size of the spatial torus occurs. -/
theorem rooted_card (p : Plaquettes N) (k : ℕ) :
    (rooted N p k).card ≤ 256^(k-1) := by
  have h := FiniteConnectedCount.rooted_card (graph N) 16 (degree_bound N) p k
  simpa only [rooted, pow_mul] using h

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteGraph
