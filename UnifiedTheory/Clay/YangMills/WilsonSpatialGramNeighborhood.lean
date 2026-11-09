/- Every spatial link has at most sixteen links in its affected plaquettes.
Outside this explicit set the bare mixed action cancels. The bound also
covers short periodic geometries with repeated plaquette occurrences. -/
import UnifiedTheory.Clay.YangMills.WilsonMixedGroundResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialGramNeighborhood
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSlabLocalComparison

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def plaquetteLinks (p : SpatialVertex n × SpatialPlane) : Finset (SpatialVertex n × Fin 3) :=
  {(p.1,p.2.1.1), (spatialStep n p.1 p.2.1.1,p.2.1.2),
    (spatialStep n p.1 p.2.1.2,p.2.1.1), (p.1,p.2.1.2)}

omit [NeZero n] in
theorem plaquetteLinks_card (p : SpatialVertex n × SpatialPlane) :
    (plaquetteLinks n p).card ≤ 4 := by
  unfold plaquetteLinks
  have h1 := Finset.card_insert_le (p.1,p.2.1.1)
    {(spatialStep n p.1 p.2.1.1,p.2.1.2),
      (spatialStep n p.1 p.2.1.2,p.2.1.1), (p.1,p.2.1.2)}
  have h2 := Finset.card_insert_le (spatialStep n p.1 p.2.1.1,p.2.1.2)
    {(spatialStep n p.1 p.2.1.2,p.2.1.1), (p.1,p.2.1.2)}
  have h3 := Finset.card_insert_le (spatialStep n p.1 p.2.1.2,p.2.1.1) {(p.1,p.2.1.2)}
  simp only [Finset.card_singleton] at h3
  omega

omit [NeZero n] in
theorem affected_contains_link (e : SpatialVertex n × Fin 3)
    (p : SpatialVertex n × SpatialPlane) (hp : p ∈ affected n e.1 e.2) :
    e ∈ plaquetteLinks n p := by
  rcases Finset.mem_biUnion.mp hp with ⟨s, hs, hp⟩
  have hs' : s.1.1 = e.2 ∨ s.1.2 = e.2 := by simpa only [planes,
    Finset.mem_filter, Finset.mem_univ, true_and] using hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · rcases hs' with h | h
    · simp [plaquetteLinks, h]
    · simp [plaquetteLinks, h]
  · rcases hs' with h | h
    · have he : spatialStep n (e.1-Pi.single (transverse e.2 s) 1) s.1.2 = e.1 := by
        simp [spatialStep, transverse, h]
      simp [plaquetteLinks, h, he]
    · have hn : s.1.1 ≠ e.2 := by rw [← h]; exact ne_of_lt s.2
      have he : spatialStep n (e.1-Pi.single (transverse e.2 s) 1) s.1.1 = e.1 := by
        simp [spatialStep, transverse, hn]
      simp [plaquetteLinks, h, he]

def near (e : SpatialVertex n × Fin 3) : Finset (SpatialVertex n × Fin 3) :=
  (affected n e.1 e.2).biUnion (plaquetteLinks n)

omit [NeZero n] in
theorem near_card (e : SpatialVertex n × Fin 3) : (near n e).card ≤ 16 := by
  calc
    _ ≤ ∑ p ∈ affected n e.1 e.2, (plaquetteLinks n p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ affected n e.1 e.2, 4 :=
      Finset.sum_le_sum (fun p _ => plaquetteLinks_card n p)
    _ = (affected n e.1 e.2).card*4 := by simp
    _ ≤ 16 := by have h := affected_card n e.1 e.2; omega

omit [NeZero n] in
theorem self_mem_near (e : SpatialVertex n × Fin 3) : e ∈ near n e := by
  have hn : (planes e.2).Nonempty := Finset.card_pos.mp (by rw [planes_card]; omega)
  obtain ⟨p, hp⟩ := hn
  have hplane : p.1.1 = e.2 ∨ p.1.2 = e.2 := by
    simpa only [planes, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  have ha := base_mem n e.1 e.2 p hplane
  exact Finset.mem_biUnion.mpr ⟨(e.1,p), ha, affected_contains_link n e _ ha⟩

omit [NeZero n] in
theorem far_disjoint (e d : SpatialVertex n × Fin 3) (hd : d ∉ near n e) :
    Disjoint (affected n e.1 e.2) (affected n d.1 d.2) := by
  apply Finset.disjoint_left.mpr
  intro p he hp
  exact hd (Finset.mem_biUnion.mpr ⟨p, he, affected_contains_link n d p hp⟩)

omit [NeZero n] in
theorem far_ne (e d : SpatialVertex n × Fin 3) (hd : d ∉ near n e) : e ≠ d := by
  rintro rfl
  exact hd (self_mem_near n e)

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialGramNeighborhood
