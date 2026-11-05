/- Actual incidence-degree and influence-row bounds on the open Wilson cylinder.
Every incident face is placed in an explicit candidate list. Spatial links
have at most four spatial and two temporal faces; temporal links have six.
No degree or influence-row hypothesis is supplied. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry
import UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
import UnifiedTheory.Clay.YangMills.FiniteIncidenceInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderInfluenceGeometry
noncomputable section
open WilsonTimeSlab WilsonCylinderGeometry

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n L) := Classical.decEq _

/-- Only the slab immediately below or above a spatial slice can contain its link. -/
def timeChoices (t : Fin (L + 1)) : Finset (Fin L) :=
  Finset.univ.filter (fun s => s.val = t.val ∨ s.val + 1 = t.val)

omit [NeZero n] in
theorem timeChoices_card_le (t : Fin (L + 1)) : (timeChoices L t).card ≤ 2 := by
  have hs : (timeChoices L t).image Fin.val ⊆ {t.val, t.val - 1} := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    have hh : s.val = t.val ∨ s.val + 1 = t.val := (Finset.mem_filter.mp hs).2
    rcases hh with hh | hh
    · simp [hh]
    · have he : s.val = t.val - 1 := by omega
      simp [he]
  calc
    _ = ((timeChoices L t).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ ({t.val, t.val - 1} : Finset ℕ).card := Finset.card_le_card hs
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

def spatialCandidates (a : SpatialLink n L) : Finset (Plaquette n L) :=
  ((WilsonSlabLocalComparison.affected n a.2.1 a.2.2).image
    (fun p => Sum.inl (a.1, p))) ∪
    ((timeChoices L a.1).image (fun s => Sum.inr (s, a.2)))

def temporalCandidates (a : TemporalLink n L) : Finset (Plaquette n L) :=
  Finset.univ.biUnion (fun i : Fin 3 =>
    {Sum.inr (a.1, a.2, i), Sum.inr (a.1, a.2 - Pi.single i 1, i)})

def candidates (a : Link n L) : Finset (Plaquette n L) :=
  Sum.elim (spatialCandidates n L) (temporalCandidates n L) a

omit [NeZero n] in
theorem spatialCandidates_card_le (a : SpatialLink n L) :
    (spatialCandidates n L a).card ≤ 6 := by
  unfold spatialCandidates
  have h := Finset.card_union_le
    ((WilsonSlabLocalComparison.affected n a.2.1 a.2.2).image
      (fun p => (Sum.inl (a.1, p) : Plaquette n L)))
    ((timeChoices L a.1).image (fun s => (Sum.inr (s, a.2) : Plaquette n L)))
  have hs : ((WilsonSlabLocalComparison.affected n a.2.1 a.2.2).image
      (fun p => (Sum.inl (a.1, p) : Plaquette n L))).card ≤ 4 :=
    Finset.card_image_le.trans (WilsonSlabLocalComparison.affected_card n a.2.1 a.2.2)
  have ht : ((timeChoices L a.1).image
      (fun s => (Sum.inr (s, a.2) : Plaquette n L))).card ≤ 2 :=
    Finset.card_image_le.trans (timeChoices_card_le L a.1)
  omega

omit [NeZero n] in
theorem temporalCandidates_card_le (a : TemporalLink n L) :
    (temporalCandidates n L a).card ≤ 6 := by
  unfold temporalCandidates
  calc
    _ ≤ ∑ i : Fin 3, ({Sum.inr (a.1, a.2, i),
        Sum.inr (a.1, a.2 - Pi.single i 1, i)} : Finset (Plaquette n L)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 3, 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 6 := by simp

omit [NeZero n] in
theorem candidates_card_le (a : Link n L) : (candidates n L a).card ≤ 6 := by
  rcases a with a | a
  · exact spatialCandidates_card_le n L a
  · exact temporalCandidates_card_le n L a

omit [NeZero n] in
theorem spatial_candidate_mem (t : Fin (L + 1)) (x : SpatialVertex n) (i : Fin 3)
    (p : SpatialVertex n × SpatialPlane) (hp : p ∈ WilsonSlabLocalComparison.affected n x i) :
    Sum.inl (t, p) ∈ candidates n L (Sum.inl (t, x, i)) := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

omit [NeZero n] in
theorem spatial_candidate_temporal (t : Fin (L + 1)) (s : Fin L)
    (x : SpatialVertex n) (i : Fin 3) (ht : s.val = t.val ∨ s.val + 1 = t.val) :
    Sum.inr (s, x, i) ∈ candidates n L (Sum.inl (t, x, i)) := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩

omit [NeZero n] in
theorem temporal_candidate_base (t : Fin L) (x : SpatialVertex n) (i : Fin 3) :
    Sum.inr (t, x, i) ∈ candidates n L (Sum.inr (t, x)) := by
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ _, by simp⟩

omit [NeZero n] in
theorem temporal_candidate_shift (t : Fin L) (x : SpatialVertex n) (i : Fin 3) :
    Sum.inr (t, x - Pi.single i 1, i) ∈ candidates n L (Sum.inr (t, x)) := by
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ _, by simp⟩

omit [NeZero n] in
/-- Every actual spatial square appears in each of its four edges' candidate lists. -/
theorem spatial_boundary_candidate (p : SpatialPlaquette n L) (k : Fin 4) :
    Sum.inl p ∈ candidates n L (spatialBoundary n L p k) := by
  fin_cases k
  · exact spatial_candidate_mem n L p.1 p.2.1 p.2.2.1.1 p.2
      (WilsonSlabLocalComparison.base_mem n p.2.1 p.2.2.1.1 p.2.2 (Or.inl rfl))
  · apply spatial_candidate_mem n L p.1 (spatialStep n p.2.1 p.2.2.1.1) p.2.2.1.2 p.2
    have h := WilsonSlabLocalComparison.shifted_mem n
      (spatialStep n p.2.1 p.2.2.1.1) p.2.2.1.2 p.2.2 (Or.inr rfl)
    have hn : p.2.2.1.1 ≠ p.2.2.1.2 := ne_of_lt p.2.2.2
    simpa [WilsonSlabLocalComparison.transverse, hn, spatialStep] using h
  · apply spatial_candidate_mem n L p.1 (spatialStep n p.2.1 p.2.2.1.2) p.2.2.1.1 p.2
    have h := WilsonSlabLocalComparison.shifted_mem n
      (spatialStep n p.2.1 p.2.2.1.2) p.2.2.1.1 p.2.2 (Or.inl rfl)
    simpa [WilsonSlabLocalComparison.transverse, spatialStep] using h
  · exact spatial_candidate_mem n L p.1 p.2.1 p.2.2.1.2 p.2
      (WilsonSlabLocalComparison.base_mem n p.2.1 p.2.2.1.2 p.2.2 (Or.inr rfl))

omit [NeZero n] in
/-- Temporal endpoint slices need only one of the two available neighboring slabs. -/
theorem temporal_boundary_candidate (p : TemporalPlaquette n L) (k : Fin 4) :
    Sum.inr p ∈ candidates n L (temporalBoundary n L p k) := by
  fin_cases k
  · exact temporal_candidate_base n L p.1 p.2.1 p.2.2
  · exact spatial_candidate_temporal n L p.1.succ p.1 p.2.1 p.2.2 (Or.inr rfl)
  · have h := temporal_candidate_shift n L p.1 (spatialStep n p.2.1 p.2.2) p.2.2
    simpa [spatialStep] using h
  · exact spatial_candidate_temporal n L p.1.castSucc p.1 p.2.1 p.2.2 (Or.inl rfl)

omit [NeZero n] in
theorem boundary_mem_candidates (p : Plaquette n L) (k : Fin 4) :
    p ∈ candidates n L (boundary n L p k) := by
  rcases p with p | p
  · exact spatial_boundary_candidate n L p k
  · exact temporal_boundary_candidate n L p k

/-- Every genuinely incident plaquette belongs to the explicitly counted finite list. -/
theorem incidentFaces_subset_candidates (a : Link n L) :
    FiniteIncidenceInfluence.incidentFaces (incidentLinks n L) a ⊆ candidates n L a := by
  intro p hp
  have hi := (FiniteIncidenceInfluence.mem_incidentFaces (incidentLinks n L) a p).mp hp
  obtain ⟨k, hk⟩ := (incident_iff n L p a).mp hi
  rw [← hk]
  exact boundary_mem_candidates n L p k

/-- The actual degree bound is independent of temporal length and includes endpoint links. -/
theorem incident_degree_le (a : Link n L) :
    (FiniteIncidenceInfluence.incidentFaces (incidentLinks n L) a).card ≤ 6 :=
  (Finset.card_le_card (incidentFaces_subset_candidates n L a)).trans (candidates_card_le n L a)

/-- The actual open-cylinder shared-plaquette row count, with multiplicities preserved. -/
theorem multiplicity_row_le (a : Link n L) :
    ∑ b, FiniteIncidenceInfluence.multiplicity (incidentLinks n L) a b ≤ 18 :=
  FiniteIncidenceInfluence.row_le_eighteen (incidentLinks n L) a
    (incidentLinks_card_le n L) (incident_degree_le n L a)

/-- The genuine cylinder incidence matrix has row bound 36 beta for every temporal length. -/
theorem coefficient_row_le (β : ℝ) (hβ : 0 ≤ β) (a : Link n L) :
    ∑ b, FiniteIncidenceInfluence.coefficient (incidentLinks n L) β a b ≤ 36 * β :=
  FiniteIncidenceInfluence.coefficient_row_le (incidentLinks n L) β hβ a
    (incidentLinks_card_le n L) (incident_degree_le n L a)

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderInfluenceGeometry
