/- Joint regional bad-density bounds for the original interacting Wilson law.
Regions need only have disjoint edge sets; their bad events need not be independent.
Each threshold retains the boundary-to-volume penalty of its own region. -/
import UnifiedTheory.Clay.YangMills.WilsonRegionDensityTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRegionClusters
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonInducedSupport WilsonRegionEnergy WilsonRegionPartition WilsonRegionDensityTail
open WilsonEnergyDensity

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

theorem mem_boundary (B : Finset (Edge (Vertex n))) (p : PlaquetteIndex n) :
    p ∈ boundary n B ↔ (∃ e ∈ B, e ∈ plaquetteEdges n p) ∧ ¬plaquetteEdges n p ⊆ B := by
  simp only [boundary, Finset.mem_sdiff, WilsonRegionEnergy.interior,
    Finset.mem_filter, mem_touching]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨hp, fun hs => hn ⟨hp, hs⟩⟩
  · rintro ⟨hp, hn⟩
    exact ⟨hp, fun hs => hn hs.2⟩

theorem boundary_biUnion_subset {ι : Type*} (s : Finset ι)
    (B : ι → Finset (Edge (Vertex n))) :
    boundary n (s.biUnion B) ⊆ s.biUnion (fun i => boundary n (B i)) := by
  intro p hp
  obtain ⟨⟨e,he,hep⟩,hout⟩ := (mem_boundary n _ p).mp hp
  obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,(mem_boundary n (B i) p).mpr ⟨⟨e,hei,hep⟩,?_⟩⟩
  intro h
  exact hout (fun d hd => Finset.mem_biUnion.mpr ⟨i,hi,h hd⟩)

theorem boundary_biUnion_card {ι : Type*} (s : Finset ι)
    (B : ι → Finset (Edge (Vertex n))) :
    (boundary n (s.biUnion B)).card ≤ ∑ i ∈ s, (boundary n (B i)).card :=
  (Finset.card_le_card (boundary_biUnion_subset n s B)).trans Finset.card_biUnion_le

omit [NeZero n] in
theorem rate_biUnion {ι : Type*} (s : Finset ι) (B : ι → Finset (Edge (Vertex n)))
    (hB : (s : Set ι).PairwiseDisjoint B) (β : ℝ) (U : Configuration (Vertex n) Q) :
    rate n (s.biUnion B) β U = ∑ i ∈ s, rate n (B i) β U := by
  unfold rate
  rw [Finset.sum_biUnion hB, Finset.mul_sum]

theorem union_cost_bound {ι : Type*} (s : Finset ι) (B : ι → Finset (Edge (Vertex n)))
    (hB : (s : Set ι).PairwiseDisjoint B) (β : ℝ) (hβ : 0 < β) :
    cost n (s.biUnion B) β (grid β) ≤
      (∑ i ∈ s, budget n (B i) β) - ∑ i ∈ s, ((B i).card : ℝ) := by
  have hc : ((s.biUnion B).card : ℝ) = ∑ i ∈ s, ((B i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion hB
  have hb : ((boundary n (s.biUnion B)).card : ℝ) ≤
      ∑ i ∈ s, ((boundary n (B i)).card : ℝ) := by
    exact_mod_cast boundary_biUnion_card n s B
  calc
    _ ≤ 6 * β * energyEnvelope β * (s.biUnion B).card +
        4 * β * (boundary n (s.biUnion B)).card := cost_grid_bound n _ β hβ
    _ ≤ 6 * β * energyEnvelope β * (∑ i ∈ s, ((B i).card : ℝ)) +
        4 * β * (∑ i ∈ s, ((boundary n (B i)).card : ℝ)) := by
      rw [hc]
      have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * β by positivity)
      linarith
    _ = _ := by
      simp only [budget, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

variable [Fact (1 < n)]

/-- Correlated joint events obey an exponential total-region-size bound.
The threshold in each region includes its explicit boundary penalty. -/
theorem joint_bad_probability_bound {ι : Type*} (s : Finset ι)
    (B : ι → Finset (Edge (Vertex n))) (hB : (s : Set ι).PairwiseDisjoint B)
    (hne : ∀ i ∈ s, (B i).Nonempty) (β : ℝ) (hβ : 0 < β) :
    (wilsonLaw n Q character β 2).real {U | ∀ i ∈ s, U ∈ bad n (B i) β} ≤
      Real.exp (-(∑ i ∈ s, ((B i).card : ℝ))) := by
  apply (event_bound n (s.biUnion B) β hβ (grid β) (grid_pos β)
    {U | ∀ i ∈ s, U ∈ bad n (B i) β} (∑ i ∈ s, budget n (B i) β) (by
      intro U hU
      rw [rate_biUnion n s B hB]
      exact Finset.sum_le_sum (fun i hi => bad_rate n (B i) (hne i hi) β hβ U (hU i hi)))).trans
  apply Real.exp_le_exp.mpr
  linarith [union_cost_bound n s B hB β hβ]

/-- One threshold tending to zero controls all disjoint regions satisfying beta*boundary<=size. -/
theorem joint_common_probability_bound {ι : Type*} (s : Finset ι)
    (B : ι → Finset (Edge (Vertex n))) (hB : (s : Set ι).PairwiseDisjoint B)
    (hne : ∀ i ∈ s, (B i).Nonempty) (β : ℝ) (hβ : 0 < β)
    (hsurface : ∀ i ∈ s, β * (boundary n (B i)).card ≤ (B i).card) :
    (wilsonLaw n Q character β 2).real
      {U | ∀ i ∈ s, commonLevel β ≤ WilsonRegionEnergy.density n (B i) β U} ≤
      Real.exp (-(∑ i ∈ s, ((B i).card : ℝ))) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  apply (measureReal_mono (μ := wilsonLaw n Q character β 2)
    (show {U | ∀ i ∈ s, commonLevel β ≤ WilsonRegionEnergy.density n (B i) β U} ⊆
      {U | ∀ i ∈ s, U ∈ bad n (B i) β} from ?_)).trans
    (joint_bad_probability_bound n s B hB hne β hβ)
  intro U hU i hi
  exact (level_le_common n (B i) (hne i hi) β hβ (hsurface i hi)).trans (hU i hi)

end
end UnifiedTheory.Clay.YangMills.WilsonRegionClusters
