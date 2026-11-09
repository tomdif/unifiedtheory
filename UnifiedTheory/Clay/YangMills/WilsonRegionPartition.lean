/- A regional Haar partition bound uniform in every frozen exterior.
Only the boundary plaquettes pay the unrestricted exterior-energy cost. -/
import UnifiedTheory.Clay.YangMills.WilsonRegionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRegionPartition
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks WilsonInducedSupport SingleLinkWilsonOscillation
open WilsonEnergyDensity WilsonBlockMarginal UnitaryHaarNeighborhood
open WilsonRegionEnergy WilsonJointBadStarTail

theorem massLower_le_one (K : ℕ) : massLower (Fin 2) K ≤ 1 := by
  unfold massLower
  rw [one_div]
  apply inv_le_one_of_one_le₀
  apply one_le_pow₀
  exact_mod_cast (show 1 ≤ 2 * K + 1 by omega)

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

def cap (B : Finset (Edge (Vertex n))) (K : ℕ) : Set (Inside (G := Q) B) :=
  Set.pi Set.univ (fun _ => nearIdentity representation K)

theorem cap_measurable (B : Finset (Edge (Vertex n))) (K : ℕ) : MeasurableSet (cap n B K) :=
  MeasurableSet.pi Set.countable_univ
    (fun _ _ => nearIdentity_measurable representation representation_continuous K)

omit [NeZero n] in
theorem cap_mass_lower (B : Finset (Edge (Vertex n))) (K : ℕ) (hK : 0 < K) :
    massLower (Fin 2) K ^ B.card ≤ (insideMeasure B (compactHaar Q)).real (cap n B K) := by
  have he : (insideMeasure B (compactHaar Q)).real (cap n B K) =
      ((compactHaar Q).real (nearIdentity representation K)) ^ B.card := by
    unfold Measure.real insideMeasure cap
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ENNReal.toReal_pow]
  rw [he]
  exact pow_le_pow_left₀ (massLower_pos (Fin 2) K).le
    (nearIdentity_mass_lower representation representation_continuous K hK) _

theorem plaquette_small (K : ℕ) (U : Configuration (Vertex n) Q) (p : PlaquetteIndex n)
    (hU : ∀ e ∈ plaquetteEdges n p, U e ∈ nearIdentity representation K) :
    plaquetteTerm n Q character 2 U p ≤ squaredTolerance (Fin 2) K := by
  rw [← plaquetteDefect_eq_term]
  unfold WilsonAverageDefect.plaquetteDefect loops
  rw [PeriodicPlaquetteReflection.plaquette_holonomy_eq_product n Q U p.1 p.2.1.1 p.2.1.2]
  apply four_link_defect_squared_bound
  all_goals
    apply hU
    apply (mem_plaquetteEdges n p _).mpr
    apply incident_affected
    simp [incident, edgeCoord, forward]

/-- Interior plaquettes are genuinely small on the cap; crossing plaquettes cost at most four. -/
theorem cap_energy_bound (B : Finset (Edge (Vertex n))) (K : ℕ)
    (r : Outside (G := Q) B) (v : Inside (G := Q) B) (hv : v ∈ cap n B K) :
    energy n B (assemble B (r,v)) ≤
      6 * (B.card : ℝ) * squaredTolerance (Fin 2) K + 4 * (boundary n B).card := by
  have hi : (∑ p ∈ interior n B, plaquetteTerm n Q character 2 (assemble B (r,v)) p) ≤
      (interior n B).card * squaredTolerance (Fin 2) K := by
    calc
      _ ≤ ∑ _p ∈ interior n B, squaredTolerance (Fin 2) K := by
        apply Finset.sum_le_sum
        intro p hp
        apply plaquette_small n K _ p
        intro e he
        have hb := (Finset.mem_filter.mp hp).2 he
        rw [assemble_inside B _ e hb]
        exact hv _ (Set.mem_univ _)
      _ = _ := by simp
  have hb : (∑ p ∈ boundary n B, plaquetteTerm n Q character 2 (assemble B (r,v)) p) ≤
      4 * (boundary n B).card := by
    calc
      _ ≤ ∑ _p ∈ boundary n B, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        simpa only [WilsonBlockNoiseKernel.source_basis] using
          (WilsonBlockNoiseKernel.source_basis_bounds n p (assemble B (r,v))).2
      _ = _ := by simp [mul_comm]
  have hsum := Finset.sum_sdiff (interior_subset n B)
    (f := fun p => plaquetteTerm n Q character 2 (assemble B (r,v)) p)
  have hc : ((interior n B).card : ℝ) ≤ 6 * (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (interior_subset n B)).trans (touching_card n B)
  have hh := mul_le_mul_of_nonneg_right hc (squaredTolerance_nonneg (Fin 2) K)
  change (∑ p ∈ boundary n B, plaquetteTerm n Q character 2 (assemble B (r,v)) p) +
    (∑ p ∈ interior n B, plaquetteTerm n Q character 2 (assemble B (r,v)) p) =
      energy n B (assemble B (r,v)) at hsum
  nlinarith

def cost (B : Finset (Edge (Vertex n))) (β : ℝ) (K : ℕ) : ℝ :=
  (6 * β * squaredTolerance (Fin 2) K - Real.log (massLower (Fin 2) K)) * B.card +
    4 * β * (boundary n B).card

/-- An actual regional partition bound, with no total-lattice-volume normalization loss. -/
theorem partition_lower (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 ≤ β)
    (K : ℕ) (hK : 0 < K) (r : Outside (G := Q) B) :
    Real.exp (-cost n B β K) ≤
      ∫ v, Real.exp (-(β * energy n B (assemble B (r,v))))
        ∂insideMeasure B (compactHaar Q) := by
  have h := GibbsLowEnergyConcentration.partition_lower (insideMeasure B (compactHaar Q))
    (fun v => energy n B (assemble B (r,v)))
    ((energy_continuous n B).comp
      ((assemble_continuous B).comp (continuous_const.prodMk continuous_id)))
    β hβ (6 * (B.card : ℝ) * squaredTolerance (Fin 2) K + 4 * (boundary n B).card)
    (massLower (Fin 2) K ^ B.card) (cap n B K) (cap_measurable n B K)
    (cap_mass_lower n B K hK) (cap_energy_bound n B K r)
  have he : Real.exp (-cost n B β K) =
      massLower (Fin 2) K ^ B.card *
        Real.exp (-β * (6 * (B.card : ℝ) * squaredTolerance (Fin 2) K +
          4 * (boundary n B).card)) := by
    rw [← Real.exp_log (mul_pos (pow_pos (massLower_pos (Fin 2) K) _) (Real.exp_pos _))]
    congr 1
    rw [Real.log_mul (pow_ne_zero _ (massLower_pos (Fin 2) K).ne') (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
    unfold cost
    ring
  rw [he]
  simpa only [GibbsLowEnergyConcentration.weight, neg_mul] using h

omit [NeZero n] in
theorem cost_grid_bound (B : Finset (Edge (Vertex n))) (β : ℝ) (hβ : 0 < β) :
    cost n B β (grid β) ≤
      6 * β * energyEnvelope β * B.card + 4 * β * (boundary n B).card := by
  have hl := Real.log_nonpos (massLower_pos (Fin 2) (grid β)).le (massLower_le_one (grid β))
  have hh := entropyCost_grid_le β hβ
  unfold entropyCost at hh
  have hc : 6 * β * squaredTolerance (Fin 2) (grid β) -
      Real.log (massLower (Fin 2) (grid β)) ≤ 6 * β * energyEnvelope β := by linarith
  unfold cost
  have h := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg B.card : (0 : ℝ) ≤ _)
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonRegionPartition
