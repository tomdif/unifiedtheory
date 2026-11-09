/- Actual Wilson marginals have spatial covariance decay throughout the
small weighted-budget regime. The bound is independent of volume, depth,
and any coloring of the generated interactions. -/
import UnifiedTheory.Clay.YangMills.GibbsWeightedClustering
import UnifiedTheory.Clay.YangMills.WilsonMixedBudgetTower
import UnifiedTheory.Clay.YangMills.PeriodicSupportDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonWeightedClustering
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonMixedBudgetTower PeriodicSupportDistance FiniteFactorInfluence

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The original coefficient vanishes outside actual periodic plaquette range. -/
theorem seed_range (β : ℝ) (i j : Edge (Vertex n)) (hfar : 1 < distance n i j) :
    seed n β i j = 0 := by
  unfold seed coefficient
  split
  · rfl
  · have hs : (∑ p ∈ FiniteFactorElimination.touching (WilsonInducedSupport.plaquetteEdges n) i,
        if j ∈ WilsonInducedSupport.plaquetteEdges n p then 4 * β else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hj : j ∈ WilsonInducedSupport.plaquetteEdges n p
      · have hi : i ∈ WilsonInducedSupport.plaquetteEdges n p := by
          simpa only [FiniteFactorElimination.touching, Finset.mem_filter, Finset.mem_univ,
            true_and] using hp
        exact False.elim ((not_lt_of_ge (plaquette_distance n p i j hi hj)) hfar)
      · simp [hj]
    rw [hs, zero_div]

/-- The initial weighted row bound is derived from actual Wilson incidence, not assumed. -/
theorem seed_weighted_row (β m : ℝ) (hβ : 0 ≤ β) (hm : 0 ≤ m) (i : Edge (Vertex n)) :
    ∑ j, Real.exp (m * (distance n i j : ℝ)) * seed n β i j ≤ 36 * β * Real.exp m := by
  calc
    _ ≤ ∑ j, Real.exp m * seed n β i j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hfar : 1 < distance n i j
      · simp [seed_range n β i j hfar]
      · apply mul_le_mul_of_nonneg_right _ (seed_nonneg n β hβ i j)
        apply Real.exp_le_exp.mpr
        have hd : (distance n i j : ℝ) ≤ 1 := by exact_mod_cast (Nat.le_of_not_gt hfar)
        nlinarith
    _ = Real.exp m * ∑ j, seed n β i j := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp m * (36 * β) :=
      mul_le_mul_of_nonneg_left (seed_row n β hβ i) (Real.exp_pos _).le
    _ = _ := by ring

/-- The weighted budget survives every finite depth, including generated long-range couplings. -/
theorem stage_weighted_row (β m : ℝ) (hβ : 0 ≤ β) (hm : 0 ≤ m)
    (hsmall : 36 * β * Real.exp m ≤ 1) (E : ℕ → Edge (Vertex n)) (k : ℕ)
    (i : Edge (Vertex n)) :
    ∑ j, Real.exp (m * (distance n i j : ℝ)) * coefficients n β E k i j ≤
      36 * β * Real.exp m := by
  exact (WeightedMixedInfluence.iterate_rows (seed n β)
    (fun i j => Real.exp (m * (distance n i j : ℝ))) (seed_nonneg n β hβ)
    (fun i j => (Real.exp_pos _).le) (seed_diagonal n β)
    (WeightedMixedInfluence.exp_triangle (fun i j => (distance n i j : ℝ))
      (fun i e j => by dsimp only; exact_mod_cast distance_triangle n i e j) m hm)
    (36 * β * Real.exp m) (by positivity) hsmall (seed_weighted_row n β m hβ hm) E k).2.2 i

/-- Spatial clustering for the actual generated Wilson probability, with no coloring premise. -/
theorem stage_covariance_decay (β m : ℝ) (hβ : 0 ≤ β) (hm : 0 ≤ m)
    (hsmall : 36 * β * Real.exp m < 1) (E : ℕ → Edge (Vertex n)) (k : ℕ)
    (F G : C(Configuration (Vertex n) Q, ℝ))
    (S T : Finset (Edge (Vertex n))) (hT : T.Nonempty)
    (hF : DependsOn F (S : Set (Edge (Vertex n))))
    (hG : DependsOn G (T : Set (Edge (Vertex n))))
    (R : ℕ) (hsep : ∀ i ∈ S, ∀ j ∈ T, R ≤ distance n i j) :
    |(∫ U, F U * G U ∂stageLaw n β E k) -
      (∫ U, F U ∂stageLaw n β E k) * (∫ U, G U ∂stageLaw n β E k)| ≤
      (S.card : ℝ) * ‖F‖ * ‖G‖ * Real.exp (-m * (R : ℝ)) /
        (1 - 36 * β * Real.exp m) := by
  letI : Nonempty (Edge (Vertex n)) := ⟨Classical.choose hT⟩
  rw [stageLaw_eq_tower]
  exact GibbsWeightedClustering.tower_covariance_decay (compactHaar Q)
    (WilsonFactorTower.initialAction n β) (seed n β) (fun i j => (distance n i j : ℝ))
    (seed_nonneg n β hβ) (seed_symmetric n β) (seed_diagonal n β) (seed_mixed n β hβ)
    (fun i j => Nat.cast_nonneg _)
    (fun i e j => by dsimp only; exact_mod_cast distance_triangle n i e j)
    m (36 * β * Real.exp m) hm (by positivity) hsmall (seed_weighted_row n β m hβ hm)
    E k F G S T hF hG (fun i => (toSupport n T hT i : ℝ))
    (fun i j => by dsimp only; exact_mod_cast toSupport_triangle n T hT i j) (R : ℝ)
    (fun i hi => by dsimp only; exact_mod_cast toSupport_lower n T hT i R (hsep i hi))
    (fun i hi => by simp [toSupport_zero n T hT i hi])

end
end UnifiedTheory.Clay.YangMills.WilsonWeightedClustering
