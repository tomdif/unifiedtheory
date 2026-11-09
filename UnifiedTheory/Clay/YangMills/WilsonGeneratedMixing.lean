/- Apply the generated-interaction mixing criterion to the actual Wilson tower.
Oscillation bounds and the identity with exact elimination are proved. Smallness
of the stage budget and a uniformly bounded valid coloring remain explicit. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorContraction
import UnifiedTheory.Clay.YangMills.FiniteFactorOscillationTower
import UnifiedTheory.Clay.YangMills.WilsonFactorTower
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGeneratedMixing
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open FiniteFactorInfluence FiniteFactorElimination WilsonIndependentBlocks

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

omit [NeZero n] in
/-- The actual SU(2) plaquette factors have oscillation at most 4β. -/
theorem initial_oscillation (β : ℝ) (hβ : 0 ≤ β) :
    OscillationBound (WilsonFactorTower.initialFactor n β) (fun _ => 4 * β) := by
  intro p U V
  have hU : 0 ≤ WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p ∧
      WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p ≤ 4 :=
    WilsonSlabBounds.characterDefect_bounds _
  have hV : 0 ≤ WilsonIndependentBlocks.plaquetteTerm n Q character 2 V p ∧
      WilsonIndependentBlocks.plaquetteTerm n Q character 2 V p ≤ 4 :=
    WilsonSlabBounds.characterDefect_bounds _
  unfold WilsonFactorTower.initialFactor
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
  have hd : |WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p -
      WilsonIndependentBlocks.plaquetteTerm n Q character 2 V p| ≤ 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_left hd hβ]

/-- The weighted budget is computed along the same supports as the exact Wilson factors. -/
def weights (β : ℝ) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) :
    FiniteFactorIteration.Index (PlaquetteIndex n) T k → ℝ :=
  FiniteFactorOscillationTower.weights (WilsonInducedSupport.plaquetteEdges n)
    (fun _ => 4 * β) T k

theorem weights_nonneg (β : ℝ) (hβ : 0 ≤ β) (T : ℕ → Finset (Edge (Vertex n)))
    (k : ℕ) (j : FiniteFactorIteration.Index (PlaquetteIndex n) T k) :
    0 ≤ weights n β T k j :=
  FiniteFactorOscillationTower.weights_nonneg _ _ (fun _ => by positivity) T k j

/-- Every actual generated factor satisfies its computed finite-depth bound. -/
theorem factors_oscillation (β : ℝ) (hβ : 0 ≤ β) (T : ℕ → Finset (Edge (Vertex n)))
    (k : ℕ) : OscillationBound (WilsonFactorTower.factors n β T k) (weights n β T k) :=
  FiniteFactorOscillationTower.factors_oscillation (compactHaar Q)
    (WilsonInducedSupport.plaquetteEdges n) (WilsonFactorTower.initialFactor n β)
    (WilsonFactorTower.initialFactor_continuous n β) (WilsonFactorTower.initialFactor_dependsOn n β)
    _ (initial_oscillation n β hβ) T 1 k

/-- A Wilson edge touches at most six actual factors. -/
theorem touching_card (e : Edge (Vertex n)) :
    (touching (WilsonInducedSupport.plaquetteEdges n) e).card ≤ 6 := by
  have he : touching (WilsonInducedSupport.plaquetteEdges n) e =
      SingleLinkWilsonOscillation.affected n (edgeCoord n e).1 (edgeCoord n e).2 := by
    ext p
    simp only [touching, Finset.mem_filter, Finset.mem_univ, true_and,
      WilsonInducedSupport.mem_plaquetteEdges]
  rw [he]
  exact SingleLinkWilsonOscillation.affected_card n _ _

/-- At the Wilson seed the new criterion recovers the familiar 36β budget. -/
theorem initial_budget (β : ℝ) (hβ : 0 ≤ β) (e : Edge (Vertex n)) :
    rowBudget (WilsonInducedSupport.plaquetteEdges n) (fun _ => 4 * β) e ≤ 36 * β := by
  unfold rowBudget
  have hs : (∑ p ∈ touching (WilsonInducedSupport.plaquetteEdges n) e,
      (((WilsonInducedSupport.plaquetteEdges n p).erase e).card : ℝ) * (4 * β)) ≤
      (touching (WilsonInducedSupport.plaquetteEdges n) e).card * (12 * β) := by
    calc
      _ ≤ ∑ _p ∈ touching (WilsonInducedSupport.plaquetteEdges n) e, 12 * β := by
        apply Finset.sum_le_sum
        intro p hp
        have he : e ∈ WilsonInducedSupport.plaquetteEdges n p :=
          (Finset.mem_filter.mp hp).2
        have hc := Finset.card_erase_add_one he
        have hb := WilsonInducedSupport.plaquetteEdges_card n p
        have hr : (((WilsonInducedSupport.plaquetteEdges n p).erase e).card : ℝ) ≤ 3 := by
          exact_mod_cast
            (show ((WilsonInducedSupport.plaquetteEdges n p).erase e).card ≤ 3 by omega)
        nlinarith
      _ = _ := by simp
  have ht : ((touching (WilsonInducedSupport.plaquetteEdges n) e).card : ℝ) ≤ 6 :=
    Nat.cast_le.mpr (touching_card n e)
  nlinarith

/-- The conservative generated-factor weight after one step is at most 48β. -/
theorem first_generated_weight (β : ℝ) (hβ : 0 ≤ β)
    (T : ℕ → Finset (Edge (Vertex n))) (e : T 0) :
    weights n β T 1 (.inr e) ≤ 48 * β := by
  change 2 * (∑ _p ∈ touching (WilsonInducedSupport.plaquetteEdges n) e.val, 4 * β) ≤ _
  simp only [Finset.sum_const, nsmul_eq_mul]
  have ht : ((touching (WilsonInducedSupport.plaquetteEdges n) e.val).card : ℝ) ≤ 6 :=
    Nat.cast_le.mpr (touching_card n e.val)
  nlinarith

/-- The probability used in the mixing estimate equals the genuine induced Wilson law. -/
theorem stage_law_eq_tower (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : WilsonFactorTower.Admissible n T) (k : ℕ) :
    FiniteFactorContraction.law (compactHaar Q) (WilsonFactorTower.factors n β T k)
      (WilsonFactorTower.factors_continuous n β T k) =
      GibbsCoordinateTower.law (compactHaar Q) T (WilsonFactorTower.initialAction n β) k :=
  WilsonFactorTower.stage_law n β T hT k

/-- This is the remaining quantitative test on the actual induced interactions.
Its smallness and valid coloring premises are not inferred from UV stability. -/
theorem stage_contraction {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (β : ℝ) (hβ : 0 ≤ β) (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ)
    (color : Edge (Vertex n) → Color)
    (hcolor : FiniteFactorContraction.AdmissibleColoring (WilsonFactorTower.supports n T k) color)
    (α : ℝ) (hα : 0 ≤ α) (hsmall : α < 1)
    (hrow : ∀ e, rowBudget (WilsonFactorTower.supports n T k) (weights n β T k) e ≤ α) :
    ParallelOscillation.colorRate (Color := Color) α < 1 ∧
    ∀ F : C(Configuration (Vertex n) Q, ℝ),
      (∫ U, F U ∂FiniteFactorContraction.law (compactHaar Q)
        (WilsonFactorTower.factors n β T k)
        (WilsonFactorTower.factors_continuous n β T k)) = 0 →
      ‖ContinuousMap.toLp 2 (FiniteFactorContraction.law (compactHaar Q)
        (WilsonFactorTower.factors n β T k) (WilsonFactorTower.factors_continuous n β T k)) ℝ
        (FiniteFactorContraction.update (compactHaar Q) (WilsonFactorTower.factors n β T k)
          (WilsonFactorTower.factors_continuous n β T k) color F)‖ ≤
      ParallelOscillation.colorRate (Color := Color) α *
        ‖ContinuousMap.toLp 2 (FiniteFactorContraction.law (compactHaar Q)
          (WilsonFactorTower.factors n β T k)
          (WilsonFactorTower.factors_continuous n β T k)) ℝ F‖ := by
  refine ⟨ParallelOscillation.colorRate_lt_one α hsmall, ?_⟩
  intro F hmean
  exact FiniteFactorContraction.centered_norm_contraction (compactHaar Q)
    (WilsonFactorTower.supports n T k) (WilsonFactorTower.factors n β T k)
    (WilsonFactorTower.factors_continuous n β T k) (WilsonFactorTower.factors_dependsOn n β T k)
    (weights n β T k) (weights_nonneg n β hβ T k) (factors_oscillation n β hβ T k)
    color hcolor α hα hrow F hmean

end
end UnifiedTheory.Clay.YangMills.WilsonGeneratedMixing
