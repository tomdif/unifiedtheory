/- Stable mixed-interaction control for actual Wilson marginals in the proved
small-beta regime. Arbitrary singleton elimination schedules are admissible.
The influence row bound is uniform in elimination depth and volume. A uniform
color count and the weak-coupling crossover are not proved here. -/
import UnifiedTheory.Clay.YangMills.MixedEliminationTower
import UnifiedTheory.Clay.YangMills.WilsonGeneratedMixing

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMixedBudgetTower
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open FiniteFactorInfluence GibbsMixedElimination

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The actual plaquette-incidence influence budget at the Wilson seed. -/
def seed (β : ℝ) : Edge (Vertex n) → Edge (Vertex n) → ℝ :=
  coefficient (WilsonInducedSupport.plaquetteEdges n) (fun _ => 4 * β)

theorem seed_nonneg (β : ℝ) (hβ : 0 ≤ β) (i j : Edge (Vertex n)) :
    0 ≤ seed n β i j := coefficient_nonneg _ _ (fun _ => by positivity) i j

theorem seed_symmetric (β : ℝ) (i j : Edge (Vertex n)) : seed n β i j = seed n β j i :=
  MixedEliminationTower.coefficient_symmetric _ _ i j

theorem seed_diagonal (β : ℝ) (i : Edge (Vertex n)) : seed n β i i = 0 := by
  simp [seed, coefficient]

theorem seed_row (β : ℝ) (hβ : 0 ≤ β) (i : Edge (Vertex n)) :
    ∑ j, seed n β i j ≤ 36 * β := by
  rw [seed, coefficient_row_sum]
  exact WilsonGeneratedMixing.initial_budget n β hβ i

/-- Input mixed estimates are proved from the actual SU(2) Wilson plaquettes. -/
theorem seed_mixed (β : ℝ) (hβ : 0 ≤ β) : MixedBound (WilsonFactorTower.initialAction n β)
    (seed n β) := by
  have h := MixedEliminationTower.factor_mixed_of_oscillation
    (WilsonInducedSupport.plaquetteEdges n) (WilsonFactorTower.initialFactor n β)
    (WilsonFactorTower.initialFactor_dependsOn n β) (fun _ => 4 * β)
    (WilsonGeneratedMixing.initial_oscillation n β hβ)
  simpa only [WilsonFactorTower.initial_sum] using h

/-- Singleton elimination is independent for every generated support family. -/
theorem singleton_admissible (E : ℕ → Edge (Vertex n)) :
    WilsonFactorTower.Admissible n (fun t => {E t}) := by
  intro k p i hi j hj _ _
  exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm

def coefficients (β : ℝ) (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    Edge (Vertex n) → Edge (Vertex n) → ℝ := MixedInfluenceBudget.iterate (seed n β) E k

/-- The 36β row budget survives every finite depth of genuine Wilson integration. -/
theorem tower_bound (β : ℝ) (hβ : 0 ≤ β) (hsmall : β ≤ 1 / 36)
    (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    MixedBound (GibbsCoordinateTower.action (compactHaar Q) (fun t => {E t})
      (WilsonFactorTower.initialAction n β) k) (coefficients n β E k) ∧
    (∀ i j, 0 ≤ coefficients n β E k i j) ∧
    (∀ i j, coefficients n β E k i j = coefficients n β E k j i) ∧
    (∀ i, coefficients n β E k i i = 0) ∧
    (∀ i, ∑ j, coefficients n β E k i j ≤ 36 * β) := by
  exact MixedEliminationTower.uniform_tower (compactHaar Q) (WilsonFactorTower.initialAction n β)
    (seed n β) (seed_nonneg n β hβ) (seed_symmetric n β) (seed_diagonal n β)
    (seed_mixed n β hβ) (36 * β) (by positivity) (by linarith) (seed_row n β hβ) E k

/-- The computed factor family inherits the stable mixed bound on the whole induced action.
This avoids adding the global amplitudes of the reference-subtracted factors. -/
theorem factors_mixed (β : ℝ) (hβ : 0 ≤ β) (hsmall : β ≤ 1 / 36)
    (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    FiniteFactorInfluence.MixedOscillationBound (WilsonFactorTower.factors n β (fun t => {E t}) k)
      (fun i j => 4 * coefficients n β E k i j) := by
  rw [← factor_mixedBound_iff]
  change MixedBound (WilsonFactorTower.stageAction n β (fun t => {E t}) k) _
  rw [WilsonFactorTower.stageAction_eq_tower n β _ (singleton_admissible n E) k]
  exact (tower_bound n β hβ hsmall E k).1

/-- Conditional influence under the genuine Wilson stage law has the same depth-uniform budget. -/
theorem tower_localInfluence (β : ℝ) (hβ : 0 ≤ β) (hsmall : β ≤ 1 / 36)
    (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    ParallelOscillation.LocalInfluence
      (fun i U => CompactGibbsContinuity.law (compactHaar Q)
        (fun q => GibbsCoordinateTower.action (compactHaar Q) (fun t => {E t})
          (WilsonFactorTower.initialAction n β) k (Function.update U i q)))
      (coefficients n β E k) :=
  MixedEliminationTower.tower_localInfluence (compactHaar Q) (WilsonFactorTower.initialAction n β)
    (seed n β) (seed_nonneg n β hβ) (seed_symmetric n β) (seed_diagonal n β)
    (seed_mixed n β hβ) (36 * β) (by positivity) (by linarith) (seed_row n β hβ) E k

/-- The genuine generated Gibbs law used by the auxiliary update. -/
def stageLaw (β : ℝ) (E : ℕ → Edge (Vertex n)) (k : ℕ) : Measure (Configuration (Vertex n) Q) :=
  FiniteFactorContraction.law (compactHaar Q) (WilsonFactorTower.factors n β (fun t => {E t}) k)
    (WilsonFactorTower.factors_continuous n β (fun t => {E t}) k)

instance stageLaw_probability (β : ℝ) (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    IsProbabilityMeasure (stageLaw n β E k) :=
  FiniteFactorContraction.law_probability (compactHaar Q)
    (WilsonFactorTower.factors n β (fun t => {E t}) k)
    (WilsonFactorTower.factors_continuous n β (fun t => {E t}) k)

def stageUpdate {Color : Type*} [Fintype Color] [DecidableEq Color]
    (β : ℝ) (E : ℕ → Edge (Vertex n)) (k : ℕ) (color : Edge (Vertex n) → Color)
    (F : C(Configuration (Vertex n) Q, ℝ)) : C(Configuration (Vertex n) Q, ℝ) :=
  FiniteFactorContraction.update (compactHaar Q)
    (WilsonFactorTower.factors n β (fun t => {E t}) k)
    (WilsonFactorTower.factors_continuous n β (fun t => {E t}) k) color F

/-- The represented probability is exactly the Wilson-induced tower law. -/
theorem stageLaw_eq_tower (β : ℝ) (E : ℕ → Edge (Vertex n)) (k : ℕ) :
    stageLaw n β E k = GibbsCoordinateTower.law (compactHaar Q) (fun t => {E t})
      (WilsonFactorTower.initialAction n β) k :=
  WilsonGeneratedMixing.stage_law_eq_tower n β _ (singleton_admissible n E) k

/-- The generated-action smallness premise has been discharged in the initial small-beta regime.
The color count still has to be controlled to obtain a volume-uniform update rate. -/
theorem stage_contraction {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36)
    (E : ℕ → Edge (Vertex n)) (k : ℕ) (color : Edge (Vertex n) → Color)
    (hcolor : FiniteFactorContraction.AdmissibleColoring
      (WilsonFactorTower.supports n (fun t => {E t}) k) color)
    (F : C(Configuration (Vertex n) Q, ℝ)) (hmean : (∫ U, F U ∂stageLaw n β E k) = 0) :
    ParallelOscillation.colorRate (Color := Color) (36 * β) < 1 ∧
    ‖ContinuousMap.toLp 2 (stageLaw n β E k) ℝ (stageUpdate n β E k color F)‖ ≤
      ParallelOscillation.colorRate (Color := Color) (36 * β) *
        ‖ContinuousMap.toLp 2 (stageLaw n β E k) ℝ F‖ := by
  refine ⟨ParallelOscillation.colorRate_lt_one _ (by linarith), ?_⟩
  have ht := tower_bound n β hβ hsmall.le E k
  apply FiniteFactorContraction.centered_norm_contraction_of_mixed (compactHaar Q)
    (WilsonFactorTower.supports n (fun t => {E t}) k)
    (WilsonFactorTower.factors n β (fun t => {E t}) k)
    (WilsonFactorTower.factors_continuous n β (fun t => {E t}) k)
    (WilsonFactorTower.factors_dependsOn n β (fun t => {E t}) k)
    (fun i j => 4 * coefficients n β E k i j)
    (fun i j => mul_nonneg (by norm_num) (ht.2.1 i j))
    (factors_mixed n β hβ hsmall.le E k) color hcolor (36 * β) (by positivity) _ F hmean
  intro i
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (ht.2.2.2.2 i) (by norm_num)

end
end UnifiedTheory.Clay.YangMills.WilsonMixedBudgetTower
