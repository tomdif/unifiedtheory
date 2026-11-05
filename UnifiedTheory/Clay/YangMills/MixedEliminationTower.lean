/- Iterated mixed-interaction control for the actual coordinate-elimination tower.
Once a symmetric influence budget at most one is verified, exact single-site
integration preserves it at every finite depth. No small output action is assumed. -/
import UnifiedTheory.Clay.YangMills.GibbsMixedElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.MixedEliminationTower
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination FiniteFactorInfluence
open GibbsMixedElimination

section Algebra
variable {I P X : Type*} [Fintype P] [DecidableEq I]

/-- Shared-support oscillation coefficients are symmetric. -/
theorem coefficient_symmetric (D : P → Finset I) (w : P → ℝ) (i j : I) :
    coefficient D w i j = coefficient D w j i := by
  by_cases hij : i = j
  · subst j
    rfl
  simp only [coefficient, if_neg hij, if_neg (Ne.symm hij), touching, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hi : i ∈ D p <;> by_cases hj : j ∈ D p <;> simp [hi, hj]

/-- Global factor oscillations supply a valid initial mixed budget, with exterior cancellation. -/
theorem factor_mixed_of_oscillation (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw : OscillationBound Φ w) : MixedBound (action Φ) (coefficient D w) := by
  intro i j U V hUV q z
  by_cases hij : i = j
  · subst j
    rw [update_eq_of_agrees U V i hUV q, update_eq_of_agrees U V i hUV z]
    simp [coefficient]
  let b := ∑ p ∈ touching D i, if j ∈ D p then w p else 0
  have hq := localAction_difference_bound D Φ hΦ w hw i j U V hUV q
  have hz := localAction_difference_bound D Φ hΦ w hw i j U V hUV z
  calc
    _ = |(localAction D Φ i U q - localAction D Φ i V q) -
        (localAction D Φ i U z - localAction D Φ i V z)| := by
      simp only [action_eq_constant_add D Φ hΦ]
      congr 1
      ring
    _ ≤ |localAction D Φ i U q - localAction D Φ i V q| +
        |localAction D Φ i U z - localAction D Φ i V z| := abs_sub _ _
    _ ≤ b + b := add_le_add hq hz
    _ = 4 * coefficient D w i j := by rw [coefficient, if_neg hij]; dsimp [b]; ring

end Algebra

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- All actions are the existing genuine tower actions. The initial hypotheses,
not fresh output bounds at each step, control every finite marginal. -/
theorem uniform_tower (A : C(I → X, ℝ)) (c : I → I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hA : MixedBound A c)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hrow : ∀ i, ∑ j, c i j ≤ α)
    (E : ℕ → I) : ∀ k,
      MixedBound (GibbsCoordinateTower.action μ (fun t => {E t}) A k)
        (MixedInfluenceBudget.iterate c E k) ∧
      (∀ i j, 0 ≤ MixedInfluenceBudget.iterate c E k i j) ∧
      (∀ i j, MixedInfluenceBudget.iterate c E k i j =
        MixedInfluenceBudget.iterate c E k j i) ∧
      (∀ i, MixedInfluenceBudget.iterate c E k i i = 0) ∧
      (∀ i, ∑ j, MixedInfluenceBudget.iterate c E k i j ≤ α) := by
  intro k
  have hp := MixedInfluenceBudget.iterate_properties c hc hsym hdiag α hα0 hα1 hrow E k
  refine ⟨?_, hp⟩
  clear hp
  induction k with
  | zero => exact hA
  | succ k ih =>
      have hs := (MixedInfluenceBudget.iterate_properties c hc hsym hdiag α hα0 hα1 hrow E k).2.1
      exact singleAction_mixed μ (GibbsCoordinateTower.action μ (fun t => {E t}) A k)
        (MixedInfluenceBudget.iterate c E k) hs ih (E k)

/-- The all-depth bound controls actual conditional expectations of the exact stage action. -/
theorem tower_localInfluence (A : C(I → X, ℝ)) (c : I → I → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hA : MixedBound A c)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hrow : ∀ i, ∑ j, c i j ≤ α)
    (E : ℕ → I) (k : ℕ) :
    ParallelOscillation.LocalInfluence
      (fun i U => CompactGibbsContinuity.law μ
        (fun q => GibbsCoordinateTower.action μ (fun t => {E t}) A k (Function.update U i q)))
      (MixedInfluenceBudget.iterate c E k) := by
  let B := GibbsCoordinateTower.action μ (fun t => {E t}) A k
  let Φ : Unit → (I → X) → ℝ := fun _ => B
  have hΦ : action Φ = (B : (I → X) → ℝ) := by
    funext U
    simp [action, Φ]
  have hm : FiniteFactorInfluence.MixedOscillationBound Φ
      (fun i j => 4 * MixedInfluenceBudget.iterate c E k i j) := by
    rw [← factor_mixedBound_iff, hΦ]
    exact (uniform_tower μ A c hc hsym hdiag hA α hα0 hα1 hrow E k).1
  have h := FiniteFactorInfluence.localInfluence_of_mixed μ Φ (fun _ => B.continuous) _ hm
  change ParallelOscillation.LocalInfluence
    (fun i U => CompactGibbsContinuity.law μ (fun q => action Φ (Function.update U i q)))
    (fun i j => (4 * MixedInfluenceBudget.iterate c E k i j) / 4) at h
  simpa only [hΦ, mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using h

end
end UnifiedTheory.Clay.YangMills.MixedEliminationTower
