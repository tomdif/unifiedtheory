/- Computable oscillation bounds for the factors produced by exact integration.
These finite-depth bounds are deliberately conservative. They certify no
weak-coupling entry into a mixing region and assert no uniform RG norm. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorInfluence
import UnifiedTheory.Clay.YangMills.FiniteFactorIteration
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorOscillationTower
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination FiniteFactorInfluence

universe u v
variable {I P : Type u} {X : Type v} [DecidableEq I] [Fintype P]

/-- The explicit conservative successor budget for the actual reference-subtracted factors. -/
def nextWeight (D : P → Finset I) (w : P → ℝ) (T : Finset I) : P ⊕ T → ℝ :=
  Sum.elim w (fun i => 2 * ∑ p ∈ touching D i.val, w p)

theorem nextWeight_nonneg (D : P → Finset I) (w : P → ℝ) (hw : ∀ p, 0 ≤ w p)
    (T : Finset I) (j : P ⊕ T) : 0 ≤ nextWeight D w T j := by
  cases j with
  | inl p => exact hw p
  | inr i => exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ => hw p))

/-- Unaffected factors cancel before the increment is estimated. -/
theorem increment_abs_bound (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw : OscillationBound Φ w) (T : Finset I) (x₀ : X) (i : T) (U : I → X) (q : X) :
    |increment Φ T x₀ i (U, q)| ≤ ∑ p ∈ touching D i.val, w p := by
  unfold increment
  rw [action_increment_eq_sum D Φ hΦ]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hw p _ _))

section Analytic
variable [Finite I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [Finite I] [SecondCountableTopology X] in
/-- The literal generated logarithmic partition has an explicit absolute bound. -/
theorem generated_abs_bound (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (w : P → ℝ) (hw : OscillationBound Φ w) (T : Finset I) (x₀ : X)
    (i : T) (U : I → X) :
    |nextFactor μ Φ T x₀ (.inr i) U| ≤ ∑ p ∈ touching D i.val, w p := by
  have hc := (increment_continuous Φ hΦc T x₀ i).comp
    (continuous_const.prodMk continuous_id : Continuous (fun q : X => (U, q)))
  have h := GibbsMixedInteraction.freeEnergy_difference_bound μ
    (fun q => increment Φ T x₀ i (U, q)) (fun _ => 0) hc continuous_const
    (∑ p ∈ touching D i.val, w p) (fun q => by
      simpa only [sub_zero] using increment_abs_bound D Φ hΦ w hw T x₀ i U q)
  have hzero : GibbsMixedInteraction.freeEnergy μ (fun _ : X => 0) = 0 := by
    simp [GibbsMixedInteraction.freeEnergy]
  rw [hzero, sub_zero] at h
  exact h

omit [Finite I] [SecondCountableTopology X] in
/-- Every successor factor receives a proved oscillation budget, not an assumed bound. -/
theorem nextFactor_oscillation (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (w : P → ℝ) (hw : OscillationBound Φ w) (T : Finset I) (x₀ : X) :
    OscillationBound (nextFactor μ Φ T x₀) (nextWeight D w T) := by
  intro j U V
  cases j with
  | inl p => exact hw p _ _
  | inr i =>
      calc
        _ ≤ |nextFactor μ Φ T x₀ (.inr i) U| + |nextFactor μ Φ T x₀ (.inr i) V| := abs_sub _ _
        _ ≤ (∑ p ∈ touching D i.val, w p) + (∑ p ∈ touching D i.val, w p) :=
          add_le_add (generated_abs_bound μ D Φ hΦc hΦ w hw T x₀ i U)
            (generated_abs_bound μ D Φ hΦc hΦ w hw T x₀ i V)
        _ = nextWeight D w T (.inr i) := by dsimp [nextWeight]; ring

end Analytic

/-- The budget follows exactly the recursively generated support inventory. -/
def weights (D : P → Finset I) (w : P → ℝ) (T : ℕ → Finset I) :
    (k : ℕ) → FiniteFactorIteration.Index P T k → ℝ
  | 0 => w
  | k + 1 => nextWeight (FiniteFactorIteration.supports D T k) (weights D w T k) (T k)

theorem weights_nonneg (D : P → Finset I) (w : P → ℝ) (hw : ∀ p, 0 ≤ w p)
    (T : ℕ → Finset I) : ∀ k j, 0 ≤ weights D w T k j := by
  intro k
  induction k with
  | zero => exact hw
  | succ k ih => exact nextWeight_nonneg _ _ ih _

variable [Finite I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Actual integrated factors at every finite depth satisfy the computed bounds. -/
theorem factors_oscillation (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (w : P → ℝ) (hw : OscillationBound Φ w) (T : ℕ → Finset I) (x₀ : X) :
    ∀ k, OscillationBound (FiniteFactorIteration.factors μ Φ T x₀ k) (weights D w T k) := by
  intro k
  induction k with
  | zero => exact hw
  | succ k ih =>
      exact nextFactor_oscillation μ (FiniteFactorIteration.supports D T k)
        (FiniteFactorIteration.factors μ Φ T x₀ k)
        (FiniteFactorIteration.factors_continuous μ Φ hΦc T x₀ k)
        (FiniteFactorIteration.factors_dependsOn μ D Φ hΦ T x₀ k)
        (weights D w T k) ih (T k) x₀

end
end UnifiedTheory.Clay.YangMills.FiniteFactorOscillationTower
