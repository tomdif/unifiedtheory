/- Actual continuous-observable L2 contraction for the original Wilson
probability and its auxiliary random-color update. -/
import UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction
import UnifiedTheory.Clay.YangMills.WilsonParallelPoincare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonParallelL2
noncomputable section
open MeasureTheory WilsonParallelContraction WilsonParallelPoincare
open WilsonIndependentBlocks ParallelOscillation

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Reversibility removes the finite, observable-dependent moment prefactor. -/
theorem centered_norm_contraction (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) :
    ‖ContinuousMap.toLp 2 (law n β) ℝ (update n β heven F)‖ ≤
      rate β * ‖ContinuousMap.toLp 2 (law n β) ℝ F‖ := by
  apply ContinuousUpdateContraction.norm_le_of_moments (law n β) (update n β heven)
    (update_reversible n β heven) F (rate β)
    (2 * Fintype.card (Link n) * ‖F‖ ^ 2) (rate_nonneg β hβ)
  intro k
  simpa only [ContinuousUpdateGap.pairing, iterate_eq] using
    centered_moment_bound n β hβ heven F hmean k

/-- Every power contracts in the actual L2 norm, with no volume prefactor. -/
theorem centered_iterate_norm (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) (k : ℕ) :
    ‖ContinuousMap.toLp 2 (law n β) ℝ (updateIterate (update n β heven) k F)‖ ≤
      rate β ^ k * ‖ContinuousMap.toLp 2 (law n β) ℝ F‖ := by
  induction k with
  | zero => simp only [updateIterate, pow_zero, one_mul, le_refl]
  | succ k ih =>
    have hm : (∫ U, updateIterate (update n β heven) k F U ∂law n β) = 0 := by
      rw [updateIterate_mean (law n β) (update n β heven)
        (update_stationary n β heven), hmean]
    calc
      _ ≤ rate β * ‖ContinuousMap.toLp 2 (law n β) ℝ
          (updateIterate (update n β heven) k F)‖ :=
        centered_norm_contraction n β hβ heven _ hm
      _ ≤ rate β * (rate β ^ k * ‖ContinuousMap.toLp 2 (law n β) ℝ F‖) :=
        mul_le_mul_of_nonneg_left ih (rate_nonneg β hβ)
      _ = _ := by rw [pow_succ]; ring

/-- The prefactor is exactly the product of actual L2 norms. -/
theorem centered_pairing_decay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F G : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) (k : ℕ) :
    |∫ U, updateIterate (update n β heven) k F U * G U ∂law n β| ≤
      rate β ^ k * ‖ContinuousMap.toLp 2 (law n β) ℝ F‖ *
        ‖ContinuousMap.toLp 2 (law n β) ℝ G‖ := by
  exact (ContinuousUpdateContraction.abs_pairing_le (law n β) _ G).trans
    (mul_le_mul_of_nonneg_right (centered_iterate_norm n β hβ heven F hmean k)
      (norm_nonneg _))

end
end UnifiedTheory.Clay.YangMills.WilsonParallelL2
