/- Actual collective conditional-update contraction for the original SU(2)
Wilson law on an even periodic lattice. The clock counts random color updates;
these estimates do not identify auxiliary dynamics with physical transfer time. -/
import UnifiedTheory.Clay.YangMills.ParallelOscillation
import UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence
import UnifiedTheory.Clay.YangMills.WilsonParallelColors
import UnifiedTheory.Clay.YangMills.WilsonParallelKernel
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonParallelContraction
noncomputable section
open MeasureTheory WilsonIndependentBlocks WilsonCoordinateInfluence ParallelOscillation

abbrev Q := SU2QuaternionEquivalence.UnitQuaternion
abbrev State (n : ℕ) := Link n → Q

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance colorDecidableEq : DecidableEq WilsonParallelColors.Color := Classical.decEq _
local instance coordinateProbability (β : ℝ) (a : Link n) (U : State n) :
    IsProbabilityMeasure (coordinateLaw n β U a) := coordinateLaw_probability n β U a

/-- The original full Wilson probability law in positive-link product coordinates. -/
def law (β : ℝ) : Measure (State n) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => SU2HaarTilt.haar))
    (WilsonParallelKernel.stateAction n β)

instance law_probability (β : ℝ) : IsProbabilityMeasure (law n β) :=
  CompactGibbsContinuity.law_probability _ _ (WilsonParallelKernel.stateAction n β).continuous

/-- One actual auxiliary update chooses one of the eight independent geometric colors uniformly. -/
def update (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) : C(State n, ℝ) :=
  (1 / 8 : ℝ) • ∑ c : WilsonParallelColors.Color,
    CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
      (WilsonParallelColors.colorBlock n heven c) F

omit [Fact (1 < n)] in
theorem update_apply (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) (U : State n) :
    update n β heven F U = (1 / 8 : ℝ) * ∑ c : WilsonParallelColors.Color,
      CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (WilsonParallelColors.colorBlock n heven c) F U := by
  simp only [update, ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]

omit [Fact (1 < n)] in
/-- Stationarity is derived from the actual Gibbs conditional block operators. -/
theorem update_stationary (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) :
    (∫ U, update n β heven F U ∂law n β) = ∫ U, F U ∂law n β := by
  simp only [update_apply, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun c _ =>
    (CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
      (WilsonParallelColors.colorBlock n heven c) F).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp_rw [law, CompactGibbsBlockUpdate.blockAverage_stationary]
  simp only [Finset.sum_const, Finset.card_univ, WilsonParallelColors.color_card, nsmul_eq_mul]
  ring

omit [Fact (1 < n)] in
/-- Reversibility of the genuine random-color update in the original Wilson law. -/
theorem update_reversible (β : ℝ) (heven : 2 ∣ n) (F H : C(State n, ℝ)) :
    (∫ U, F U * update n β heven H U ∂law n β) =
      ∫ U, update n β heven F U * H U ∂law n β := by
  have hleft (U : State n) : F U * update n β heven H U =
      (1 / 8 : ℝ) * ∑ c : WilsonParallelColors.Color, F U *
        CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar
          (WilsonParallelKernel.stateAction n β)
          (WilsonParallelColors.colorBlock n heven c) H U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) (1 / 8), mul_assoc, Finset.mul_sum]
  have hright (U : State n) : update n β heven F U * H U =
      (1 / 8 : ℝ) * ∑ c : WilsonParallelColors.Color,
        CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar
          (WilsonParallelKernel.stateAction n β) (WilsonParallelColors.colorBlock n heven c) F U *
            H U := by
    rw [update_apply, mul_assoc, Finset.sum_mul]
  simp_rw [hleft, hright]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hiL (c : WilsonParallelColors.Color) : Integrable (fun U : State n => F U *
      CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (WilsonParallelColors.colorBlock n heven c) H U) (law n β) :=
    (F.continuous.mul (CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar
      (WilsonParallelKernel.stateAction n β)
        (WilsonParallelColors.colorBlock n heven c) H).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hiR (c : WilsonParallelColors.Color) : Integrable (fun U : State n =>
      CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (WilsonParallelColors.colorBlock n heven c) F U * H U) (law n β) :=
    ((CompactGibbsBlockUpdate.blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
      (WilsonParallelColors.colorBlock n heven c) F).continuous.mul
        H.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hiL c),
    integral_finset_sum Finset.univ (fun c _ => hiR c)]
  apply Finset.sum_congr rfl
  intro c _
  exact CompactGibbsBlockUpdate.blockAverage_reversible SU2HaarTilt.haar
    (WilsonParallelKernel.stateAction n β) (WilsonParallelColors.colorBlock n heven c) F H

omit [Fact (1 < n)] in
theorem update_const (β : ℝ) (heven : 2 ∣ n) (c : ℝ) :
    update n β heven (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext U
  rw [update_apply]
  simp only [CompactGibbsBlockUpdate.blockAverage_const, ContinuousMap.const_apply,
    Finset.sum_const, Finset.card_univ, WilsonParallelColors.color_card, nsmul_eq_mul]
  ring

omit [Fact (1 < n)] in
theorem update_sub (β : ℝ) (heven : 2 ∣ n) (F H : C(State n, ℝ)) :
    update n β heven (F - H) = update n β heven F - update n β heven H := by
  simp only [update, CompactGibbsBlockUpdate.blockAverage_sub, Finset.sum_sub_distrib, smul_sub]

omit [Fact (1 < n)] in
/-- The continuous actual Gibbs update is the literal product color update used in the estimates. -/
theorem update_eq_colorAverage (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) (U : State n) :
    update n β heven F U = colorAverage (fun a V => coordinateLaw n β V a)
      (WilsonParallelColors.color n heven) F U := by
  rw [update_apply]
  unfold colorAverage
  rw [WilsonParallelColors.color_card]
  norm_num only [Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [WilsonParallelKernel.blockAverage_eq_parallelAverage n β U _
    (WilsonParallelColors.colorBlock_independent n heven c) F]
  congr 1
  ext a
  simp only [WilsonParallelColors.mem_colorBlock, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The actual one-site conditional laws satisfy the local influence premise. -/
theorem localInfluence (β : ℝ) (hβ : 0 ≤ β) :
    LocalInfluence (fun a U => coordinateLaw n β U a)
      (WilsonInfluenceGeometry.coefficient n β) := by
  intro a b U V hUV G d hG
  obtain ⟨c, hcd, hb⟩ := interval_of_oscillation G d hG
  have h := coordinateLaw_influence n a b β hβ U V hUV G G.continuous c (c + d) hcd hb
  simpa only [add_sub_cancel_left] using h

/-- The explicit auxiliary update rate, independent of the lattice volume. -/
def rate (β : ℝ) : ℝ := 1 - (1 - 36 * β) / 8

omit [NeZero n] [Fact (1 < n)] in
theorem rate_eq_colorRate (β : ℝ) :
    rate β = colorRate (Color := WilsonParallelColors.Color) (36 * β) := by
  unfold rate colorRate
  rw [WilsonParallelColors.color_card]
  norm_num

omit [NeZero n] [Fact (1 < n)] in
theorem rate_nonneg (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ rate β := by
  rw [rate_eq_colorRate]
  exact colorRate_nonneg _ (by positivity)

omit [NeZero n] [Fact (1 < n)] in
theorem rate_lt_one (β : ℝ) (hβ : β < 1 / 36) : rate β < 1 := by
  rw [rate_eq_colorRate]
  apply colorRate_lt_one
  linarith

/-- Actual Wilson conditional influences yield the full, volume-independent color budget rate. -/
theorem iterate_expectation_error (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (d : Link n → ℝ)
    (hF : FiniteProductInfluence.OscBound F d) (hd : ∀ a, 0 ≤ d a)
    (k : ℕ) (U : State n) :
    |updateIterate (update n β heven) k F U - ∫ V, F V ∂law n β| ≤
      rate β ^ k * ∑ a, d a := by
  simpa only [← rate_eq_colorRate] using
    stationary_error (fun a V => coordinateLaw n β V a) (WilsonParallelColors.color n heven)
      (WilsonInfluenceGeometry.coefficient n β) (localInfluence n β hβ)
      (WilsonInfluenceGeometry.coefficient_nonneg n β hβ) (update n β heven)
      (update_eq_colorAverage n β heven) (law n β) (update_stationary n β heven)
      F d hF hd (36 * β) (by positivity) (WilsonInfluenceGeometry.coefficient_row_le n β hβ) k U

/-- Every centered continuous observable has a proved geometric moment bound for the actual law. -/
theorem centered_moment_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) (k : ℕ) :
    |∫ U, F U * updateIterate (update n β heven) k F U ∂law n β| ≤
      (2 * Fintype.card (Link n) * ‖F‖ ^ 2) * rate β ^ k := by
  simpa only [← rate_eq_colorRate] using
    stationary_correlation_uniform (fun a V => coordinateLaw n β V a)
      (WilsonParallelColors.color n heven) (WilsonInfluenceGeometry.coefficient n β)
      (localInfluence n β hβ) (WilsonInfluenceGeometry.coefficient_nonneg n β hβ)
      (update n β heven) (update_eq_colorAverage n β heven) (law n β)
      (update_stationary n β heven) F hmean (36 * β) (by positivity)
      (WilsonInfluenceGeometry.coefficient_row_le n β hβ) k

/-- Actual strong-coupling sampler convergence for every continuous test, from any initial state. -/
theorem iterate_expectation_tendsto (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36)
    (heven : 2 ∣ n) (F : C(State n, ℝ)) (U : State n) :
    Filter.Tendsto (fun k => updateIterate (update n β heven) k F U) Filter.atTop
      (nhds (∫ V, F V ∂law n β)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => iterate_expectation_error n β hβ heven F (fun _ => 2 * ‖F‖)
      (uniform_oscillation F) (fun _ => by positivity) k U)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (rate_nonneg β hβ)
    (rate_lt_one β hsmall)).mul_const (∑ _a : Link n, 2 * ‖F‖)

end
end UnifiedTheory.Clay.YangMills.WilsonParallelContraction
