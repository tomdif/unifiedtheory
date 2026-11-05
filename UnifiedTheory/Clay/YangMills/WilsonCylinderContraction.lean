/- Actual random-color contraction on arbitrary-length open Wilson cylinders.
The local influence and product-update identities are derived from the original
full-endpoint action. The rate is independent of spatial volume and time length. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderConditionalInfluence
import UnifiedTheory.Clay.YangMills.WilsonCylinderParallelKernel
import UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderContraction
noncomputable section
open MeasureTheory RegulatedGauge WilsonCylinderGeometry WilsonCylinderConditionalInfluence
open ParallelOscillation WilsonSingleLinkStaples

variable (n L : ℕ) [NeZero n]

local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n L) := Classical.decEq _
local instance colorDecidableEq : DecidableEq WilsonCylinderColors.Color := Classical.decEq _
local instance coordinateProbability (β : ℝ) (a : Link n L) (U : State n L) :
    IsProbabilityMeasure (coordinateLaw n L β U a) := coordinateLaw_probability n L β U a

/-- The original full open-cylinder Wilson probability in flat positive-link coordinates. -/
def law (β : ℝ) : Measure (State n L) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : Link n L => compactHaar Q))
    (stateAction n L β)

instance law_probability (β : ℝ) : IsProbabilityMeasure (law n L β) :=
  CompactGibbsContinuity.law_probability _ _ (stateAction n L β).continuous

/-- One actual auxiliary update chooses one of the eight independent geometric colors uniformly. -/
def update (β : ℝ) (heven : 2 ∣ n) (F : C(State n L, ℝ)) : C(State n L, ℝ) :=
  (1 / 8 : ℝ) • ∑ c : WilsonCylinderColors.Color,
    CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
      (WilsonCylinderColors.colorBlock n L heven c) F

theorem update_apply (β : ℝ) (heven : 2 ∣ n) (F : C(State n L, ℝ)) (U : State n L) :
    update n L β heven F U = (1 / 8 : ℝ) * ∑ c : WilsonCylinderColors.Color,
      CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
        (WilsonCylinderColors.colorBlock n L heven c) F U := by
  simp only [update, ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]

/-- Stationarity is derived from the actual Gibbs conditional block operators. -/
theorem update_stationary (β : ℝ) (heven : 2 ∣ n) (F : C(State n L, ℝ)) :
    (∫ U, update n L β heven F U ∂law n L β) = ∫ U, F U ∂law n L β := by
  simp only [update_apply, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun c _ =>
    (CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
      (WilsonCylinderColors.colorBlock n L heven c) F).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp_rw [law, CompactGibbsBlockUpdate.blockAverage_stationary]
  simp only [Finset.sum_const, Finset.card_univ, WilsonCylinderColors.color_card, nsmul_eq_mul]
  ring

/-- Reversibility of the genuine random-color update in the original Wilson law. -/
theorem update_reversible (β : ℝ) (heven : 2 ∣ n) (F H : C(State n L, ℝ)) :
    (∫ U, F U * update n L β heven H U ∂law n L β) =
      ∫ U, update n L β heven F U * H U ∂law n L β := by
  have hleft (U : State n L) : F U * update n L β heven H U =
      (1 / 8 : ℝ) * ∑ c : WilsonCylinderColors.Color, F U *
        CompactGibbsBlockUpdate.blockAverage (compactHaar Q)
          (stateAction n L β)
          (WilsonCylinderColors.colorBlock n L heven c) H U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) (1 / 8), mul_assoc, Finset.mul_sum]
  have hright (U : State n L) : update n L β heven F U * H U =
      (1 / 8 : ℝ) * ∑ c : WilsonCylinderColors.Color,
        CompactGibbsBlockUpdate.blockAverage (compactHaar Q)
          (stateAction n L β) (WilsonCylinderColors.colorBlock n L heven c) F U *
            H U := by
    rw [update_apply, mul_assoc, Finset.sum_mul]
  simp_rw [hleft, hright]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hiL (c : WilsonCylinderColors.Color) : Integrable (fun U : State n L => F U *
      CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
        (WilsonCylinderColors.colorBlock n L heven c) H U) (law n L β) :=
    (F.continuous.mul (CompactGibbsBlockUpdate.blockAverage (compactHaar Q)
      (stateAction n L β)
        (WilsonCylinderColors.colorBlock n L heven c) H).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hiR (c : WilsonCylinderColors.Color) : Integrable (fun U : State n L =>
      CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
        (WilsonCylinderColors.colorBlock n L heven c) F U * H U) (law n L β) :=
    ((CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
      (WilsonCylinderColors.colorBlock n L heven c) F).continuous.mul
        H.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hiL c),
    integral_finset_sum Finset.univ (fun c _ => hiR c)]
  apply Finset.sum_congr rfl
  intro c _
  exact CompactGibbsBlockUpdate.blockAverage_reversible (compactHaar Q)
    (stateAction n L β) (WilsonCylinderColors.colorBlock n L heven c) F H

theorem update_const (β : ℝ) (heven : 2 ∣ n) (c : ℝ) :
    update n L β heven (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext U
  rw [update_apply]
  simp only [CompactGibbsBlockUpdate.blockAverage_const, ContinuousMap.const_apply,
    Finset.sum_const, Finset.card_univ, WilsonCylinderColors.color_card, nsmul_eq_mul]
  ring

theorem update_sub (β : ℝ) (heven : 2 ∣ n) (F H : C(State n L, ℝ)) :
    update n L β heven (F - H) = update n L β heven F - update n L β heven H := by
  simp only [update, CompactGibbsBlockUpdate.blockAverage_sub, Finset.sum_sub_distrib, smul_sub]

/-- The continuous actual Gibbs update is the literal product color update used in the estimates. -/
theorem update_eq_colorAverage (β : ℝ) (heven : 2 ∣ n) (F : C(State n L, ℝ)) (U : State n L) :
    update n L β heven F U = colorAverage (fun a V => coordinateLaw n L β V a)
      (WilsonCylinderColors.color n L heven) F U := by
  rw [update_apply]
  unfold colorAverage
  rw [WilsonCylinderColors.color_card]
  norm_num only [Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [WilsonCylinderParallelKernel.blockAverage_eq_parallelAverage n L β U _
    (WilsonCylinderColors.colorBlock_independent n L heven c) F]
  congr 1

/-- The actual one-site conditional laws satisfy the local influence premise. -/
theorem localInfluence (β : ℝ) (hβ : 0 ≤ β) :
    LocalInfluence (fun a U => coordinateLaw n L β U a)
      (FiniteIncidenceInfluence.coefficient (incidentLinks n L) β) := by
  exact WilsonCylinderConditionalInfluence.localInfluence n L β hβ

/-- The explicit auxiliary update rate, independent of the lattice volume. -/
def rate (β : ℝ) : ℝ := 1 - (1 - 36 * β) / 8

omit [NeZero n] in
theorem rate_eq_colorRate (β : ℝ) :
    rate β = colorRate (Color := WilsonCylinderColors.Color) (36 * β) := by
  unfold rate colorRate
  rw [WilsonCylinderColors.color_card]
  norm_num

omit [NeZero n] in
theorem rate_nonneg (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ rate β := by
  rw [rate_eq_colorRate]
  exact colorRate_nonneg _ (by positivity)

omit [NeZero n] in
theorem rate_lt_one (β : ℝ) (hβ : β < 1 / 36) : rate β < 1 := by
  rw [rate_eq_colorRate]
  apply colorRate_lt_one
  linarith

/-- Actual Wilson conditional influences yield the full, volume-independent color budget rate. -/
theorem iterate_expectation_error (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n L, ℝ)) (d : Link n L → ℝ)
    (hF : FiniteProductInfluence.OscBound F d) (hd : ∀ a, 0 ≤ d a)
    (k : ℕ) (U : State n L) :
    |updateIterate (update n L β heven) k F U - ∫ V, F V ∂law n L β| ≤
      rate β ^ k * ∑ a, d a := by
  simpa only [← rate_eq_colorRate] using
    stationary_error (fun a V => coordinateLaw n L β V a) (WilsonCylinderColors.color n L heven)
      (FiniteIncidenceInfluence.coefficient (incidentLinks n L) β) (localInfluence n L β hβ)
      (FiniteIncidenceInfluence.coefficient_nonneg (incidentLinks n L) β hβ) (update n L β heven)
      (update_eq_colorAverage n L β heven) (law n L β) (update_stationary n L β heven)
      F d hF hd (36 * β) (by positivity)
      (WilsonCylinderInfluenceGeometry.coefficient_row_le n L β hβ) k U

/-- Every centered continuous observable has a proved geometric moment bound for the actual law. -/
theorem centered_moment_bound (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n L, ℝ)) (hmean : (∫ U, F U ∂law n L β) = 0) (k : ℕ) :
    |∫ U, F U * updateIterate (update n L β heven) k F U ∂law n L β| ≤
      (2 * Fintype.card (Link n L) * ‖F‖ ^ 2) * rate β ^ k := by
  simpa only [← rate_eq_colorRate] using
    stationary_correlation_uniform (fun a V => coordinateLaw n L β V a)
      (WilsonCylinderColors.color n L heven)
      (FiniteIncidenceInfluence.coefficient (incidentLinks n L) β)
      (localInfluence n L β hβ)
      (FiniteIncidenceInfluence.coefficient_nonneg (incidentLinks n L) β hβ)
      (update n L β heven) (update_eq_colorAverage n L β heven) (law n L β)
      (update_stationary n L β heven) F hmean (36 * β) (by positivity)
      (WilsonCylinderInfluenceGeometry.coefficient_row_le n L β hβ) k

/-- Actual strong-coupling sampler convergence for every continuous test, from any initial state. -/
theorem iterate_expectation_tendsto (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36)
    (heven : 2 ∣ n) (F : C(State n L, ℝ)) (U : State n L) :
    Filter.Tendsto (fun k => updateIterate (update n L β heven) k F U) Filter.atTop
      (nhds (∫ V, F V ∂law n L β)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => iterate_expectation_error n L β hβ heven F (fun _ => 2 * ‖F‖)
      (uniform_oscillation F) (fun _ => by positivity) k U)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (rate_nonneg β hβ)
    (rate_lt_one β hsmall)).mul_const (∑ _a : Link n L, 2 * ‖F‖)


theorem iterate_eq (β : ℝ) (heven : 2 ∣ n) (F : C(State n L, ℝ)) (k : ℕ) :
    ContinuousUpdateGap.iterate (update n L β heven) k F =
      updateIterate (update n L β heven) k F := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ContinuousUpdateGap.iterate, updateIterate, ih]

/-- The actual cylinder law has an L2 contraction rate independent of both cutoffs. -/
theorem centered_norm_contraction (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n L, ℝ)) (hmean : (∫ U, F U ∂law n L β) = 0) :
    ‖ContinuousMap.toLp 2 (law n L β) ℝ (update n L β heven F)‖ ≤
      rate β * ‖ContinuousMap.toLp 2 (law n L β) ℝ F‖ := by
  apply ContinuousUpdateContraction.norm_le_of_moments (law n L β) (update n L β heven)
    (update_reversible n L β heven) F (rate β)
    (2 * Fintype.card (Link n L) * ‖F‖^2) (rate_nonneg β hβ)
  intro k
  simpa only [ContinuousUpdateGap.pairing, iterate_eq] using
    centered_moment_bound n L β hβ heven F hmean k

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderContraction
