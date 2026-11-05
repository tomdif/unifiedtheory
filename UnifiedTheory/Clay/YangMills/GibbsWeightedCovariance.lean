/- Weighted covariance bounds for the actual finite Gibbs measure. The
random-site update is eliminated from the final estimate: its site-count
normalization cancels the geometric resolvent denominator. -/
import UnifiedTheory.Clay.YangMills.GibbsSiteCovariance
import UnifiedTheory.Clay.YangMills.WeightedOscillation
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.GibbsWeightedCovariance
noncomputable section
open MeasureTheory Filter ParallelOscillation FiniteProductInfluence GibbsSiteCovariance

/-- A geometric defect estimate plus a vanishing remainder controls the initial value. -/
theorem geometric_defects (a : ℕ → ℝ) (q K : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hstep : ∀ k, |a k - a (k + 1)| ≤ K * (1 - q) * q ^ k)
    (hlim : Tendsto a atTop (nhds 0)) : |a 0| ≤ K := by
  have hfinite (k : ℕ) : |a 0 - a k| ≤ K * (1 - q ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          _ ≤ |a 0 - a k| + |a k - a (k + 1)| := abs_sub_le _ _ _
          _ ≤ K * (1 - q ^ k) + K * (1 - q) * q ^ k := add_le_add ih (hstep k)
          _ = _ := by rw [pow_succ]; ring
  have hcap (k : ℕ) : |a 0 - a k| ≤ K :=
    (hfinite k).trans (by nlinarith [mul_nonneg hK (pow_nonneg hq k)])
  have h := le_of_tendsto ((tendsto_const_nhds.sub hlim).abs)
    (Eventually.of_forall hcap)
  simpa using h

variable {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

set_option maxHeartbeats 1000000 in
-- The covariance telescope combines finite-sum algebra with genuine Gibbs operators.
/-- No number of sites or independent colors appears in the resulting covariance bound. -/
theorem covariance_bound (A F G : C(I → X, ℝ)) (C : I → I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hlocal : LocalInfluence
      (fun i U => CompactGibbsContinuity.law μ (fun q => A (Function.update U i q))) C)
    (u d e : I → ℝ) (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, 0 ≤ d i)
    (hF : OscBound F d) (hG : OscBound G e)
    (α b : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) (hb : 0 ≤ b)
    (hrow : ∀ i, ∑ j, C i j ≤ α)
    (hweighted : ∀ i, ∑ j, C i j * u j ≤ α * u i)
    (he : ∀ i, e i ≤ b * u i) :
    |(∫ U, F U * G U ∂law μ A) -
      (∫ U, F U ∂law μ A) * (∫ U, G U ∂law μ A)| ≤
      b * (∑ i, u i * d i) / (4 * (1 - α)) := by
  let P := update μ A
  let K := b * (∑ i, u i * d i) / (4 * (1 - α))
  let q := colorRate (Color := I) α
  let M := ∫ U, F U ∂law μ A
  let a (k : ℕ) := ∫ U, (updateIterate P k F U - M) * G U ∂law μ A
  let Ksite := fun i U => CompactGibbsContinuity.law μ (fun z => A (Function.update U i z))
  letI (i : I) (U : I → X) : IsProbabilityMeasure (Ksite i U) :=
    CompactGibbsContinuity.law_probability μ _
      (A.continuous.comp (FiniteFactorConditional.update_continuous U i))
  have hP (H : C(I → X, ℝ)) (U : I → X) :
      P H U = colorAverage Ksite (id : I → I) H U := update_eq_colorAverage μ A H U
  have hstat := update_stationary μ A
  have hq0 : 0 ≤ q := colorRate_nonneg α hα
  have hq1 : q < 1 := colorRate_lt_one α hα1
  have hdenpos : 0 < 1 - α := sub_pos.mpr hα1
  have hK0 : 0 ≤ K := div_nonneg
    (mul_nonneg hb (Finset.sum_nonneg (fun i _ => mul_nonneg (hu i) (hd i))))
    (by positivity)
  have hi (H : C(I → X, ℝ)) : Integrable H (law μ A) :=
    H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hstep (k : ℕ) : |a k - a (k + 1)| ≤ K * (1 - q) * q ^ k := by
    let dk := budgetIterate (Color := I) C k d
    have hdk : ∀ i, 0 ≤ dk i := budgetIterate_nonneg C hC d hd k
    have hosc := updateIterate_oscillation Ksite (id : I → I) C hlocal P hP F d hF k
    have ha : a k - a (k + 1) = ∫ U,
        (updateIterate P k F U - P (updateIterate P k F) U) * G U ∂law μ A := by
      have hs := integral_sub
        (hi ((updateIterate P k F - ContinuousMap.const _ M) * G))
        (hi ((updateIterate P (k + 1) F - ContinuousMap.const _ M) * G))
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply] at hs
      dsimp only [a]
      rw [← hs]
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [updateIterate]
      ring
    rw [ha]
    have hsum : (∑ i, dk i * e i) ≤ b * (q ^ k * ∑ i, u i * d i) := by
      calc
        _ ≤ ∑ i, dk i * (b * u i) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he i) (hdk i))
        _ = b * ∑ i, u i * dk i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (WeightedOscillation.weighted_iterate C hC u d hd α hα hweighted k) hb
    calc
      _ ≤ (Fintype.card I : ℝ)⁻¹ * (∑ i, dk i * e i) / 4 :=
        update_defect_bound μ A (updateIterate P k F) G dk e hosc hG
      _ ≤ (Fintype.card I : ℝ)⁻¹ * (b * (q ^ k * ∑ i, u i * d i)) / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity))
          (by norm_num)
      _ = _ := by
        dsimp [K, q, colorRate]
        have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        have hden : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα1)
        field_simp
        ring
  have habs (k : ℕ) : |a k| ≤ ‖G‖ * (q ^ k * ∑ i, d i) := by
    have hp (U : I → X) : |updateIterate P k F U - M| ≤ q ^ k * ∑ i, d i :=
      stationary_error Ksite (id : I → I) C hlocal hC P hP (law μ A) hstat
        F d hF hd α hα hrow k U
    calc
      _ ≤ ∫ U, |(updateIterate P k F U - M) * G U| ∂law μ A :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _U : I → X, ‖G‖ * (q ^ k * ∑ i, d i) ∂law μ A := by
        have hc : Continuous (fun U => |(updateIterate P k F U - M) * G U|) :=
          (((updateIterate P k F).continuous.sub continuous_const).mul G.continuous).abs
        have hj : Integrable (fun U => |(updateIterate P k F U - M) * G U|) (law μ A) :=
          hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        apply integral_mono hj (integrable_const _)
        intro U
        change |(updateIterate P k F U - M) * G U| ≤ ‖G‖ * (q ^ k * ∑ i, d i)
        rw [abs_mul, mul_comm ‖G‖]
        exact mul_le_mul (hp U) (ContinuousMap.norm_coe_le_norm G U) (abs_nonneg _)
          (mul_nonneg (pow_nonneg hq0 k) (Finset.sum_nonneg (fun i _ => hd i)))
      _ = _ := by simp
  have hlim : Tendsto a atTop (nhds 0) := by
    apply squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using habs k)
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (∑ i, d i)).const_mul ‖G‖
  have h := geometric_defects a q K hq0 hK0 hstep hlim
  have ha0 : a 0 = (∫ U, F U * G U ∂law μ A) -
      (∫ U, F U ∂law μ A) * (∫ U, G U ∂law μ A) := by
    dsimp [a, updateIterate]
    simp_rw [sub_mul]
    have hs := integral_sub (hi (F * G)) (hi (ContinuousMap.const _ M * G))
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply] at hs
    rw [hs, integral_const_mul]
  simpa only [ha0] using h

end
end UnifiedTheory.Clay.YangMills.GibbsWeightedCovariance
