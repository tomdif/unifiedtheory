/- Quantitative convergence of normalized square densities from real L² amplitudes. -/
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SquaredDensityConvergence
noncomputable section
open MeasureTheory
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual real L² norm of a continuous amplitude. -/
def amplitudeNorm (f : C(X, ℝ)) : ℝ := ‖ContinuousMap.toLp 2 μ ℝ f‖

theorem amplitudeNorm_sq (f : C(X, ℝ)) :
    amplitudeNorm μ f ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h := MeasureTheory.ContinuousMap.inner_toLp μ f f
  simpa only [real_inner_self_eq_norm_sq, RCLike.inner_apply, star_trivial, sq] using h

theorem amplitudeNorm_complex (f : C(X, ℝ)) :
    amplitudeNorm μ f =
      ‖ContinuousMap.toLp 2 μ ℂ (WilsonPositiveGroundState.complexify f)‖ := by
  have h := WilsonPositiveGroundState.real_embedding_norm_sq μ f
  rw [← amplitudeNorm_sq] at h
  have h0 : 0 ≤ amplitudeNorm μ f := norm_nonneg _
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 μ ℂ
    (WilsonPositiveGroundState.complexify f))]

theorem amplitudeNorm_sub_le (f g : C(X, ℝ)) :
    amplitudeNorm μ (f - g) ≤ amplitudeNorm μ f + amplitudeNorm μ g := by
  unfold amplitudeNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem amplitudeNorm_add_le (f g : C(X, ℝ)) :
    amplitudeNorm μ (f + g) ≤ amplitudeNorm μ f + amplitudeNorm μ g := by
  unfold amplitudeNorm
  rw [map_add]
  exact norm_add_le _ _

theorem amplitudeNorm_smul (c : ℝ) (f : C(X, ℝ)) :
    amplitudeNorm μ (c • f) = |c| * amplitudeNorm μ f := by
  simp only [amplitudeNorm, map_smul, norm_smul, Real.norm_eq_abs]

theorem product_integral_bound (f g : C(X, ℝ)) :
    |∫ x, f x * g x ∂μ| ≤ amplitudeNorm μ f * amplitudeNorm μ g := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (ContinuousMap.toLp 2 μ ℝ f)
    (ContinuousMap.toLp 2 μ ℝ g)
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa [amplitudeNorm, mul_comm] using h

theorem amplitudeNorm_mul_le (f g : C(X, ℝ)) :
    amplitudeNorm μ (f * g) ≤ ‖f‖ * amplitudeNorm μ g := by
  have hsq : amplitudeNorm μ (f * g) ^ 2 ≤ (‖f‖ * amplitudeNorm μ g) ^ 2 := by
    rw [amplitudeNorm_sq, mul_pow, amplitudeNorm_sq, ← integral_const_mul]
    apply integral_mono
    · exact ((f * g).continuous.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ((continuous_const.mul (g.continuous.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · intro x
      simp only [ContinuousMap.mul_apply, mul_pow]
      have hb := ContinuousMap.norm_coe_le_norm f x
      have hs : f x ^ 2 ≤ ‖f‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have h0 : 0 ≤ amplitudeNorm μ (f * g) := norm_nonneg _
  have h1 : 0 ≤ ‖f‖ * amplitudeNorm μ g := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Unit L² amplitudes give a bounded-test square-density estimate. -/
theorem unit_square_expectation (u v F : C(X, ℝ))
    (hu : amplitudeNorm μ u = 1) (hv : amplitudeNorm μ v = 1) :
    |(∫ x, u x ^ 2 * F x ∂μ) - (∫ x, v x ^ 2 * F x ∂μ)| ≤
      2 * ‖F‖ * amplitudeNorm μ (u - v) := by
  have hiu : Integrable (fun x => u x ^ 2 * F x) μ :=
    ((u.continuous.pow 2).mul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiv : Integrable (fun x => v x ^ 2 * F x) μ :=
    ((v.continuous.pow 2).mul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hiu hiv]
  have he : (fun x => u x ^ 2 * F x - v x ^ 2 * F x) =
      (fun x => (F * (u - v)) x * (u + v) x) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply]
    ring
  rw [he]
  calc
    _ ≤ amplitudeNorm μ (F * (u - v)) * amplitudeNorm μ (u + v) :=
      product_integral_bound μ _ _
    _ ≤ (‖F‖ * amplitudeNorm μ (u - v)) * (1 + 1) := by
      apply mul_le_mul (amplitudeNorm_mul_le μ F (u - v))
        (by simpa only [hu, hv] using amplitudeNorm_add_le μ u v)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- Normalization is quantitatively stable relative to any positive target scale. -/
theorem normalize_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : 0 < ‖x‖) (hy : ‖y‖ = 1) (c : ℝ) (hc : 0 < c) :
    ‖‖x‖⁻¹ • x - y‖ ≤ 2 / c * ‖x - c • y‖ := by
  have hreverse : |‖x‖ - c| ≤ ‖x - c • y‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, hy, mul_one] using
      abs_norm_sub_norm_le x (c • y)
  have hfirst : ‖‖x‖⁻¹ • x - c⁻¹ • x‖ = |‖x‖ - c| / c := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have he : ‖x‖⁻¹ - c⁻¹ = (c - ‖x‖) / (c * ‖x‖) := by field_simp
    rw [he, abs_div, abs_mul, abs_of_pos hc, abs_of_pos hx, abs_sub_comm]
    field_simp
  have hsecond : ‖c⁻¹ • x - y‖ = ‖x - c • y‖ / c := by
    rw [show c⁻¹ • x - y = c⁻¹ • (x - c • y) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    ring
  calc
    _ ≤ ‖‖x‖⁻¹ • x - c⁻¹ • x‖ + ‖c⁻¹ • x - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |‖x‖ - c| / c + ‖x - c • y‖ / c := by rw [hfirst, hsecond]
    _ ≤ ‖x - c • y‖ / c + ‖x - c • y‖ / c :=
      add_le_add (div_le_div_of_nonneg_right hreverse hc.le) le_rfl
    _ = _ := by ring

/-- Dividing a nonzero continuous amplitude by its actual L² norm gives unit norm. -/
theorem normalized_amplitude (f : C(X, ℝ)) (hf : 0 < amplitudeNorm μ f) :
    amplitudeNorm μ ((amplitudeNorm μ f)⁻¹ • f) = 1 := by
  rw [amplitudeNorm_smul, abs_inv, abs_of_pos hf, inv_mul_cancel₀ hf.ne']

/-- An arbitrary positive comparison scale can be used in the square-law error. -/
theorem square_law_error (f psi F : C(X, ℝ))
    (hf : 0 < amplitudeNorm μ f) (hpsi : amplitudeNorm μ psi = 1)
    (c : ℝ) (hc : 0 < c) :
    |(∫ x, F x ∂LocalGibbsComparison.weightedLaw μ (fun x => f x ^ 2)) -
      (∫ x, psi x ^ 2 * F x ∂μ)| ≤
      4 * ‖F‖ / c * amplitudeNorm μ (f - c • psi) := by
  have hmass : 0 < ∫ x, f x ^ 2 ∂μ := by
    rw [← amplitudeNorm_sq]
    positivity
  rw [LocalGibbsComparison.weighted_integral μ _ (f.continuous.pow 2).measurable
    (fun x => sq_nonneg _) hmass F]
  let u : C(X, ℝ) := (amplitudeNorm μ f)⁻¹ • f
  have he : (∫ x, f x ^ 2 * F x ∂μ) / (∫ x, f x ^ 2 ∂μ) =
      ∫ x, u x ^ 2 * F x ∂μ := by
    rw [← amplitudeNorm_sq, div_eq_mul_inv, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [u, ContinuousMap.smul_apply, smul_eq_mul, mul_pow, inv_pow]
    ring
  rw [he]
  have hnorm : amplitudeNorm μ (u - psi) ≤
      2 / c * amplitudeNorm μ (f - c • psi) := by
    simpa only [u, amplitudeNorm, map_sub, map_smul] using
      normalize_distance (ContinuousMap.toLp 2 μ ℝ f) (ContinuousMap.toLp 2 μ ℝ psi)
        hf hpsi c hc
  calc
    _ ≤ 2 * ‖F‖ * amplitudeNorm μ (u - psi) :=
      unit_square_expectation μ u psi F (normalized_amplitude μ f hf) hpsi
    _ ≤ 2 * ‖F‖ * (2 / c * amplitudeNorm μ (f - c • psi)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end
end UnifiedTheory.Clay.YangMills.SquaredDensityConvergence
