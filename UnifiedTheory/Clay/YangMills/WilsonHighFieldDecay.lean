/- Actual L2 decay for observables supported on high total spatial energy.
The ground amplitude and transfer normalization are retained throughout.
For physical observables, the step is the original full Wilson transfer. -/
import UnifiedTheory.Clay.YangMills.WilsonHighFieldNormalization
import UnifiedTheory.Clay.YangMills.WilsonAxialAlignment
import UnifiedTheory.Clay.YangMills.WilsonSpatialSourceObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHighFieldDecay
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse WilsonAveragedResponse
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHighFieldNormalization CompactDensityEntropy
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]

def mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, (f u)^2 ∂groundLaw n β hβ

theorem mass_nonneg (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : 0 ≤ mass n β hβ f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem mass_ground (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ f = ∫ u, (ground n β hβ u*f u)^2 ∂WilsonSlabOperator.measure n := by
  rw [mass, groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  simp only [mul_pow]

theorem l1_square_le_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, |ground n β hβ u*f u| ∂WilsonSlabOperator.measure n)^2 ≤ mass n β hβ f := by
  have hc : Continuous (fun u => |ground n β hβ u*f u|) :=
    ((ground n β hβ).continuous.mul f.continuous).abs
  have h := ProbabilityTheory.variance_nonneg (fun u => |ground n β hβ u*f u|)
    (WilsonSlabOperator.measure n)
  rw [CompactLikelihoodVariance.variance_formula _ _ hc] at h
  simp only [sq_abs] at h
  rw [mass_ground]
  linarith

theorem ground_step (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    ground n β hβ u*step n β hβ f u =
      (∫ v, rawKernel character β 2 u v*ground n β hβ v*f v
        ∂WilsonSlabOperator.measure n)/‖transfer n β‖ := by
  change ground n β hβ u*rowMean n β hβ f u = _
  rw [rowMean_eq_raw, ← integral_const_mul, ← integral_div]
  apply integral_congr_ae
  filter_upwards with v
  unfold rawTransition
  field_simp [(ground_pos n β hβ u).ne',
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne']

theorem kernel_output_bound (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (u v : Slice n)
    (hv : R ≤ potential character 2 v) :
    rawKernel character β 2 u v ≤ Real.exp (-β*R/2) := by
  have hu : spatialWeight character β 2 u ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
      (WilsonSlabBounds.potential_bounds n u).1
  have hk : kineticWeight character β 2 u v ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hT : 0 ≤ kineticAction character 2 u v := by
      rw [WilsonAxialAlignment.kinetic_eq_sum]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) hT
  have hw : spatialWeight character β 2 v ≤ Real.exp (-β*R/2) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hv hβ
    change -(β/2)*potential character 2 v ≤ _
    linarith
  have h1 : spatialWeight character β 2 u*kineticWeight character β 2 u v ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hu hk (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)
  simpa only [rawKernel, one_mul] using
    mul_le_mul h1 hw (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)

theorem weighted_kernel_bound (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < R → f v = 0) (u v : Slice n) :
    |rawKernel character β 2 u v*ground n β hβ v*f v| ≤
      Real.exp (-β*R/2)*|ground n β hβ v*f v| := by
  by_cases hv : R ≤ potential character 2 v
  · rw [mul_assoc, abs_mul, abs_of_pos (rawKernel_pos _ _ _ _ _)]
    exact mul_le_mul_of_nonneg_right (kernel_output_bound n β hβ R u v hv) (abs_nonneg _)
  · simp only [hs v (lt_of_not_ge hv), mul_zero, abs_zero, le_refl]

theorem amplitude_bound (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < R → f v = 0) (u : Slice n) :
    |ground n β hβ u*step n β hβ f u| ≤
      Real.exp (-β*R/2)*(∫ v, |ground n β hβ v*f v| ∂WilsonSlabOperator.measure n)/
        ‖transfer n β‖ := by
  have hk := (rawKernel_continuous character character_continuous β 2 (n := n)).comp
    (f := fun v : Slice n => (u,v)) (continuous_const.prodMk continuous_id)
  have hg := (ground n β hβ).continuous
  have hi := integral_mono
    (continuous_integrable (WilsonSlabOperator.measure n) _ (((hk.mul hg).mul f.continuous).abs))
    ((continuous_integrable (WilsonSlabOperator.measure n) _ (hg.mul f.continuous).abs).const_mul
      (Real.exp (-β*R/2))) (weighted_kernel_bound n β hβ R f hs u)
  rw [integral_const_mul] at hi
  have ha : |∫ v, rawKernel character β 2 u v*ground n β hβ v*f v
      ∂WilsonSlabOperator.measure n| ≤
      ∫ v, |rawKernel character β 2 u v*ground n β hβ v*f v| ∂WilsonSlabOperator.measure n := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun v => rawKernel character β 2 u v*ground n β hβ v*f v)
  rw [ground_step, abs_div, abs_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1]
  exact div_le_div_of_nonneg_right (ha.trans hi) (norm_nonneg _)

theorem squared_amplitude_bound (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < R → f v = 0) (u : Slice n) :
    (ground n β hβ u*step n β hβ f u)^2 ≤
      (Real.exp (-β*R)/‖transfer n β‖^2)*mass n β hβ f := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (amplitude_bound n β hβ R f hs u) 2
  simp only [sq_abs, div_pow, mul_pow] at h
  have he : (Real.exp (-β*R/2))^2 = Real.exp (-β*R) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left (l1_square_le_mass n β hβ f)
    (show 0 ≤ Real.exp (-β*R)/‖transfer n β‖^2 by positivity)
  apply le_trans _ hm
  convert h using 1 <;> ring

theorem mass_decay_factor (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < R → f v = 0) :
    mass n β hβ (step n β hβ f) ≤
      (Real.exp (-β*R)/‖transfer n β‖^2)*mass n β hβ f := by
  rw [mass_ground]
  have h := integral_mono
    (continuous_integrable (WilsonSlabOperator.measure n) _
      (((ground n β hβ).continuous.mul (step n β hβ f).continuous).pow 2))
    (integrable_const _) (squared_amplitude_bound n β hβ R f hs)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem loss_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    loss n β hβ f = mass n β hβ f-mass n β hβ (step n β hβ f) := by
  unfold loss mass
  rw [variance_formula, variance_formula, stationary_mean]
  ring

/-- Actual high-density modes decay, including sources concentrated on the
high-energy region. This does not discard their variance-pair contribution. -/
theorem highfield_decay (β : ℝ) (hβ : 0 < β) (r : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < r * links n → f v = 0) :
    mass n β hβ.le (step n β hβ.le f) ≤ rate n β r*mass n β hβ.le f :=
  (mass_decay_factor n β hβ.le (r * links n) f hs).trans
    (mul_le_mul_of_nonneg_right (normalized_factor n β r hβ) (mass_nonneg n β hβ.le f))

theorem highfield_loss (β : ℝ) (hβ : 0 < β) (r : ℝ) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < r * links n → f v = 0) :
    (1-rate n β r)*mass n β hβ.le f ≤ loss n β hβ.le f := by
  rw [loss_mass]
  have h := highfield_decay n β hβ r f hs
  linarith

/-- Once the proved free-energy price is below r / 2, the decay bound is
independent of the spatial period. -/
theorem uniform_highfield_decay (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 ≤ r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < r * links n → f v = 0) :
    mass n β hβ.le (step n β hβ.le f) ≤ Real.exp (-β*r / 2)*mass n β hβ.le f :=
  (highfield_decay n β hβ r f hs).trans
    (mul_le_mul_of_nonneg_right (rate_uniform n β r hβ.le hr he) (mass_nonneg n β hβ.le f))

theorem uniform_highfield_loss (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 ≤ r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) (f : C(Slice n, ℝ))
    (hs : ∀ v, potential character 2 v < r * links n → f v = 0) :
    (1-Real.exp (-β*r / 2))*mass n β hβ.le f ≤ loss n β hβ.le f := by
  rw [loss_mass]
  have h := uniform_highfield_decay n β hβ r hr he f hs
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonHighFieldDecay
