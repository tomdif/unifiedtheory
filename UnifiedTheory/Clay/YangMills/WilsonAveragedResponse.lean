/- Averaged physical-transfer response and actual local tilt covariance.
The squared response is O(beta), rather than the O(beta^2) obtained by
squaring the pointwise range estimate. This is not a contraction theorem. -/
import UnifiedTheory.Clay.YangMills.WilsonStationaryEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAveragedResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse
open WilsonSymmetricLinkChange WilsonStationaryEntropy CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

theorem rowMean_eq_raw (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    rowMean n β hβ f u = ∫ v, rawTransition n β hβ u v * f v ∂measure n :=
  rowLaw_integral n β hβ u f

theorem rowMean_continuous (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Continuous (rowMean n β hβ f) := by
  have he : rowMean n β hβ f = fun u => ∫ v, rawTransition n β hβ u v * f v ∂measure n :=
    funext (rowMean_eq_raw n β hβ f)
  rw [he]
  exact GibbsMarginalTower.fiber_integral_continuous (measure n) _
    ((rawTransition_continuous n β hβ).mul (f.continuous.comp continuous_snd))

theorem response_sq_le_rowEntropy (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (rowMean n β hβ f u-rowMean n β hβ f w)^2 ≤ (hi-lo)^2 * rowEntropy n β hβ u w := by
  rw [rowMean_eq_raw, rowMean_eq_raw]
  exact response_sq_le_entropy (measure n) _ _ f
    (row_continuous n β hβ u) (row_continuous n β hβ w) f.continuous
    (rawTransition_pos n β hβ u) (rawTransition_pos n β hβ w)
    (rawTransition_mass n β hβ u) (rawTransition_mass n β hβ w) lo hi hf

/-- Actual stationary mean-square sensitivity, uniform in the spatial volume. -/
theorem mean_response_sq_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ))
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, (rowMean n β hβ f u-rowMean n β hβ f (shift n e q u))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 66*β*(hi-lo)^2*‖(q : ℍ)-1‖^2 := by
  have hp := rowMean_continuous n β hβ f
  have hd : Continuous (fun u =>
      (rowMean n β hβ f u-rowMean n β hβ f (shift n e q u))^2) :=
    (hp.sub (hp.comp (shift_continuous n e q))).pow 2
  have he : Continuous (fun u => rowEntropy n β hβ u (shift n e q u)) :=
    (rowEntropy_continuous n β hβ).comp (f := fun u : Slice n => (u,shift n e q u))
      (continuous_id.prodMk (shift_continuous n e q))
  have hg := (ground n β hβ).continuous.pow 2
  have h := integral_mono (continuous_integrable (measure n) _ (hg.mul hd))
    (continuous_integrable (measure n) _ (hg.mul (continuous_const.mul he)))
    (fun u => mul_le_mul_of_nonneg_left
      (response_sq_le_rowEntropy n β hβ u (shift n e q u) f lo hi hf) (sq_nonneg _))
  have hfactor : (∫ u, (ground n β hβ u)^2 *
      ((hi-lo)^2 * rowEntropy n β hβ u (shift n e q u)) ∂measure n) =
      (hi-lo)^2 * meanEntropy n β hβ e q := by
    unfold meanEntropy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    ring
  simp only [Pi.mul_apply] at h
  rw [hfactor] at h
  rw [WilsonGroundHeatBath.groundLaw, GroundStateDirichlet.stationary_integral
    (measure n) (ground n β hβ) (ground n β hβ).continuous]
  have hb := mul_le_mul_of_nonneg_left (meanEntropy_bound n β hβ e q) (sq_nonneg (hi-lo))
  nlinarith

/-- The estimate is bound to the original full transfer on physical observables. -/
theorem physical_response_sq_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ))
    (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, ((∫ v, transition n β hβ u v * f v ∂measure n) -
      (∫ v, transition n β hβ (shift n e q u) v * f v ∂measure n))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 66*β*(hi-lo)^2*‖(q : ℍ)-1‖^2 := by
  simp_rw [← rowMean_eq_full n β hβ f hinv]
  exact mean_response_sq_bound n β hβ e q f lo hi hf

/-- The literal one-link tilt covariance, with its true row-dependent denominator. -/
theorem covariance_mean_square_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ))
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, (tiltCovariance n β hβ {e} (shift n e q u) u f /
      (∫ v, tilt n β {e} (shift n e q u) u v ∂rowLaw n β hβ u))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 66*β*(hi-lo)^2*‖(q : ℍ)-1‖^2 := by
  have he (u : Slice n) : tiltCovariance n β hβ {e} (shift n e q u) u f /
      (∫ v, tilt n β {e} (shift n e q u) u v ∂rowLaw n β hβ u) =
      rowMean n β hβ f (shift n e q u)-rowMean n β hβ f u := by
    have hu : ∀ j, j ∉ ({e} : Finset _) → shift n e q u j = u j := by
      intro j hj
      exact shift_away n e q u j (by simpa only [Finset.mem_singleton] using hj)
    rw [covariance_eq_response_mul n β hβ {e} _ u hu,
      mul_div_cancel_right₀ _ (tilt_mean_pos n β hβ {e} _ u hu).ne']
  have h := mean_response_sq_bound n β hβ e q f lo hi hf
  convert h using 1
  apply integral_congr_ae
  filter_upwards with u
  rw [he, sub_sq_comm]

end
end UnifiedTheory.Clay.YangMills.WilsonAveragedResponse
