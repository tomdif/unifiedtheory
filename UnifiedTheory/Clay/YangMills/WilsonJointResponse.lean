/- Actual response to one simultaneous spatial rotation. The l2 displacement
budget does not sum separate source-range costs over links. The source norm
is still oscillation, not variance dissipation, so no gap is concluded. -/
import UnifiedTheory.Clay.YangMills.WilsonJointEntropy
import UnifiedTheory.Clay.YangMills.QuaternionRotationFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonJointResponse
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonPhysicalResponse WilsonAveragedResponse
open WilsonStationaryEntropy CompactDensityEntropy WilsonJointRotation
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem mean_response_sq_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, (rowMean n β hβ f u-rowMean n β hβ f (q*u))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 18*β*(hi-lo)^2*cost n q := by
  letI := WilsonGroundHeatBath.groundLaw_probability n β hβ
  have hp := rowMean_continuous n β hβ f
  have hd : Continuous (fun u => (rowMean n β hβ f u-rowMean n β hβ f (q*u))^2) :=
    (hp.sub (hp.comp (continuous_const.mul continuous_id))).pow 2
  have he : Continuous (fun u => rowEntropy n β hβ u (q*u)) :=
    (rowEntropy_continuous n β hβ).comp (f := fun u : Slice n => (u,q*u))
      (continuous_id.prodMk (continuous_const.mul continuous_id))
  have h := integral_mono
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _ hd)
    (continuous_integrable (WilsonGroundHeatBath.groundLaw n β hβ) _
      (continuous_const.mul he))
    (fun u => response_sq_le_rowEntropy n β hβ u (q*u) f lo hi hf)
  simp only [Pi.mul_apply] at h
  rw [integral_const_mul] at h
  have hb := WilsonJointEntropy.meanEntropy_bound n β hβ q
  rw [WilsonJointEntropy.meanEntropy_eq_groundLaw] at hb
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (hi-lo))
  nlinarith

/-- Bound to the original full transfer for gauge-invariant observables. -/
theorem physical_response_sq_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) (hinv : ∀ h v, f (gaugeSlice h v) = f v)
    (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, ((∫ v, transition n β hβ u v*f v ∂measure n) -
      (∫ v, transition n β hβ (q*u) v*f v ∂measure n))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 18*β*(hi-lo)^2*cost n q := by
  simp_rw [← rowMean_eq_full n β hβ f hinv]
  exact mean_response_sq_bound n β hβ q f lo hi hf

/-- Literal all-link tilt covariance with its actual row-dependent denominator. -/
theorem covariance_mean_square_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, (tiltCovariance n β hβ Finset.univ (q*u) u f /
      (∫ v, tilt n β Finset.univ (q*u) u v ∂rowLaw n β hβ u))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤ 18*β*(hi-lo)^2*cost n q := by
  have he (u : Slice n) : tiltCovariance n β hβ Finset.univ (q*u) u f /
      (∫ v, tilt n β Finset.univ (q*u) u v ∂rowLaw n β hβ u) =
      rowMean n β hβ f (q*u)-rowMean n β hβ f u := by
    have hu : ∀ j, j ∉ (Finset.univ : Finset (SpatialVertex n × Fin 3)) → (q*u) j = u j := by
      intro j hj
      exact False.elim (hj (Finset.mem_univ j))
    rw [covariance_eq_response_mul n β hβ Finset.univ _ u hu,
      mul_div_cancel_right₀ _ (tilt_mean_pos n β hβ Finset.univ _ u hu).ne']
  have h := mean_response_sq_bound n β hβ q f lo hi hf
  convert h using 1
  apply integral_congr_ae
  filter_upwards with u
  rw [he, sub_sq_comm]

omit [NeZero n] in
def direction (t : ℝ) (a : (SpatialVertex n × Fin 3) → ℝ)
    (axis : (SpatialVertex n × Fin 3) → Fin 3) : Slice n :=
  fun e => QuaternionRotationFrame.rotation (t*a e) (axis e)

theorem direction_cost (t : ℝ) (a : (SpatialVertex n × Fin 3) → ℝ)
    (axis : (SpatialVertex n × Fin 3) → Fin 3) :
    cost n (direction n t a axis) ≤ 4*t^2*∑ e, (a e)^2 := by
  have he (e : SpatialVertex n × Fin 3) :
      (displacement n (direction n t a axis) e)^2 ≤ 4*t^2*(a e)^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (QuaternionRotationFrame.distance_le (t*a e) (axis e))
    simp only [mul_pow, sq_abs] at h
    dsimp only [displacement, direction]
    nlinarith
  have h := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => he e)
  simpa only [cost, ← Finset.mul_sum] using h

/-- Arbitrary fixed coefficient directions, with no channel-count factor. -/
theorem directional_response_bound (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (a : (SpatialVertex n × Fin 3) → ℝ) (axis : (SpatialVertex n × Fin 3) → Fin 3)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, (rowMean n β hβ f u-rowMean n β hβ f (direction n t a axis*u))^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤
      72*β*(hi-lo)^2*t^2*∑ e, (a e)^2 := by
  have h := (mean_response_sq_bound n β hβ (direction n t a axis) f lo hi hf).trans
    (mul_le_mul_of_nonneg_left (direction_cost n t a axis)
      (show 0 ≤ 18*β*(hi-lo)^2 by positivity))
  nlinarith

/-- A uniform finite-difference quotient estimate; no derivative limit is assumed. -/
theorem directional_quotient_bound (β : ℝ) (hβ : 0 ≤ β) (t : ℝ) (ht : t ≠ 0)
    (a : (SpatialVertex n × Fin 3) → ℝ) (axis : (SpatialVertex n × Fin 3) → Fin 3)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ u, ((rowMean n β hβ f u-rowMean n β hβ f (direction n t a axis*u))/t)^2
      ∂WilsonGroundHeatBath.groundLaw n β hβ) ≤
      72*β*(hi-lo)^2*∑ e, (a e)^2 := by
  simp only [div_pow, integral_div]
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).mpr
  have h := directional_response_bound n β hβ t a axis f lo hi hf
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonJointResponse
