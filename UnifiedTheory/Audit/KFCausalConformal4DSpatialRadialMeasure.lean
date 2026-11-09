/- Exact three-dimensional radial measure and L1 transfer, including sharp
ball indicators. The factor4pi is derived from Euclidean ball volume. -/
import UnifiedTheory.Audit.KFCausalConformal4DCoordinateVolume
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasure
noncomputable section
open MeasureTheory Set Real WithLp

abbrev Space := Fin 3 → ℝ
abbrev Euclidean := EuclideanSpace ℝ (Fin 3)
def radius (v : Space) : ℝ := ‖(toLp 2 v : Euclidean)‖
def radiusBall (R : ℝ) : Set Space := {v | radius v<R}

theorem radius_nonnegative (v : Space) : 0≤radius v := norm_nonneg _

theorem radius_eq (v : Space) : radius v=sqrt (v 0^2+v 1^2+v 2^2) := by
  have hn : radius v^2=v 0^2+v 1^2+v 2^2 := by
    simp [radius,EuclideanSpace.norm_sq_eq,Fin.sum_univ_three,Real.norm_eq_abs]
  rw [← hn,sqrt_sq (radius_nonnegative v)]

theorem radius_continuous : Continuous radius := by unfold radius; fun_prop

theorem radius_ball_measurable (R : ℝ) : MeasurableSet (radiusBall R) :=
  (isOpen_lt radius_continuous continuous_const).measurableSet

private theorem euclidean_unit_volume :
    (volume : Measure Euclidean).real (Metric.ball 0 1)=π*4/3 := by
  rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
  norm_num only [ENNReal.ofReal_one,one_pow,one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

theorem radial_integrable_iff (f : ℝ → ℝ) :
    Integrable (fun v : Space => f (radius v)) ↔
      IntegrableOn (fun r : ℝ => r^2*f r) (Ioi 0) := by
  have mp := PiLp.volume_preserving_toLp (Fin 3)
  have he := mp.integrable_comp_emb (g := fun x : Euclidean => f ‖x‖)
    (MeasurableEquiv.toLp 2 Space).measurableEmbedding
  change Integrable ((fun x : Euclidean => f ‖x‖) ∘ toLp 2) volume ↔ _
  rw [he]
  simpa only [finrank_euclideanSpace_fin,show 3-1=2 by omega,smul_eq_mul] using
    (integrable_fun_norm_addHaar (volume : Measure Euclidean) (f := f))

theorem radial_integral (f : ℝ → ℝ) :
    (∫ v : Space, f (radius v)) = 4*π*(∫ r in Ioi (0:ℝ), r^2*f r) := by
  have mp := PiLp.volume_preserving_toLp (Fin 3)
  have he := mp.integral_comp (MeasurableEquiv.toLp 2 Space).measurableEmbedding
    (fun x : Euclidean => f ‖x‖)
  change (∫ v : Space, f ‖(toLp 2 v : Euclidean)‖)=_
  rw [he,integral_fun_norm_addHaar (volume : Measure Euclidean) f]
  simp only [finrank_euclideanSpace_fin,show 3-1=2 by omega,euclidean_unit_volume,
    smul_eq_mul,nsmul_eq_mul]
  ring

private theorem radial_indicator (f : ℝ → ℝ) (R : ℝ) :
    (radiusBall R).indicator (fun v : Space => f (radius v)) =
      fun v : Space => (Iio R).indicator f (radius v) := by
  funext v
  by_cases h : radius v<R
  · rw [indicator_of_mem (show v∈radiusBall R from h),
      indicator_of_mem (show radius v∈Iio R from h)]
  · rw [indicator_of_notMem (show v∉radiusBall R from h),
      indicator_of_notMem (show radius v∉Iio R from h)]

private theorem weighted_indicator (f : ℝ → ℝ) (R : ℝ) :
    (fun r : ℝ => r^2*(Iio R).indicator f r) = (Iio R).indicator (fun r : ℝ => r^2*f r) := by
  funext r
  by_cases h : r<R
  · simp only [indicator_of_mem (show r∈Iio R from h)]
  · simp only [indicator_of_notMem (show r∉Iio R from h),mul_zero]

private theorem positive_inter_below (R : ℝ) : Ioi (0:ℝ)∩Iio R=Ioo 0 R := by
  ext r
  rfl

theorem ball_integrable_iff (f : ℝ → ℝ) (R : ℝ) :
    IntegrableOn (fun v : Space => f (radius v)) (radiusBall R) ↔
      IntegrableOn (fun r : ℝ => r^2*f r) (Ioo 0 R) := by
  rw [← integrable_indicator_iff (radius_ball_measurable R),radial_indicator,radial_integrable_iff,
    weighted_indicator]
  change Integrable ((Iio R).indicator (fun r : ℝ => r^2*f r)) (volume.restrict (Ioi 0)) ↔ _
  rw [integrable_indicator_iff measurableSet_Iio]
  simp only [IntegrableOn,Measure.restrict_restrict measurableSet_Iio,
    inter_comm (Iio R),positive_inter_below]

theorem ball_integral (f : ℝ → ℝ) (R : ℝ) :
    (∫ v in radiusBall R, f (radius v)) = 4*π*(∫ r in Ioo (0:ℝ) R, r^2*f r) := by
  rw [← integral_indicator (radius_ball_measurable R),radial_indicator,radial_integral,
    weighted_indicator,setIntegral_indicator measurableSet_Iio,positive_inter_below]

theorem ball_integrable_of_continuous (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ) :
    IntegrableOn (fun v : Space => f (radius v)) (radiusBall R) := by
  apply (ball_integrable_iff f R).mpr
  have hc : Continuous (fun r : ℝ => r^2*f r) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc : IsCompact (Icc (0:ℝ) R))).mono_set
    Ioo_subset_Icc_self

theorem radial_integrable_of_compact (f : ℝ → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun v : Space => f (radius v)) := by
  apply (radial_integrable_iff f).mpr
  have hc : Continuous (fun r : ℝ => r^2*f r) := by fun_prop
  have hk : HasCompactSupport (fun r : ℝ => r^2*f r) := hs.mul_left
  exact (hc.integrable_of_hasCompactSupport hk).integrableOn

theorem point_radius (p : KFCausalConformal4DDiamondBenchmark.Point) :
    KFCausalConformal4DDiamondMeasure.spatialRadius p = radius (fun i : Fin 3 => p i.succ) := by
  rw [radius_eq]
  rfl

#print axioms radius_nonnegative
#print axioms radius_eq
#print axioms radius_continuous
#print axioms radius_ball_measurable
#print axioms radial_integrable_iff
#print axioms radial_integral
#print axioms ball_integrable_iff
#print axioms ball_integral
#print axioms ball_integrable_of_continuous
#print axioms radial_integrable_of_compact
#print axioms point_radius
end
end UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasure
