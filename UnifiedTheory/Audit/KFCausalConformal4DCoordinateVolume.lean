/- Actual coordinate integration on the oriented Minkowski diamond agrees with
the compact parameter-volume definition. No causal/manifold identification is
assumed; the domain is the explicit two chronological cone inequalities. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialAxialIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalConformal4DCoordinateVolume
noncomputable section
open MeasureTheory Real Set
open KFCausalConformal4DDiamondBenchmark (Point metric)
open KFCausalConformal4DDiamondAffine KFCausalConformal4DDiamondMeasure
open KFCausalConformal4DBallAxialIntegral (Space spatialBall)
open KFCausalConformal4DRadialAxialIntegral
open KFCausalConformal4DBoostedMoments KFCausalConformal4DTemporalVariation

def timeSplit : Point ≃ᵐ ℝ × Space :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0

def slice (T m A B : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  (T-|s|)^3 * ∫ v in (0:ℝ)..1, v^2 * ∫ mu in (-1:ℝ)..1,
    f (m+A*s+B*(T-|s|)*v*mu)

private theorem timeSplit_symm (s : ℝ) (v : Space) :
    timeSplit.symm (s,v)=![s,v 0,v 1,v 2] := by
  ext i
  fin_cases i <;> rfl

private theorem rest_measurable (T : ℝ) : MeasurableSet (restDiamond T) := by
  have he : restDiamond T={v : Point | |v 0|+spatialRadius v<T} := by
    ext v
    exact rest_diamond_iff T v
  rw [he]
  apply measurableSet_lt _ measurable_const
  unfold spatialRadius
  fun_prop

private theorem slice_continuous (T m A B : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (slice T m A B f) := by
  have hinner : Continuous (fun p : ℝ × ℝ => ∫ mu in (-1:ℝ)..1,
      f (m+A*p.1+B*(T-|p.1|)*p.2*mu)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hmid : Continuous (fun s : ℝ => ∫ v in (0:ℝ)..1,
      v^2 * ∫ mu in (-1:ℝ)..1, f (m+A*s+B*(T-|s|)*v*mu)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_snd.pow 2).mul hinner
  exact ((continuous_const.sub continuous_abs).pow 3).mul hmid

theorem radial_scaling (R : ℝ) (f : ℝ → ℝ) :
    (∫ b in (0:ℝ)..R, b^2 * ∫ mu in (-1:ℝ)..1, f (b*mu)) =
      R^3 * ∫ v in (0:ℝ)..1, v^2 * ∫ mu in (-1:ℝ)..1, f (R*v*mu) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun b => b^2 * ∫ mu in (-1:ℝ)..1, f (b*mu)) R
  simp only [smul_eq_mul,mul_zero,mul_one] at h
  rw [← h,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  ring

theorem rest_slice_integral (T m A B : ℝ) (hT : 0<T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in restDiamond T, f (m+A*z 0+B*z 1)) =
      2*π * ∫ s in (-T)..T, slice T m A B f s := by
  let F : Point → ℝ := (restDiamond T).indicator (fun z => f (m+A*z 0+B*z 1))
  have hi : Integrable F := (rest_integrable T hT.le _ (by fun_prop)).integrable_indicator
    (rest_measurable T)
  have mp : MeasurePreserving timeSplit := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hic : Integrable (fun p : ℝ × Space => F (timeSplit.symm p)) :=
    (mp.symm.integrable_comp_emb timeSplit.symm.measurableEmbedding).2 hi
  have hs (s : ℝ) : (∫ v : Space, F (timeSplit.symm (s,v))) =
      (Ioo (-T) T).indicator (fun s => 2*π*slice T m A B f s) s := by
    by_cases hsin : s∈Ioo (-T) T
    · have habs : |s|<T := abs_lt.mpr hsin
      have hR : 0<T-|s| := by linarith
      have he : (fun v : Space => F (timeSplit.symm (s,v))) =
          (spatialBall (T-|s|)).indicator (fun v => f (m+A*s+B*v 0)) := by
        funext v
        rw [timeSplit_symm]
        have hmem : ![s,v 0,v 1,v 2]∈restDiamond T ↔ v∈spatialBall (T-|s|) := by
          rw [rest_diamond_iff]
          change |s|+sqrt (v 0^2+v 1^2+v 2^2)<T ↔ v 0^2+v 1^2+v 2^2<(T-|s|)^2
          rw [← sqrt_lt (by positivity) hR.le]
          constructor <;> intro h <;> linarith
        dsimp only [F]
        by_cases hv : v∈spatialBall (T-|s|)
        · rw [indicator_of_mem (hmem.2 hv),indicator_of_mem hv]
          rfl
        · rw [indicator_of_notMem (fun hh => hv (hmem.1 hh)),indicator_of_notMem hv]
      rw [he,integral_indicator (by exact measurableSet_lt (by fun_prop) measurable_const),
        ball_radial_integral _ hR (fun z : ℝ => f (m+A*s+B*z)) (by fun_prop),
        radial_scaling _ (fun z : ℝ => f (m+A*s+B*z)),
        indicator_of_mem hsin]
      unfold slice
      simp only [mul_assoc]
    · have habs : T≤|s| := le_of_not_gt (fun h => hsin (abs_lt.mp h))
      rw [indicator_of_notMem hsin]
      apply integral_eq_zero_of_ae
      filter_upwards [] with v
      rw [timeSplit_symm]
      dsimp only [F]
      apply indicator_of_notMem
      intro hv
      have hh := (rest_diamond_iff T _).1 hv
      change |s|+sqrt (v 0^2+v 1^2+v 2^2)<T at hh
      linarith [sqrt_nonneg (v 0^2+v 1^2+v 2^2)]
  rw [← integral_indicator (rest_measurable T)]
  change (∫ z, F z)=_
  rw [← mp.symm.integral_comp' F]
  change (∫ p : ℝ × Space, F (timeSplit.symm p) ∂volume.prod volume)=_
  rw [integral_prod _ hic]
  simp_rw [hs]
  rw [integral_indicator measurableSet_Ioo,integral_const_mul,
    intervalIntegral.integral_of_le (by linarith : -T≤T),integral_Ioc_eq_integral_Ioo]

theorem rest_coordinate_integral (T m A B : ℝ) (hT : 0<T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in restDiamond T, f (m+A*z 0+B*z 1))=coordinateIntegral T m A B f := by
  rw [rest_slice_integral T m A B hT f hf,
    symmetric_interval T _ (slice_continuous T m A B f hf)]
  have hscale := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun s => slice T m A B f s+slice T m A B f (-s)) T
  simp only [smul_eq_mul,mul_zero,mul_one] at hscale
  rw [← hscale]
  have hpoint (u : ℝ) (hu : u∈uIcc (0:ℝ) 1) :
      slice T m A B f (T*u)+slice T m A B f (-(T*u)) =
        T^3 * ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1, pair T m A B f u v mu := by
    have hu0 : 0≤u := by
      rw [uIcc_of_le (zero_le_one : (0:ℝ)≤1)] at hu
      exact hu.1
    have hTu : 0≤T*u := mul_nonneg hT.le hu0
    unfold slice
    simp only [abs_neg,abs_of_nonneg hTu]
    have hin (A : ℝ) : Continuous (fun v : ℝ => v^2 * ∫ mu in (-1:ℝ)..1,
        f (m+A*(T*u)+B*(T-T*u)*v*mu)) := by
      apply Continuous.mul (by fun_prop)
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      fun_prop
    have hneg : ∀ v mu : ℝ, m+A*(-(T*u))+B*(T-T*u)*v*mu=
        m+(-A)*(T*u)+B*(T-T*u)*v*mu := by intros; ring
    simp_rw [hneg]
    rw [← mul_add,← intervalIntegral.integral_add ((hin A).intervalIntegrable _ _)
      ((hin (-A)).intervalIntegrable _ _),← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [← mul_add,← intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun mu : ℝ => f (m+A*(T*u)+B*(T-T*u)*v*mu))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun mu : ℝ => f (m+(-A)*(T*u)+B*(T-T*u)*v*mu))).intervalIntegrable _ _)]
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro mu _
    dsimp only
    unfold pair time
    have hp : m+A*(T*u)+B*(T-T*u)*v*mu=m+A*T*u+B*T*(1-u)*v*mu := by ring
    have hm : m+(-A)*(T*u)+B*(T-T*u)*v*mu=m+(-A)*T*u+B*T*(1-u)*v*mu := by ring
    rw [hp,hm]
    ring
  rw [intervalIntegral.integral_congr hpoint,intervalIntegral.integral_const_mul]
  unfold coordinateIntegral
  ring

theorem timelike_volume_eq_coordinate_integral (c t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2) :
    timelikeVolume c t r =
      ∫ x in diamond (endpoint t r) 0, sqrt |Matrix.det (metric (2*c) 0 x)| := by
  have hc : Continuous (density c) := by
    change Continuous (fun x => density c x)
    simp_rw [density_polynomial]
    fun_prop
  rw [density_integral_transport c t r ht hq,
    rest_coordinate_integral _ _ _ _ (by positivity) (density c) hc]
  rfl

#print axioms radial_scaling
#print axioms rest_slice_integral
#print axioms rest_coordinate_integral
#print axioms timelike_volume_eq_coordinate_integral
end
end UnifiedTheory.Audit.KFCausalConformal4DCoordinateVolume
