/- A clock moment of each actual shifted Gaussian is in L2. Splitting
the clock Gaussian in half absorbs the moment without narrowing the
closed admissible imaginary strip. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianClockMoment
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument argument_smooth scale)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude profile_memLp)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (clockFunction_factor)

def bound (a y : ℝ) : ℝ := (1+1/(a/2)+|y|)*Real.exp ((a/2)*y^2)

theorem bound_positive (a y : ℝ) (ha : 0 < a) : 0 < bound a y := by
  unfold bound
  positivity

theorem linear_gaussian_bound (b r : ℝ) (hb : 0 < b) :
    |r| *Real.exp (-b*r^2) ≤ 1+1/b := by
  have he : Real.exp (-b*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  have hx : (b*r^2)*Real.exp (-(b*r^2)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (b*r^2)).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hsq : r^2*Real.exp (-b*r^2) ≤ 1/b := by
    apply (le_div_iff₀ hb).mpr
    rw [← neg_mul] at hx
    nlinarith only [hx]
  have hr : |r| ≤ 1+r^2 := by nlinarith [sq_nonneg (|r|-1),sq_abs r]
  have hm := mul_le_mul_of_nonneg_right hr (Real.exp_pos (-b*r^2)).le
  nlinarith

theorem moment_bound (a r y : ℝ) (ha : 0 < a) :
    ‖((r:ℂ)+(y:ℂ)*Complex.I)*clockFactor (a/2) ((r:ℂ)+(y:ℂ)*Complex.I)‖ ≤ bound a y := by
  have hq : ‖(r:ℂ)+(y:ℂ)*Complex.I‖ ≤ |r|+|y| := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] using
      norm_add_le (r:ℂ) ((y:ℂ)*Complex.I)
  have he : Real.exp (-(a/2)*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  have hr := linear_gaussian_bound (a/2) r (by positivity)
  have hy := mul_le_mul_of_nonneg_left he (abs_nonneg y)
  have hsum : (|r|+|y|)*Real.exp (-(a/2)*r^2) ≤ 1+1/(a/2)+|y| := by nlinarith
  rw [norm_mul,clockFactor_norm]
  have hexp : Real.exp (-(a/2)*(r^2-y^2)) = Real.exp (-(a/2)*r^2)*Real.exp ((a/2)*y^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ (|r|+|y|)*(Real.exp (-(a/2)*r^2)*Real.exp ((a/2)*y^2)) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ bound a y := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le

theorem factor_split (a : ℝ) (q : ℂ) :
    clockFactor a q = clockFactor (a/2) q*clockFactor (a/2) q := by
  unfold clockFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem profile_factor (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    profile (clockAmplitude ε a p y) (scale ε y) α β b x =
      clockFactor (a/2) (argument ε y x.1)*
        profile (clockAmplitude ε (a/2) p y) (scale ε y) α β b x := by
  unfold profile clockAmplitude
  rw [factor_split a]
  ring

theorem profile_moment_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fun x => argument ε y x.1*profile (clockAmplitude ε a p y) (scale ε y) α β b x) 2 volume := by
  have hc : Continuous (fun s => argument ε y s*clockFactor (a/2) (argument ε y s)) := by
    unfold clockFactor
    exact (argument_smooth ε y).continuous.mul
      ((continuous_const.mul ((argument_smooth ε y).continuous.pow 2)).cexp)
  have hm := KFCausalShearPolynomialMoments.clock_mul_memLp _ hc (bound a y)
    (bound_positive a y ha).le (fun s => moment_bound a (chart ε s) y ha) _
    (profile_memLp ε (a/2) α β p y b hε (by positivity) hα hβ hw hy)
  convert hm using 1
  funext x
  rw [profile_factor]
  ring

theorem clockFunction_half (ε a s : ℝ) (hε : 0 < ε) :
    clockFunction ε a s = clockFactor (a/2) (chart ε s:ℂ)*clockFunction ε (a/2) s := by
  rw [clockFunction_factor ε a s hε,clockFunction_factor ε (a/2) s hε,factor_split a]
  ring

theorem clockFunction_moment_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (fun s => (chart ε s:ℂ)*clockFunction ε a s) 2 volume := by
  have hc : Continuous (fun s => (chart ε s:ℂ)*clockFunction ε a s) := by
    unfold clockFunction KFCausalClockFloorInvariantTrial.realClock chart
    fun_prop
  apply ((clockFunction_memLp ε (a/2) hε (by positivity)).const_mul (bound a 0:ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with s
  rw [clockFunction_half ε a s hε,← mul_assoc]
  have hm := mul_le_mul_of_nonneg_right (moment_bound a (chart ε s) 0 ha)
    (norm_nonneg (clockFunction ε (a/2) s))
  simpa only [Complex.ofReal_zero,zero_mul,add_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (bound_positive a 0 ha)] using hm

#print axioms bound_positive
#print axioms linear_gaussian_bound
#print axioms moment_bound
#print axioms factor_split
#print axioms profile_factor
#print axioms profile_moment_memLp
#print axioms clockFunction_half
#print axioms clockFunction_moment_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianClockMoment
