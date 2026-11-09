/- Clock moments of the actual invariant trial. All real exponential
clock moments are integrable; the shifted clock-half therefore acts on
the trial on its natural maximal domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
import UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests (quadratic_exp_integrable)

theorem clock_exponential_moment (ε a κ : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s : ℝ => Real.exp (κ*s)*(realClock ε a s)^2) := by
  have h0 := quadratic_exp_integrable (a*ε^2) κ 0 (by positivity)
  have h1 := quadratic_exp_integrable (a*ε^2) (κ-2) 0 (by positivity)
  have hi := (h0.add (h1.const_mul (ε^2))).const_mul (2*Real.exp (2*a))
  have hc : Continuous (fun s : ℝ => Real.exp (κ*s)*(realClock ε a s)^2) := by
    unfold realClock KFCausalRegularizedLongitudinalChart.chart
    fun_prop
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (realClock_square_bound ε a hε ha.le s)
    (Real.exp_pos (κ*s)).le
  have he0 : Real.exp (-(a*ε^2)*s^2+κ*s+0) =
      Real.exp (κ*s)*Real.exp (-(a*ε^2)*s^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he1 : Real.exp (-(a*ε^2)*s^2+(κ-2)*s+0) =
      Real.exp (κ*s)*Real.exp (-(a*ε^2)*s^2-2*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert h using 1
  simp only [Pi.add_apply]
  rw [he0,he1]
  ring

def halfClockFunction (ε a : ℝ) (s : ℝ) : ℂ :=
  (Real.sqrt (Real.exp s+ε):ℂ)*clockFunction ε a s

theorem halfClockFunction_continuous (ε a : ℝ) : Continuous (halfClockFunction ε a) := by
  unfold halfClockFunction
  exact (by fun_prop : Continuous (fun s : ℝ => (Real.sqrt (Real.exp s+ε):ℂ))).mul
    (clockFunction_continuous ε a)

theorem halfClockFunction_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (halfClockFunction ε a) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (halfClockFunction_continuous ε a).aestronglyMeasurable).mpr
  have hi := (clock_exponential_moment ε a 1 hε ha).add
    ((clock_exponential_moment ε a 0 hε ha).const_mul ε)
  apply hi.congr
  filter_upwards [] with s
  simp only [Pi.add_apply,one_mul,zero_mul,Real.exp_zero,one_mul,
    halfClockFunction,clockFunction,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem clockHalf_domain (ε : ℝ) (f : Hilbert) :
    f ∈ (clockHalf ε).domain ↔ MemLp (fun x => (halfWeight ε x:ℂ)*f x) 2 volume :=
  KFCausalUnitaryPositiveMultiplier.pullback_domain_iff _ _ _ _ f

theorem trialState_clockHalf_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    trialState ε a hbar hε ha hh ∈ (clockHalf ε).domain := by
  apply (clockHalf_domain ε _).mpr
  have hm := configurationProfile_memLp (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
    (halfClockFunction ε a) (halfClockFunction_continuous ε a) (halfClockFunction_memLp ε a hε ha)
  apply hm.ae_eq
  filter_upwards [trialState_coe ε a hbar hε ha hh] with x hx
  rw [hx]
  simp only [configurationProfile,halfClockFunction,halfWeight,mul_assoc]

def dampedClockFunction (ε a : ℝ) (s : ℝ) : ℂ :=
  (Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s

theorem dampedClockFunction_continuous (ε a : ℝ) (hε : 0 < ε) :
    Continuous (dampedClockFunction ε a) := by
  have hn (s : ℝ) : (Real.sqrt (Real.exp s+ε):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  exact ((by fun_prop : Continuous (fun s : ℝ => (Real.sqrt (Real.exp s+ε):ℂ))).inv₀ hn).mul
    (clockFunction_continuous ε a)

theorem dampedClockFunction_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (dampedClockFunction ε a) 2 volume := by
  apply ((clockFunction_memLp ε a hε ha).const_mul (((Real.sqrt ε)⁻¹:ℝ):ℂ)).of_le
    (dampedClockFunction_continuous ε a hε).aestronglyMeasurable
  filter_upwards [] with s
  simp only [dampedClockFunction,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (inverseWeight_bound ε hε (s,0)) (norm_nonneg _)

#print axioms clock_exponential_moment
#print axioms halfClockFunction_continuous
#print axioms halfClockFunction_memLp
#print axioms clockHalf_domain
#print axioms trialState_clockHalf_domain
#print axioms dampedClockFunction_continuous
#print axioms dampedClockFunction_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
