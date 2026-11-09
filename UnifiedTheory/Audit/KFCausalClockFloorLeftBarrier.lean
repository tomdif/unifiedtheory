/- Bounded barriers for the negative log-clock tail. These are resolvents
of I-D^2, where D is the actual clock-defect multiplier. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectForm
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
import UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization (lowProjection lowProjection_coe)

variable (ε : ℝ) (hε : 0 < ε)
local notation "D" => defectOperator ε hε

include hε in
theorem gap_positive (s : ℝ) : 0 < 1-(defect ε s)^2 := by
  have hd := defect_positive ε s hε
  have hr := (response_bounds ε s hε).1
  have he := response_add_defect ε s hε.le
  nlinarith

def weight (b : ℝ) (x : Configuration) : ℝ := b/(1-(defect ε x.1)^2+b)

include hε in
theorem weight_bounds (b : ℝ) (hb : 0 < b) (x : Configuration) :
    0 < weight ε b x ∧ weight ε b x ≤ 1 := by
  have hg := gap_positive ε hε x.1
  exact ⟨div_pos hb (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩

theorem weight_measurable (b : ℝ) : Measurable (fun x => (weight ε b x:ℂ)) := by
  unfold weight defect KFCausalClockFloorFlow.clock
  fun_prop

include hε in
theorem weight_norm_le (b : ℝ) (hb : 0 < b) (x : Configuration) : ‖(weight ε b x:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_bounds ε hε b hb x).1]
  exact (weight_bounds ε hε b hb x).2

def barrier (b : ℝ) (hb : 0 < b) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x => (weight ε b x:ℂ)) (weight_measurable ε b) (weight_norm_le ε hε b hb)

theorem barrier_coe (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    barrier ε hε b hb f =ᵐ[volume] fun x => (weight ε b x:ℂ)*f x :=
  multiplyL_coe _ _ _ f

def shifted (b : ℝ) : Hilbert →L[ℂ] Hilbert :=
  ((1+b:ℝ):ℂ) • ContinuousLinearMap.id ℂ Hilbert-(D).comp D

theorem shifted_symmetric (b : ℝ) (f g : Hilbert) :
    inner ℂ (shifted ε hε b f) g = inner ℂ f (shifted ε hε b g) := by
  simp only [shifted,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,inner_sub_left,
    inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal,defect_inner]

theorem shifted_quadratic (b : ℝ) (f : Hilbert) :
    (inner ℂ f (shifted ε hε b f)).re = (1+b)*‖f‖^2-‖D f‖^2 := by
  change (inner ℂ f (((1+b:ℝ):ℂ) • f-D (D f))).re = _
  rw [inner_sub_right,inner_smul_right,← defect_inner,inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  change (((1+b:ℝ):ℂ)*(‖f‖:ℂ)^2-(‖D f‖:ℂ)^2).re = _
  simp only [← Complex.ofReal_pow,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]

theorem shifted_nonnegative (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    0 ≤ (inner ℂ f (shifted ε hε b f)).re := by
  rw [shifted_quadratic]
  have hd := pow_le_pow_left₀ (norm_nonneg _) (defectOperator_norm_le ε hε f) 2
  nlinarith [sq_nonneg ‖f‖]

theorem shifted_barrier (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    shifted ε hε b (barrier ε hε b hb f) = (b:ℂ) • f := by
  let y := barrier ε hε b hb f
  change ((1+b:ℝ):ℂ) • y-D (D y) = (b:ℂ) • f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (((1+b:ℝ):ℂ) • y) (D (D y)),
    Lp.coeFn_smul ((1+b:ℝ):ℂ) y,Lp.coeFn_smul (b:ℂ) f,
    defectOperator_coe ε hε (D y),defectOperator_coe ε hε y,barrier_coe ε hε b hb f]
    with x hsub hsm hbf hdd hd hy
  change y x = (weight ε b x:ℂ)*f x at hy
  simp only [hsub,Pi.sub_apply,hsm,hbf,Pi.smul_apply,smul_eq_mul,hdd,hd,hy]
  have hg := gap_positive ε hε x.1
  have he : (1+b-(defect ε x.1)^2)*weight ε b x = b := by
    unfold weight
    field_simp [show 1-(defect ε x.1)^2+b ≠ 0 by linarith]
    ring
  have he' : (1+(b:ℂ)-(defect ε x.1:ℂ)^2)*(weight ε b x:ℂ) = (b:ℂ) := by exact_mod_cast he
  push_cast
  linear_combination (f x)*he'

theorem inverse_equation (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    shifted ε hε b (((b:ℂ)⁻¹ • barrier ε hε b hb) f) = f := by
  rw [ContinuousLinearMap.smul_apply,map_smul,shifted_barrier,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'),one_smul]

theorem expectation_integral (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    (inner ℂ f (barrier ε hε b hb f)).re = ∫ x, weight ε b x*‖f x‖^2 :=
  KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _ (barrier_coe ε hε b hb f)

include hε in
theorem gap_upper (s : ℝ) : 1-(defect ε s)^2 ≤ 2*Real.exp s/ε := by
  have hd := defect_positive ε s hε
  have hr := (response_bounds ε s hε).1
  have he := response_add_defect ε s hε.le
  have hu : response ε s ≤ Real.exp s/ε := by
    unfold response KFCausalClockFloorFlow.clock
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hε (by linarith [Real.exp_pos s])
  rw [mul_div_assoc]
  nlinarith [sq_nonneg (defect ε s-1)]

theorem low_probability_bound (b : ℝ) (hb : 0 < b) (S : ℝ)
    (hS : 2*Real.exp S ≤ b*ε) (f : Hilbert) :
    ‖lowProjection S f‖^2 ≤ 2*(inner ℂ f (barrier ε hε b hb f)).re := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (barrier ε hε b hb f)).re
  have he : (fun x => (inner ℂ (f x) (barrier ε hε b hb f x)).re) =ᵐ[volume]
      fun x => weight ε b x*‖f x‖^2 := by
    filter_upwards [barrier_coe ε hε b hb f] with x hx
    rw [hx]
    change (inner ℂ (f x) ((weight ε b x:ℂ) • f x)).re = _
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change ((weight ε b x:ℂ)*(‖f x‖:ℂ)^2).re = _
    rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  have hw := hi.congr he
  rw [KFCausalAveragedEnergyGraph.l2_norm_square,expectation_integral,← integral_const_mul]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (lowProjection S f))).mp
      (Lp.memLp (lowProjection S f))) (hw.const_mul 2)
  filter_upwards [lowProjection_coe S f] with x hx
  rw [hx]
  by_cases hs : x.1 ≤ S
  · rw [if_pos hs]
    have hg : 1-(defect ε x.1)^2 ≤ b := by
      apply (gap_upper ε hε x.1).trans
      apply (div_le_iff₀ hε).mpr
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by norm_num)).trans hS
    have hp := gap_positive ε hε x.1
    have hb' : 1 ≤ 2*weight ε b x := by
      unfold weight
      have hd := (le_div_iff₀ (by linarith : 0 < 1-(defect ε x.1)^2+b)).mpr
        (show 1*(1-(defect ε x.1)^2+b) ≤ 2*b by linarith)
      simpa only [mul_div_assoc] using hd
    nlinarith [mul_le_mul_of_nonneg_right hb' (sq_nonneg ‖f x‖)]
  · rw [if_neg hs,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (mul_nonneg (weight_bounds ε hε b hb x).1.le (sq_nonneg _))

#print axioms gap_positive
#print axioms weight_bounds
#print axioms weight_measurable
#print axioms weight_norm_le
#print axioms barrier_coe
#print axioms shifted_symmetric
#print axioms shifted_quadratic
#print axioms shifted_nonnegative
#print axioms shifted_barrier
#print axioms inverse_equation
#print axioms expectation_integral
#print axioms gap_upper
#print axioms low_probability_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
