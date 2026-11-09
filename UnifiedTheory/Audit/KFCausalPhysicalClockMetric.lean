/- The original complex clock inverse supplies the small-shift metric
bound. All clock denominators and the actual bilinear shear are retained. -/
import UnifiedTheory.Audit.KFCausalPhysicalComplexShearMetric
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseLines

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalClockMetric
noncomputable section
open KFCausalComplexShearPerturbation (Space)
open KFCausalPhysicalComplexShearMetric (gram normalizedMetric normalized_difference)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)

def baseClock (ε s : ℝ) : ℝ := Real.exp s+ε
def shiftedClock (ε s : ℝ) (δ : ℂ) : ℂ := Complex.exp ((s:ℂ)+δ)+(ε:ℂ)
def ratio (ε s : ℝ) (δ : ℂ) : ℂ := (baseClock ε s:ℂ)/shiftedClock ε s δ
def metric (ε s : ℝ) (δ : ℂ) (x : Space) : Space :=
  (shiftedClock ε s δ)⁻¹ • gram δ x

private theorem exp_small (δ : ℂ) (hδ : ‖δ‖≤1/20) : ‖Complex.exp δ-1‖≤1/19 := by
  have ht := Complex.norm_exp_sub_one_sub_id_le (show ‖δ‖≤1 by linarith)
  have he := norm_add_le (Complex.exp δ-1-δ) δ
  rw [sub_add_cancel] at he
  have hp := mul_nonneg (norm_nonneg δ) (sub_nonneg.mpr hδ)
  nlinarith [norm_nonneg δ]

private theorem inverse_small (u : ℂ) (hu : ‖u‖≤1/19) :
    1+u≠0 ∧ ‖(1+u)⁻¹-1‖≤1/18 := by
  have hl : 18/19≤‖1+u‖ := by
    have hh := norm_sub_le (1+u) u
    rw [add_sub_cancel_right,norm_one] at hh
    linarith
  have hn : 1+u≠0 := by
    intro hz
    rw [hz,norm_zero] at hl
    norm_num at hl
  refine ⟨hn,?_⟩
  have he : (1+u)⁻¹-1=(-u)/(1+u) := by field_simp; ring
  rw [he,norm_div,norm_neg]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  linarith

theorem ratio_bound (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20) :
    shiftedClock ε s δ≠0 ∧ ‖ratio ε s δ-1‖≤1/18 := by
  have hC : 0<baseClock ε s := add_pos (Real.exp_pos _) hε
  let a : ℝ := Real.exp s/baseClock ε s
  have ha : 0≤a := div_nonneg (Real.exp_pos _).le hC.le
  have ha1 : a≤1 := (div_le_one hC).mpr (by dsimp [baseClock]; linarith)
  have hu : ‖(a:ℂ)*(Complex.exp δ-1)‖≤1/19 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
    have he := exp_small δ hδ
    nlinarith [mul_le_mul_of_nonneg_right ha1 (norm_nonneg (Complex.exp δ-1))]
  have haC : (baseClock ε s:ℂ)*(a:ℂ)=(Real.exp s:ℂ) := by
    have he : baseClock ε s*a=Real.exp s := by dsimp [a]; field_simp
    exact_mod_cast he
  have hf : shiftedClock ε s δ=(baseClock ε s:ℂ)*(1+(a:ℂ)*(Complex.exp δ-1)) := by
    unfold shiftedClock
    rw [Complex.exp_add,←Complex.ofReal_exp,mul_add,mul_one,←mul_assoc,haC]
    dsimp [baseClock]
    push_cast
    ring
  obtain ⟨hn,hb⟩ := inverse_small ((a:ℂ)*(Complex.exp δ-1)) hu
  have hCn : (baseClock ε s:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC.ne'
  refine ⟨by rw [hf]; exact mul_ne_zero hCn hn,?_⟩
  have he : ratio ε s δ=(1+(a:ℂ)*(Complex.exp δ-1))⁻¹ := by
    unfold ratio
    rw [hf]
    field_simp
  rw [he]
  exact hb

theorem normalized_identity (ε s : ℝ) (δ : ℂ) (x : Space) :
    normalizedMetric δ (ratio ε s δ) x=(baseClock ε s:ℂ) • metric ε s δ x := by
  simp only [normalizedMetric,ratio,metric,div_eq_mul_inv,mul_smul]

theorem normalized_bound (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20) (x : Space) :
    ‖(baseClock ε s:ℂ) • metric ε s δ x-x‖≤(1/3:ℝ)*‖x‖ := by
  rw [←normalized_identity]
  exact (normalized_difference δ (ratio ε s δ) hδ (ratio_bound ε s hε δ hδ).2 x).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (7753/27378:ℝ)≤1/3) (norm_nonneg x))

theorem metric_coercive (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20) (x : Space) :
    (2/(3*baseClock ε s))*‖x‖^2≤(inner ℂ x (metric ε s δ x)).re ∧
      (inner ℂ x (metric ε s δ x)).re≤(4/(3*baseClock ε s))*‖x‖^2 := by
  have hC : 0<baseClock ε s := add_pos (Real.exp_pos _) hε
  have hd := normalized_bound ε s hε δ hδ x
  have hn := norm_inner_le_norm (𝕜 := ℂ) x ((baseClock ε s:ℂ) • metric ε s δ x-x)
  have hr := Complex.abs_re_le_norm (inner ℂ x ((baseClock ε s:ℂ) • metric ε s δ x-x))
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg x)
  have he : (inner ℂ x ((baseClock ε s:ℂ) • metric ε s δ x-x)).re=
      baseClock ε s*(inner ℂ x (metric ε s δ x)).re-‖x‖^2 := by
    have hi : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [inner_sub_right,Complex.sub_re,inner_smul_right,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hi]
  rw [he] at hr
  have hh := abs_le.mp (hr.trans (hn.trans hm))
  constructor
  · have hEq : (2/(3*baseClock ε s))*‖x‖^2=((2/3:ℝ)*‖x‖^2)/baseClock ε s := by ring
    rw [hEq]
    apply (div_le_iff₀ hC).mpr
    nlinarith only [hh.1]
  · have hEq : (4/(3*baseClock ε s))*‖x‖^2=((4/3:ℝ)*‖x‖^2)/baseClock ε s := by ring
    rw [hEq]
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hh.2]

def actualIncrement (ε h q : ℝ) : ℂ :=
  complexInverse ε (shift (h/2) (q:ℂ))-complexInverse ε (q:ℂ)

theorem actual_clock_identity (ε h q : ℝ) (hε : 0<ε) :
    shiftedClock ε ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q)
      (actualIncrement ε h q)=Complex.exp (complexInverse ε (shift (h/2) (q:ℂ)))+(ε:ℂ) := by
  unfold shiftedClock actualIncrement
  rw [KFCausalComplexClockInverse.complexInverse_real ε hε q]
  congr 2
  ring

theorem actual_metric_bound (ε h q : ℝ) (hε : 0<ε) (hb : |h|≤ε/10) (x : Space) :
    (2/(3*baseClock ε ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q)))*‖x‖^2≤
      (inner ℂ x (metric ε ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q)
        (actualIncrement ε h q) x)).re :=
  (metric_coercive ε _ hε (actualIncrement ε h q)
    (KFCausalIndependentRadialTransverseLines.actual_half_increment ε h q hε hb) x).1

#print axioms ratio_bound
#print axioms normalized_identity
#print axioms normalized_bound
#print axioms metric_coercive
#print axioms actual_clock_identity
#print axioms actual_metric_bound
end
end UnifiedTheory.Audit.KFCausalPhysicalClockMetric
