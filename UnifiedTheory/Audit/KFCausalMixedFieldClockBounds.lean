/- A field at one complex clock shift is controlled by the neutral
coordinate at another nonzero shift. The derived clock growth is
absorbed by Gaussian amplitudes, preserving the full correlated sum. -/
import UnifiedTheory.Audit.KFCausalShiftedNeutralCoercivity
import UnifiedTheory.Audit.KFCausalShiftedPolynomialClockWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalMixedFieldClockBounds
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedNeutralCoercivity (scaleBound scaleBound_positive inverseBound inverseBound_positive inverseBound_continuous inverse_scale_bound)
open KFCausalShiftedPolynomialClockWeights (weight weight_positive weight_continuous exponential_bound)

def field (r : ℂ) (q : Transverse) : ℂ := (q 4:ℂ)+(3*r-2)*((q 2+q 3:ℝ):ℂ)

theorem field_decomposition (r t : ℂ) (q : Transverse) :
    field r q = position t q 4+(3*r-2*t)*((q 2+q 3:ℝ):ℂ) := by
  simp only [field,position,ite_true]
  push_cast
  ring

theorem neutral_im (r : ℂ) (q : Transverse) : (position r q 4).im = 2*r.im*(q 2+q 3) := by
  simp [position,Complex.mul_im]

theorem charged_sum_bound (r : ℂ) (hr : r.im ≠ 0) (q : Transverse) :
    |q 2+q 3| ≤ (1/|r.im|)*‖position r q 4‖ := by
  rw [div_mul_eq_mul_div,one_mul]
  apply (le_div_iff₀ (abs_pos.mpr hr)).mpr
  have hi := Complex.abs_im_le_norm (position r q 4)
  rw [neutral_im] at hi
  norm_num only [abs_mul] at hi
  nlinarith [mul_nonneg (abs_nonneg r.im) (abs_nonneg (q 2+q 3))]

theorem field_neutral_bound (r t : ℂ) (ht : t.im ≠ 0) (q : Transverse) :
    ‖field r q‖ ≤ (1+(3*‖r‖+2*‖t‖)*(1/|t.im|))*‖position t q 4‖ := by
  have hc : ‖3*r-2*t‖ ≤ 3*‖r‖+2*‖t‖ := by
    simpa using norm_sub_le ((3:ℂ)*r) ((2:ℂ)*t)
  have hm := mul_le_mul hc (charged_sum_bound t ht q)
    (abs_nonneg (q 2+q 3)) (by positivity : 0 ≤ 3*‖r‖+2*‖t‖)
  have hn := norm_add_le (position t q 4) ((3*r-2*t)*((q 2+q 3:ℝ):ℂ))
  rw [← field_decomposition,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  nlinarith only [hm,hn]

def growthConstant (ε y : ℝ) : ℝ := scaleBound ε y*(2+ε*Real.pi)/|y|
def fieldBound (ε y z s : ℝ) : ℝ := 1+(3*scaleBound ε z+2*scaleBound ε y)*inverseBound ε y s
def fieldConstant (ε y z : ℝ) : ℝ := 1+(3*scaleBound ε z+2*scaleBound ε y)*growthConstant ε y

theorem inverseBound_growth (ε y s : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    inverseBound ε y s ≤ growthConstant ε y*weight ε s := by
  have he := exponential_bound ε s hε.le
  have hw : 1 ≤ weight ε s := by unfold weight; linarith [abs_nonneg (KFCausalRegularizedLongitudinalChart.chart ε s)]
  have hh : 2*Real.exp s+ε*Real.pi ≤ (2+ε*Real.pi)*weight ε s := by
    nlinarith [mul_le_mul_of_nonneg_left hw (mul_pos hε Real.pi_pos).le]
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (scaleBound_positive ε y).le) (abs_pos.mpr hy).le
  simpa only [inverseBound,growthConstant,mul_div_assoc,div_mul_eq_mul_div,mul_assoc] using hm

theorem fieldBound_positive (ε y z s : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    0 < fieldBound ε y z s := by
  have hi := inverseBound_positive ε y s hε hy
  have hr := scaleBound_positive ε z
  have ht := scaleBound_positive ε y
  unfold fieldBound
  positivity

theorem fieldBound_continuous (ε y z : ℝ) : Continuous (fieldBound ε y z) :=
  continuous_const.add (continuous_const.mul (inverseBound_continuous ε y))

theorem fieldConstant_positive (ε y z : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    0 < fieldConstant ε y z := by unfold fieldConstant growthConstant scaleBound; positivity

theorem fieldBound_growth (ε y z s : ℝ) (hε : 0 < ε) (hy : y ≠ 0) :
    fieldBound ε y z s ≤ fieldConstant ε y z*weight ε s := by
  have hg := inverseBound_growth ε y s hε hy
  have hR : 0 ≤ 3*scaleBound ε z+2*scaleBound ε y := by
    have := scaleBound_positive ε z; have := scaleBound_positive ε y; positivity
  have hm := mul_le_mul_of_nonneg_left hg hR
  have hw : 1 ≤ weight ε s := by unfold weight; linarith [abs_nonneg (KFCausalRegularizedLongitudinalChart.chart ε s)]
  unfold fieldBound fieldConstant
  nlinarith only [hm,hw]

theorem actual_field_bound (ε y z s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (q : Transverse) :
    ‖field (scale ε z s) q‖ ≤ fieldBound ε y z s*‖position (scale ε y s) q 4‖ := by
  have ht := KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0
  have hf := field_neutral_bound (scale ε z s) (scale ε y s) ht q
  have hc : 3*‖scale ε z s‖+2*‖scale ε y s‖ ≤ 3*scaleBound ε z+2*scaleBound ε y := by
    have hr := KFCausalClockFloorRelativeShift.scale_bound ε z s hε hz
    have hs := KFCausalClockFloorRelativeShift.scale_bound ε y s hε hy
    change ‖scale ε z s‖ ≤ scaleBound ε z at hr
    change ‖scale ε y s‖ ≤ scaleBound ε y at hs
    linarith
  have hm := mul_le_mul hc (inverse_scale_bound ε y s hε hy hy0)
    (by positivity : 0 ≤ 1/|(scale ε y s).im|)
    (by have := scaleBound_positive ε z; have := scaleBound_positive ε y; positivity)
  exact hf.trans (mul_le_mul_of_nonneg_right (add_le_add_right hm 1) (norm_nonneg _))

#print axioms field_decomposition
#print axioms neutral_im
#print axioms charged_sum_bound
#print axioms field_neutral_bound
#print axioms inverseBound_growth
#print axioms fieldBound_positive
#print axioms fieldBound_continuous
#print axioms fieldConstant_positive
#print axioms fieldBound_growth
#print axioms actual_field_bound
end
end UnifiedTheory.Audit.KFCausalMixedFieldClockBounds
