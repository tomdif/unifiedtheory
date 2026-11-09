/- The imaginary clock shift stays uniformly close to the real physical
clock. Its relative complex transverse scale is C1 and uniformly bounded.
These estimates do not assert a force bound or a generator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso chartIso_apply)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (complexScale)

def argument (ε y s : ℝ) : ℂ := (chart ε s:ℂ)+(y:ℂ)*Complex.I
def inverse (ε y s : ℝ) : ℂ := complexInverse ε (argument ε y s)
def relative (ε y s : ℝ) : ℂ := inverse ε y s-(s:ℂ)
def scale (ε y s : ℝ) : ℂ := complexScale (relative ε y s)

theorem argument_smooth (ε y : ℝ) : ContDiff ℝ 1 (argument ε y) := by
  have hc : ContDiff ℝ 1 (chart ε) := by unfold chart; fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hc).add contDiff_const

theorem argument_mem (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    argument ε y s ∈ KFCausalComplexClockChart.targetStrip ε := by
  apply third_strip_subset ε hε
  simpa only [argument,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hy

theorem inverse_smooth (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (inverse ε y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  exact (((complexInverse_analytic ε hε _ (argument_mem ε y s hε hy)).contDiffAt).restrict_scalars ℝ).comp s
    (argument_smooth ε y).contDiffAt

theorem relative_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖relative ε y s‖ ≤ |y|/ε := by
  have hz : complexInverse ε (chart ε s:ℂ) = (s:ℂ) := by
    rw [complexInverse_real ε hε,← chartIso_apply ε hε]
    simp only [OrderIso.symm_apply_apply]
  have hr := argument_mem ε 0 s hε (by simp; positivity)
  simp only [argument,Complex.ofReal_zero,zero_mul,add_zero] at hr
  have hb := complexInverse_norm_bound ε hε (argument ε y s) (chart ε s:ℂ)
    (argument_mem ε y s hε hy) hr
  simpa only [relative,inverse,hz,argument,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] using hb

theorem scale_smooth (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ContDiff ℝ 1 (scale ε y) :=
  (((inverse_smooth ε y hε hy).sub Complex.ofRealCLM.contDiff).div_const 2).cexp

theorem scale_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖scale ε y s‖ ≤ Real.exp (|y|/(2*ε)) := by
  simp only [scale,complexScale,Complex.norm_exp,Complex.div_ofNat_re]
  apply Real.exp_le_exp.mpr
  have hb := (Complex.re_le_norm (relative ε y s)).trans (relative_bound ε y s hε hy)
  calc (relative ε y s).re/2 ≤ (|y|/ε)/2 := div_le_div_of_nonneg_right hb (by norm_num)
       _ = |y|/(2*ε) := by ring

#print axioms argument_smooth
#print axioms argument_mem
#print axioms inverse_smooth
#print axioms relative_bound
#print axioms scale_smooth
#print axioms scale_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
