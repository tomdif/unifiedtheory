/- The actual imaginary clock shift has a controlled left-clock limit.
This is a scalar ingredient for testing displaced coherent-state energy
comparisons, not a quantum clock-escape or Hamiltonian-energy theorem. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockShiftLeftAsymptotic
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalComplexClockChart (complexChart)
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse_right)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient

theorem relative_equation (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (ε:ℂ)*(relative ε y s-(y:ℂ)*Complex.I/(ε:ℂ)) =
      (Real.exp s:ℂ)*(1-Complex.exp (relative ε y s)) := by
  have hi := complexInverse_right ε hε (argument ε y s) (argument_mem ε y s hε hy)
  change complexChart ε (inverse ε y s) = argument ε y s at hi
  have hz : inverse ε y s = (s:ℂ)+relative ε y s := by unfold relative; ring
  rw [hz,complexChart,Complex.exp_add,← Complex.ofReal_exp] at hi
  simp only [argument,chart,Complex.ofReal_add,Complex.ofReal_mul] at hi
  have he : (ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  field_simp [he]
  linear_combination hi

theorem relative_exp_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖Complex.exp (relative ε y s)‖ ≤ Real.exp (|y|/ε) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (relative_bound ε y s hε hy))

theorem relative_error_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖relative ε y s-(y:ℂ)*Complex.I/(ε:ℂ)‖ ≤
      Real.exp s*((1+Real.exp (|y|/ε))/ε) := by
  have hn := congrArg norm (relative_equation ε y s hε hy)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε,
    abs_of_pos (Real.exp_pos s)] at hn
  have hb : ‖1-Complex.exp (relative ε y s)‖ ≤ 1+Real.exp (|y|/ε) :=
    (norm_sub_le _ _).trans (by
      simpa only [norm_one] using (add_le_add (le_refl (1:ℝ)) (relative_exp_bound ε y s hε hy)))
  have hs := mul_le_mul_of_nonneg_left hb (Real.exp_pos s).le
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hε).mpr
  nlinarith only [hn,hs]

theorem relative_tendsto (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (relative ε y) atBot (𝓝 ((y:ℂ)*Complex.I/(ε:ℂ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _) (fun s => relative_error_bound ε y s hε hy)
  simpa only [zero_mul] using Real.tendsto_exp_atBot.mul_const ((1+Real.exp (|y|/ε))/ε)

theorem displacement_error_bound (ε h s : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    ‖displacement ε h s-(-Complex.I*(h:ℂ)/(2*(ε:ℂ)))‖ ≤
      Real.exp s*((1+Real.exp (|h|/(2*ε)))/ε) := by
  have he := relative_error_bound ε (-h/2) s hε (half_shift_bound ε h hb)
  have hv : ((-h/2:ℝ):ℂ)*Complex.I/(ε:ℂ) = -Complex.I*(h:ℂ)/(2*(ε:ℂ)) := by
    push_cast
    ring
  have ha : |-h/2|/ε = |h|/(2*ε) := by rw [abs_div,abs_neg]; norm_num; ring
  simpa only [displacement,hv,ha] using he

theorem displacement_tendsto (ε h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    Tendsto (displacement ε h) atBot (𝓝 (-Complex.I*(h:ℂ)/(2*(ε:ℂ)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _) (fun s => displacement_error_bound ε h s hε hb)
  simpa only [zero_mul] using Real.tendsto_exp_atBot.mul_const ((1+Real.exp (|h|/(2*ε)))/ε)

theorem coefficient_tendsto (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    Tendsto (coefficient ε h) atBot (𝓝 ((1/(2*ε):ℝ):ℂ)) := by
  have ht := ((displacement_tendsto ε h hε hb).const_mul Complex.I).div_const (h:ℂ)
  have he : Complex.I*(-Complex.I*(h:ℂ)/(2*(ε:ℂ)))/(h:ℂ) = ((1/(2*ε):ℝ):ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hh,Complex.ofReal_ne_zero.mpr hε.ne']
    linear_combination -Complex.I_sq
  simpa only [coefficient,he] using ht

theorem scale_tendsto (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Tendsto (scale ε y) atBot (𝓝 (Complex.exp ((y:ℂ)*Complex.I/(2*(ε:ℂ))))) := by
  have ht := Complex.continuous_exp.continuousAt.tendsto.comp
    ((relative_tendsto ε y hε hy).div_const (2:ℂ))
  convert ht using 1
  congr 2
  ring

#print axioms relative_equation
#print axioms relative_exp_bound
#print axioms relative_error_bound
#print axioms relative_tendsto
#print axioms displacement_error_bound
#print axioms displacement_tendsto
#print axioms coefficient_tendsto
#print axioms scale_tendsto
end
end UnifiedTheory.Audit.KFCausalClockShiftLeftAsymptotic
