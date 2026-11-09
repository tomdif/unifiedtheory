/- The apparently singular clock phase p/h has a uniform bound after the
actual imaginary clock shift. Its demodulated factor tends to the expected
longitudinal exponential weight. Epsilon is fixed and positive. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative (inverse_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)

def inverseShift (ε q h : ℝ) : ℂ := complexInverse ε ((q:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)

theorem shiftArgument_mem (ε q h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ((q:ℂ)+((-h/2:ℝ):ℂ)*Complex.I) ∈ targetStrip ε := by
  change |(((q:ℂ)+((-h/2:ℝ):ℂ)*Complex.I):ℂ).im| ≤ Real.pi*ε/2
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,
    abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [abs_nonneg h]

theorem inverseShift_zero (ε q : ℝ) : inverseShift ε q 0 = complexInverse ε (q:ℂ) := by
  simp only [inverseShift,neg_zero,zero_div,Complex.ofReal_zero,zero_mul,add_zero]

theorem inverseShift_difference_bound (ε q h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ‖inverseShift ε q h-inverseShift ε q 0‖ ≤ |h|/(2*ε) := by
  have hr : (q:ℂ) ∈ targetStrip ε := by
    change |(q:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have he := complexInverse_norm_bound ε hε _ (q:ℂ) (shiftArgument_mem ε q h hb) hr
  rw [add_sub_cancel_left,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),div_div] at he
  rw [inverseShift_zero]
  exact he

theorem inverseShift_derivative (ε q : ℝ) (hε : 0 < ε) :
    HasDerivAt (inverseShift ε q) ((-Complex.I/2)*(realClock ε hε q:ℂ)⁻¹) 0 := by
  have hr : (q:ℂ) ∈ targetStrip ε := by
    change |(q:ℂ).im| ≤ Real.pi*ε/2
    simp only [Complex.ofReal_im,abs_zero]
    positivity
  have hp := (((hasDerivAt_id (0:ℂ)).neg.div_const 2).mul_const Complex.I).const_add (q:ℂ)
  have hi : HasDerivAt (complexInverse ε) (complexClock ε (q:ℂ))⁻¹
      ((q:ℂ)+(-(0:ℂ)/2)*Complex.I) := by simpa using inverse_derivative ε hε (q:ℂ) hr
  have hd := hi.comp (0:ℂ) hp
  have ht := hd.comp_ofReal
  convert ht using 1
  · funext h
    simp only [inverseShift,Function.comp_def,Complex.ofReal_div,Complex.ofReal_neg,
      Complex.ofReal_ofNat,Pi.neg_apply,id_eq]
  · rw [complexClock_real ε hε]
    ring

def phaseRatio (ε p q h : ℝ) : ℂ :=
  Complex.exp (Complex.I*(p:ℂ)*(h:ℂ)⁻¹*(inverseShift ε q h-inverseShift ε q 0))

theorem phaseRatio_norm_bound (ε p q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ‖phaseRatio ε p q h‖ ≤ Real.exp (|p|/(2*ε)) := by
  rw [phaseRatio,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_eq_abs,norm_inv,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left (inverseShift_difference_bound ε q h hε hb)
    (mul_nonneg (abs_nonneg p) (inv_nonneg.mpr (abs_nonneg h)))).trans_eq
  field_simp [abs_ne_zero.mpr hh]

theorem clockPhase_factor (ε p q h : ℝ) :
    clockPhase (p/h) (inverseShift ε q h) =
      clockPhase (p/h) (inverseShift ε q 0)*phaseRatio ε p q h := by
  simp only [clockPhase,phaseRatio,← Complex.exp_add,Complex.ofReal_div]
  congr 1
  ring

theorem phaseRatio_tendsto (ε p q : ℝ) (hε : 0 < ε) :
    Tendsto (phaseRatio ε p q) (𝓝[≠] (0:ℝ))
      (𝓝 (Complex.exp ((p/(2*realClock ε hε q):ℝ):ℂ))) := by
  have ht := (inverseShift_derivative ε q hε).tendsto_slope.const_mul (Complex.I*(p:ℂ))
  have he := Complex.continuous_exp.continuousAt.tendsto.comp ht
  convert he using 1
  · funext h
    simp only [phaseRatio,slope_def_module,sub_zero,Complex.real_smul,Complex.ofReal_inv]
    congr 1
    ring
  · congr 2
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem phaseRatio_energy_tendsto (ε p q : ℝ) (hε : 0 < ε) :
    Tendsto (fun h => ‖phaseRatio ε p q h‖^2) (𝓝[≠] (0:ℝ))
      (𝓝 (Real.exp (p/realClock ε hε q))) := by
  have ht := (phaseRatio_tendsto ε p q hε).norm.pow 2
  rw [Complex.norm_exp,Complex.ofReal_re,← Real.exp_nat_mul] at ht
  convert ht using 1
  congr 2
  norm_num only [Nat.cast_ofNat]
  ring

#print axioms shiftArgument_mem
#print axioms inverseShift_zero
#print axioms inverseShift_difference_bound
#print axioms inverseShift_derivative
#print axioms phaseRatio_norm_bound
#print axioms clockPhase_factor
#print axioms phaseRatio_tendsto
#print axioms phaseRatio_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
