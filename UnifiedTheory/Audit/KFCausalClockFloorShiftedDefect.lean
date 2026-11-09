/- The analytic shifted defect is a bounded operator on all physical L2.
This enables passage of the exponential intertwining identity to graph
limits. It does not assert that the analytic states form a graph core. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectSign
import UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorDefectForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalContractiveMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorDefectSign
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

def symbol (x : Space) : ℂ := complexDefect ε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)

include hh in
theorem shift_bound : |-hbar/2| ≤ Real.pi*ε/3 := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

include hε hh in
theorem symbol_continuous : Continuous (symbol ε hbar) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (complexDefect_analytic ε hε _
    (KFCausalClockFloorFullGaussian.third_strip_subset ε hε _
      (by simpa using shift_bound ε hbar hh))).continuousAt.comp (by fun_prop)

include hε hh in
theorem symbol_bound (x : Space) : ‖symbol ε hbar x‖ ≤ 2 :=
  complexDefect_norm_le_two ε hε _ (by simpa using shift_bound ε hbar hh)

include hε hh in
theorem normalized_symbol_bound (x : Space) : ‖symbol ε hbar x / 2‖ ≤ 1 := by
  rw [norm_div]
  have ht : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [ht]
  linarith [symbol_bound ε hε hbar hh x]

def frequencyOperator : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  (2:ℂ) • multiplyL (fun x => symbol ε hbar x / 2)
    ((symbol_continuous ε hε hbar hh).div_const 2).measurable
    (normalized_symbol_bound ε hε hbar hh)

def shiftedDefect : Hilbert →L[ℂ] Hilbert :=
  ((straightening ε hε).symm : FrequencyHilbert →L[ℂ] Hilbert).comp
    ((frequencyOperator ε hε hbar hh).comp (straightening ε hε : Hilbert →L[ℂ] FrequencyHilbert))

theorem frequencyOperator_coe (f : FrequencyHilbert) :
    frequencyOperator ε hε hbar hh f =ᵐ[volume] fun x => symbol ε hbar x * f x := by
  filter_upwards [Lp.coeFn_smul (2:ℂ) (multiplyL (fun x => symbol ε hbar x / 2)
    ((symbol_continuous ε hε hbar hh).div_const 2).measurable
    (normalized_symbol_bound ε hε hbar hh) f),
    multiplyL_coe (fun x => symbol ε hbar x / 2)
      ((symbol_continuous ε hε hbar hh).div_const 2).measurable
      (normalized_symbol_bound ε hε hbar hh) f] with x hs hm
  change ((2:ℂ) • multiplyL _ _ _ f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hm]
  ring

theorem shiftedDefect_coe (f : Hilbert) :
    straightening ε hε (shiftedDefect ε hε hbar hh f) =ᵐ[volume]
      fun x => symbol ε hbar x * (straightening ε hε f) x := by
  change straightening ε hε ((straightening ε hε).symm _) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact frequencyOperator_coe ε hε hbar hh _

theorem shiftedDefect_square_coe (f : Hilbert) :
    straightening ε hε (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f)) =ᵐ[volume]
      fun x => symbol ε hbar x ^ 2 * (straightening ε hε f) x := by
  filter_upwards [shiftedDefect_coe ε hε hbar hh (shiftedDefect ε hε hbar hh f),
    shiftedDefect_coe ε hε hbar hh f] with x h1 h0
  rw [h1,h0,pow_two,mul_assoc]

theorem shiftedDefect_norm_bound (f : Hilbert) :
    ‖shiftedDefect ε hε hbar hh f‖ ≤ 2*‖defectOperator ε hε f‖ := by
  rw [← (straightening ε hε).norm_map (shiftedDefect ε hε hbar hh f),
    ← (straightening ε hε).norm_map (defectOperator ε hε f)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [shiftedDefect_coe ε hε hbar hh f,straightening_defect_coe ε hε f] with x hx hd
  rw [hx,hd]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (realDefect_positive ε hε (x 0))]
  have hb := complexDefect_norm_bound ε hε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)
    (by simpa using shift_bound ε hbar hh)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero] at hb
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (norm_nonneg ((straightening ε hε f) x))

#print axioms shift_bound
#print axioms symbol_continuous
#print axioms symbol_bound
#print axioms normalized_symbol_bound
#print axioms frequencyOperator_coe
#print axioms shiftedDefect_coe
#print axioms shiftedDefect_square_coe
#print axioms shiftedDefect_norm_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
