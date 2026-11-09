/- Bounds and sign for the bounded shifted-defect operator on arbitrary
physical L2 vectors, and its exact action on the analytic exponential images. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
import UnifiedTheory.Audit.KFCausalSignedMultiplierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorDefectSign

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

theorem shiftedDefect_difference (f : Hilbert) :
    ‖shiftedDefect ε hε hbar hh f-defectOperator ε hε f‖ ≤
      (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε f)‖ := by
  rw [← (straightening ε hε).norm_map (shiftedDefect ε hε hbar hh f-defectOperator ε hε f),
    ← (straightening ε hε).norm_map (defectOperator ε hε (defectOperator ε hε f)),map_sub]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (straightening ε hε (shiftedDefect ε hε hbar hh f))
      (straightening ε hε (defectOperator ε hε f)),shiftedDefect_coe ε hε hbar hh f,
    straightening_defect_coe ε hε f,straightening_defect_coe ε hε (defectOperator ε hε f)] with x hs hb hd hdd
  rw [hs,Pi.sub_apply,hb,hdd,hd,← sub_mul]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (realDefect_positive ε hε (x 0))]
  have h := mul_le_mul_of_nonneg_right (half_exponential_shift_difference ε hbar (x 0) hε hh)
    (norm_nonneg ((straightening ε hε f) x))
  simpa only [symbol,pow_two,mul_assoc] using h

theorem shiftedDefect_square_difference (f : Hilbert) :
    ‖shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f)-
      defectOperator ε hε (defectOperator ε hε f)‖ ≤
      (6*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε (defectOperator ε hε f))‖ := by
  rw [← (straightening ε hε).norm_map (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f)-
      defectOperator ε hε (defectOperator ε hε f)),
    ← (straightening ε hε).norm_map (defectOperator ε hε (defectOperator ε hε (defectOperator ε hε f))),map_sub]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
      (straightening ε hε (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f)))
      (straightening ε hε (defectOperator ε hε (defectOperator ε hε f))),
    shiftedDefect_square_coe ε hε hbar hh f,straightening_defect_coe ε hε f,
    straightening_defect_coe ε hε (defectOperator ε hε f),
    straightening_defect_coe ε hε (defectOperator ε hε (defectOperator ε hε f))] with x hs hb hd hdd hddd
  rw [hs,Pi.sub_apply,hb,hddd,hdd,hd]
  have he : symbol ε hbar x^2*(straightening ε hε f) x-
      (realDefect ε hε (x 0):ℂ)*((realDefect ε hε (x 0):ℂ)*(straightening ε hε f) x) =
      (symbol ε hbar x^2-(realDefect ε hε (x 0):ℂ)^2)*(straightening ε hε f) x := by ring
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (realDefect_positive ε hε (x 0))]
  have h := mul_le_mul_of_nonneg_right (half_exponential_square_difference ε hbar (x 0) hε hh)
    (norm_nonneg ((straightening ε hε f) x))
  simpa only [symbol,pow_succ,pow_zero,one_mul,mul_assoc] using h

theorem shiftedDefect_square_form_sign (f : Hilbert) :
    0 ≤ hbar*(inner ℂ f (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f))).im := by
  have h := KFCausalSignedMultiplierPairing.signed_inner_nonnegative
    (fun x => symbol ε hbar x^2) hbar
    (straightening ε hε f)
    (straightening ε hε (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh f)))
    (fun x => half_exponential_square_sign ε hbar (x 0) hε hh)
    (shiftedDefect_square_coe ε hε hbar hh f)
  simpa only [LinearIsometryEquiv.inner_map_map] using h

theorem shifted_state_successor (a α β p : ℝ) (b : Fin 5 → ℂ)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (n : ℕ)
    (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    shiftedDefect ε hε hbar hh (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs) =
      state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [shiftedDefect_coe ε hε hbar hh (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs),
    state_coe ε a α β p b hε ha hα hβ hw n (-hbar/2) hs,
    state_coe ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs] with x hb hn hn1
  rw [hb,hn,hn1,pow_succ']
  exact (mul_assoc _ _ _).symm

#print axioms shiftedDefect_difference
#print axioms shiftedDefect_square_difference
#print axioms shiftedDefect_square_form_sign
#print axioms shifted_state_successor

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
