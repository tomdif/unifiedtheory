/- A real square-root weight for the imaginary shifted clock defect.
The weight is bounded by the actual defect, including either sign of hbar. -/
import UnifiedTheory.Audit.KFCausalClockShearRealMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorShearWeight
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hbound : |h| ≤ 2*Real.pi*ε/3)

def coefficient (s : ℝ) : ℝ := ε*(physicalSymbol ε h (s,0)).im/(2*h)
def rootValue (s : ℝ) : ℝ := Real.sqrt (coefficient ε h s)

include hε hbound

theorem symbol_im_sign (s : ℝ) : 0 ≤ h*(physicalSymbol ε h (s,0)).im := by
  have hs := KFCausalClockFloorDefectSign.complexDefect_im_sign ε hε
    ((chart ε s:ℂ)+(-h/2:ℝ)*Complex.I)
    (KFCausalClockFloorFullGaussian.third_strip_subset ε hε _
      (by simpa using KFCausalClockFloorShiftedDefect.shift_bound ε h hbound))
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hs
  change 0 ≤ h*(complexDefect ε ((chart ε s:ℂ)+(-h/2:ℝ)*Complex.I)).im
  nlinarith

theorem symbol_im_bound (s : ℝ) :
    |(physicalSymbol ε h (s,0)).im| ≤ (2*|h|/ε)*(defect ε s)^2 := by
  have he : realDefect ε hε (chart ε s) = defect ε s := by
    unfold realDefect
    change defect ε ((chartIso ε hε).symm ((chartIso ε hε) s)) = _
    rw [(chartIso ε hε).symm_apply_apply]
  have hb := KFCausalClockFloorDefectShift.half_exponential_shift_difference ε h (chart ε s) hε hbound
  rw [he] at hb
  have hi := Complex.abs_im_le_norm
    (physicalSymbol ε h (s,0)-(defect ε s:ℂ))
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  exact hi.trans hb

theorem coefficient_bounds (hne : h ≠ 0) (s : ℝ) :
    0 ≤ coefficient ε h s ∧ coefficient ε h s ≤ (defect ε s)^2 := by
  have hs := symbol_im_sign ε hε h hbound s
  constructor
  · unfold coefficient
    rcases lt_or_gt_of_ne hne with hn | hp
    · have hi : (physicalSymbol ε h (s,0)).im ≤ 0 := by nlinarith
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hε.le hi) (by linarith)
    · have hi : 0 ≤ (physicalSymbol ε h (s,0)).im := by nlinarith
      exact div_nonneg (mul_nonneg hε.le hi) (by positivity)
  · calc
      coefficient ε h s ≤ |coefficient ε h s| := le_abs_self _
      _ = (ε/(2*|h|))*|(physicalSymbol ε h (s,0)).im| := by
        unfold coefficient
        rw [abs_div,abs_mul,abs_mul,abs_of_pos hε]
        norm_num
        ring
      _ ≤ (ε/(2*|h|))*((2*|h|/ε)*(defect ε s)^2) :=
        mul_le_mul_of_nonneg_left (symbol_im_bound ε hε h hbound s) (by positivity)
      _ = (defect ε s)^2 := by field_simp [abs_ne_zero.mpr hne,hε.ne']

theorem rootValue_bounds (hne : h ≠ 0) (s : ℝ) :
    0 ≤ rootValue ε h s ∧ rootValue ε h s ≤ defect ε s := by
  have hs := Real.sq_sqrt (coefficient_bounds ε hε h hbound hne s).1
  have hd := defect_positive ε s hε
  have hb := (coefficient_bounds ε hε h hbound hne s).2
  exact ⟨Real.sqrt_nonneg _,by unfold rootValue; nlinarith⟩

theorem rootValue_square (hne : h ≠ 0) (s : ℝ) :
    (rootValue ε h s)^2 = coefficient ε h s :=
  Real.sq_sqrt (coefficient_bounds ε hε h hbound hne s).1

theorem rootValue_continuous : Continuous (rootValue ε h) := by
  have hs : Continuous (fun s : ℝ => physicalSymbol ε h (s,0)) :=
    (physicalSymbol_continuous ε hε h hbound).comp
    ((continuous_id : Continuous (fun s : ℝ => s)).prodMk continuous_const)
  unfold rootValue coefficient
  exact ((continuous_const.mul (Complex.continuous_im.comp hs)).div_const _).sqrt

theorem rootValue_contractive (hne : h ≠ 0) (s : ℝ) : ‖(rootValue ε h s:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rootValue_bounds ε hε h hbound hne s).1]
  apply (rootValue_bounds ε hε h hbound hne s).2.trans
  have hd := KFCausalClockFloorDefectOperator.weight_bound ε hε (s,0)
  simpa only [KFCausalClockFloorDefectOperator.weight,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (defect_positive ε s hε)] using hd

def root (hne : h ≠ 0) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x => (rootValue ε h x.1:ℂ))
    (Complex.continuous_ofReal.comp ((rootValue_continuous ε hε h hbound).comp continuous_fst)).measurable
    (fun x => rootValue_contractive ε hε h hbound hne x.1)

theorem root_coe (hne : h ≠ 0) (f : Hilbert) :
    root ε hε h hbound hne f =ᵐ[volume] fun x => (rootValue ε h x.1:ℂ)*f x :=
  multiplyL_coe _ _ _ f

theorem root_norm_le_defect (hne : h ≠ 0) (f : Hilbert) :
    ‖root ε hε h hbound hne f‖ ≤ ‖defectOperator ε hε f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [root_coe ε hε h hbound hne f,defectOperator_coe ε hε f] with x hr hd
  rw [hr,hd,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (rootValue_bounds ε hε h hbound hne x.1).1,
    abs_of_pos (defect_positive ε x.1 hε)]
  exact mul_le_mul_of_nonneg_right (rootValue_bounds ε hε h hbound hne x.1).2 (norm_nonneg _)

#print axioms symbol_im_sign
#print axioms symbol_im_bound
#print axioms coefficient_bounds
#print axioms rootValue_bounds
#print axioms rootValue_square
#print axioms rootValue_continuous
#print axioms rootValue_contractive
#print axioms root_coe
#print axioms root_norm_le_defect
end
end UnifiedTheory.Audit.KFCausalClockFloorShearWeight
