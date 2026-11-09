/- Only the real clock shift contributes between real field multiples
of the same wavefunction. Its first-order Taylor term is imaginary, so
the real correction has a quadratic shift bound and a cubic defect weight. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor
import UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalRealShearCorrectionBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (complexDefect realDefect)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol shiftedDefect_physical_coe)
open UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse (realPart realPart_coe)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "D" => defectOperator ε hε

include hε hb in
theorem physical_real_difference (x : Configuration) :
    |defect ε x.1-(physicalSymbol ε h x).re| ≤ (10*h^2/ε^2)*(defect ε x.1)^3 := by
  have ht := KFCausalClockFloorQuantumVelocityScalar.vertical_remainder ε hε (chart ε x.1) (-h/2)
    (KFCausalClockFloorShiftedDefect.shift_bound ε h hb)
  rw [KFCausalClockFloorClockShiftTaylor.real_defect_chart ε hε x] at ht
  have hr := (Complex.abs_re_le_norm
    (complexDefect ε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)-(defect ε x.1:ℂ)-
      ((-h/2:ℝ):ℂ)*Complex.I*(KFCausalClockFloorDefectTransportScalar.drift ε (defect ε x.1):ℂ))).trans ht
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,mul_one,add_zero] at hr
  rw [abs_sub_comm]
  convert hr using 1
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),div_pow,sq_abs]
  ring

def realCorrection : Hilbert →L[ℂ] Hilbert := (1/(ε:ℂ)) • (D-realPart ε hε h hb)

theorem realCorrection_coe (f : Hilbert) :
    realCorrection ε hε h hb f =ᵐ[volume] fun x =>
      (((defect ε x.1-(physicalSymbol ε h x).re)/ε:ℝ):ℂ)*f x := by
  filter_upwards [Lp.coeFn_smul (1/(ε:ℂ)) (D f-realPart ε hε h hb f),
    Lp.coeFn_sub (D f) (realPart ε hε h hb f),defectOperator_coe ε hε f,
    realPart_coe ε hε h hb f] with x hx hs hd hr
  change ((1/(ε:ℂ)) • (D f-realPart ε hε h hb f)) x = _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hs,Pi.sub_apply,hd,hr]
  push_cast
  ring

theorem shearCorrection_coe (f : Hilbert) :
    shearCorrection ε hε h hb f =ᵐ[volume] fun x =>
      (((defect ε x.1:ℂ)-physicalSymbol ε h x)/(ε:ℂ))*f x := by
  let Z := KFCausalClockFloorShiftedDefect.shiftedDefect ε hε h hb
  filter_upwards [Lp.coeFn_smul (1/(ε:ℂ)) (D f-Z f),Lp.coeFn_sub (D f) (Z f),
    defectOperator_coe ε hε f,shiftedDefect_physical_coe ε hε h hb f] with x hx hs hd hz
  change (Z f) x = physicalSymbol ε h x*f x at hz
  change ((1/(ε:ℂ)) • (D f-Z f)) x = _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hs,Pi.sub_apply,hd,hz]
  ring

theorem realCorrection_bound (f : Hilbert) :
    ‖realCorrection ε hε h hb f‖ ≤ (10*h^2/ε^3)*‖D (D (D f))‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [realCorrection_coe ε hε h hb f,defectOperator_coe ε hε (D (D f)),
    defectOperator_coe ε hε (D f),defectOperator_coe ε hε f] with x hr h3 h2 h1
  rw [hr,h3,h2,h1]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hε,
    abs_of_pos (defect_positive ε x.1 hε)]
  calc
    _ ≤ ((10*h^2/ε^2)*(defect ε x.1)^3/ε)*‖f x‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (physical_real_difference ε hε h hb x) hε.le) (norm_nonneg _)
    _ = _ := by ring

#print axioms physical_real_difference
#print axioms realCorrection_coe
#print axioms shearCorrection_coe
#print axioms realCorrection_bound
end
end UnifiedTheory.Audit.KFCausalRealShearCorrectionBound
