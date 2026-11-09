/- The shifted defect lies strictly inside the disk with diameter [0,1].
Its product with the shifted response has positive real part. These are
actual scalar estimates for the ordered vacuum momentum commutator. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedMomentumSign
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference (shift_mem)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem complexClock_re_above_floor (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) : ε < (complexClock ε q).re := by
  have hi := abs_lt.mp (show |(complexInverse ε q).im| < Real.pi/2 from complexInverse_mem ε hε q hq)
  have hp := mul_pos (Real.exp_pos (complexInverse ε q).re) (Real.cos_pos_of_mem_Ioo hi)
  simpa only [complexClock,Complex.add_re,Complex.exp_re,Complex.ofReal_re,lt_add_iff_pos_left] using hp

theorem complex_defect_disk (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) : ‖complexDefect ε q‖^2 < (complexDefect ε q).re := by
  have hc := complexClock_ne_zero ε hε q hq
  have hp := complexClock_re_above_floor ε hε q hq
  simp only [complexDefect,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,
    Complex.normSq_eq_norm_sq]
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hc))).mpr
    (by nlinarith)

theorem disk_product_real (z : ℂ) (hz : ‖z‖^2 < z.re) :
    0 < (z*(1-z)).re ∧ (z*(1-z)).re ≤ 1/2 := by
  rw [Complex.sq_norm,Complex.normSq_apply] at hz
  simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub]
  constructor <;> nlinarith [sq_nonneg z.im,sq_nonneg (z.re-1/2)]

theorem disk_product_norm (z : ℂ) (hz : ‖z‖^2 ≤ z.re) : ‖z*(1-z)‖ ≤ 1/2 := by
  have hp : 0 ≤ z.re := (sq_nonneg ‖z‖).trans hz
  have hq : ‖1-z‖^2 ≤ 1-z.re := by
    rw [Complex.sq_norm,Complex.normSq_apply] at hz ⊢
    simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub]
    nlinarith
  have hs : 0 ≤ 1-z.re := (sq_nonneg ‖1-z‖).trans hq
  have hm := mul_le_mul hz hq (sq_nonneg ‖1-z‖) hp
  rw [norm_mul]
  nlinarith [sq_nonneg (z.re-1/2),norm_nonneg z,norm_nonneg (1-z)]

theorem physical_momentum_sign (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    0 < (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re ∧
      (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re ≤ 1/2 :=
  disk_product_real _ (complex_defect_disk ε hε _ (shift_mem ε hε h hh x))

theorem physical_momentum_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    ‖physicalSymbol ε h x*(1-physicalSymbol ε h x)‖ ≤ 1/2 :=
  disk_product_norm _ (complex_defect_disk ε hε _ (shift_mem ε hε h hh x)).le

#print axioms complexClock_re_above_floor
#print axioms complex_defect_disk
#print axioms disk_product_real
#print axioms disk_product_norm
#print axioms physical_momentum_sign
#print axioms physical_momentum_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedMomentumSign
