/- The positive longitudinal response dominates D(1-D) on the actual
closed imaginary-clock strip. This quantitative lower bound permits
absorption of the real field-derivative correction. -/
import UnifiedTheory.Audit.KFCausalTwoEndpointCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLongitudinalResponseCoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalShiftedResponseComparison
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse)
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds (inverse_exp_re_lower)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chartIso)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem sector_product_lower (ε : ℝ) (hε : 0 < ε) (w : ℂ) (hw : ‖w‖/2 ≤ w.re) :
    ε*‖w‖/(2*‖(ε:ℂ)+w‖^2) ≤
      ((ε:ℂ)/((ε:ℂ)+w)*(1-(ε:ℂ)/((ε:ℂ)+w))).re := by
  have hw0 : 0 ≤ w.re := (by positivity : (0:ℝ) ≤ ‖w‖/2).trans hw
  have hn : (ε:ℂ)+w ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at he
    linarith
  let N := Complex.normSq ((ε:ℂ)+w)
  have hN : 0 < N := Complex.normSq_pos.mpr hn
  have hs : ‖w‖^2 = w.re^2+w.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hNe : N = ε^2+2*ε*w.re+‖w‖^2 := by
    rw [hs]
    simp only [N,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    ring
  have he : ((ε:ℂ)/((ε:ℂ)+w)*(1-(ε:ℂ)/((ε:ℂ)+w))).re =
      ε*(w.re*(ε^2+‖w‖^2)+2*ε*‖w‖^2)/N^2 := by
    simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,zero_sub,
      Complex.add_re,Complex.add_im,zero_add,neg_neg]
    change (ε*(ε+w.re)/N)*(1-ε*(ε+w.re)/N)-(-(ε*w.im/N))*(ε*w.im/N) = _
    field_simp
    rw [hNe,hs]
    ring
  have hp := mul_le_mul_of_nonneg_right hw (add_nonneg (sq_nonneg ε) (sq_nonneg ‖w‖))
  have hq := mul_le_mul_of_nonneg_left (Complex.re_le_norm w) (mul_nonneg hε.le (norm_nonneg w))
  have hm : ‖w‖*N/2 ≤ w.re*(ε^2+‖w‖^2)+2*ε*‖w‖^2 := by
    rw [hNe]
    nlinarith only [hp,hq,mul_nonneg hε.le (sq_nonneg ‖w‖)]
  rw [he,Complex.sq_norm]
  change ε*‖w‖/(2*N) ≤ _
  calc
    _ = ε*(‖w‖*N/2)/N^2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hε.le) (sq_nonneg N)

theorem complex_momentum_lower (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    (1/(2*stripFactor^2))*realDefect ε hε q.re*(1-realDefect ε hε q.re) ≤
      (complexDefect ε q*(1-complexDefect ε q)).re := by
  have hK : 0 < stripFactor := lt_of_lt_of_le (by norm_num) one_le_stripFactor
  have hC := realClock_positive ε hε q.re
  have hn := complexClock_ne_zero ε hε q (KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq)
  have hw : ‖Complex.exp (complexInverse ε q)‖/2 ≤ (Complex.exp (complexInverse ε q)).re := by
    rw [Complex.norm_exp]
    exact inverse_exp_re_lower ε hε q hq
  have hs := sector_product_lower ε hε (Complex.exp (complexInverse ε q)) hw
  have he : (ε:ℂ)+Complex.exp (complexInverse ε q) = complexClock ε q := by
    unfold complexClock
    ring
  rw [he] at hs
  apply le_trans _ hs
  have hu := pow_le_pow_left₀ (norm_nonneg (complexClock ε q)) (complexClock_norm_upper ε hε q hq) 2
  calc
    _ = ε*Real.exp ((chartIso ε hε).symm q.re)/(2*(stripFactor*realClock ε hε q.re)^2) := by
      rw [real_response_eq]
      change (1/(2*stripFactor^2))*(ε/realClock ε hε q.re)*
        (Real.exp ((chartIso ε hε).symm q.re)/realClock ε hε q.re) = _
      field_simp
    _ ≤ ε*‖Complex.exp (complexInverse ε q)‖/(2*(stripFactor*realClock ε hε q.re)^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (inverse_exp_comparison ε hε q hq).1 hε.le)
        (by positivity)
    _ ≤ ε*‖Complex.exp (complexInverse ε q)‖/(2*‖complexClock ε q‖^2) :=
      div_le_div_of_nonneg_left (mul_nonneg hε.le (norm_nonneg _))
        (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hn)))
        (mul_le_mul_of_nonneg_left hu (by norm_num))

theorem physical_momentum_lower (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : Configuration) :
    (1/(2*stripFactor^2))*defect ε x.1*(1-defect ε x.1) ≤
      (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re := by
  have hm := complex_momentum_lower ε hε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)
    (by simpa using KFCausalClockFloorShiftedDefect.shift_bound ε h hb)
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    mul_zero,zero_mul,sub_zero,add_zero,KFCausalClockFloorClockShiftTaylor.real_defect_chart ε hε x] using hm

#print axioms sector_product_lower
#print axioms complex_momentum_lower
#print axioms physical_momentum_lower
end
end UnifiedTheory.Audit.KFCausalLongitudinalResponseCoercivity
