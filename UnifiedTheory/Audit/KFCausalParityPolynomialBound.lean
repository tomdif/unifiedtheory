/- Pairing a field polynomial with its charged-coordinate reflection
removes the odd cross terms. The bound is uniform on the existing
inverse-clock strip and retains both physical field powers. -/
import UnifiedTheory.Audit.KFCausalInitialParityReflection
import UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalParityPolynomialBound
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalInitialParityReflection (reflection reflection_apply)
open UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial (transportedValue physical_transported_value)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerValue)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField pointField_apply)

def pairedPower (a : ℂ) (i : Fin 2) (v q : ℝ) : ℝ :=
  ‖((v:ℂ)+a*q)^(i.val+1)‖^2+‖((v:ℂ)-a*q)^(i.val+1)‖^2

theorem paired_linear (a : ℂ) (v q : ℝ) :
    pairedPower a 0 v q = 2*(v^2+‖a‖^2*q^2) := by
  simp [pairedPower,Complex.sq_norm,Complex.normSq_apply]
  ring

theorem paired_quadratic (a : ℂ) (v q : ℝ) :
    pairedPower a 1 v q =
      2*(v^4+(4*a.re^2+2*‖a‖^2)*v^2*q^2+‖a‖^4*q^4) := by
  simp [pairedPower,Complex.sq_norm,Complex.normSq_apply,show ‖a‖^4 = (‖a‖^2)^2 by ring]
  ring

theorem paired_bound (a : ℂ) (K : ℝ) (hK : 1 ≤ K) (ha : ‖a‖ ≤ K)
    (i : Fin 2) (v q : ℝ) : pairedPower a i v q ≤ K^(2*(i.val+1))*pairedPower 1 i v q := by
  have hK2 : 1 ≤ K^2 := one_le_pow₀ hK
  have ha2 : ‖a‖^2 ≤ K^2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  fin_cases i
  · change pairedPower a 0 v q ≤ K^2*pairedPower 1 0 v q
    rw [paired_linear,paired_linear]
    norm_num only [Fin.val_zero,zero_add,mul_one,norm_one,one_pow,one_mul]
    have hv := mul_le_mul_of_nonneg_right hK2 (sq_nonneg v)
    have hq := mul_le_mul_of_nonneg_right ha2 (sq_nonneg q)
    nlinarith
  · change pairedPower a 1 v q ≤ K^4*pairedPower 1 1 v q
    rw [paired_quadratic,paired_quadratic]
    norm_num only [Fin.val_one,Complex.one_re,norm_one,one_pow,one_mul]
    have hK4 : 1 ≤ K^4 := one_le_pow₀ hK
    have h24 : K^2 ≤ K^4 := by nlinarith [sq_nonneg (K^2-1)]
    have ha4 : ‖a‖^4 ≤ K^4 := pow_le_pow_left₀ (norm_nonneg _) ha 4
    have hre : a.re^2 ≤ ‖a‖^2 := by nlinarith [Complex.sq_norm_sub_sq_re a,sq_nonneg a.im]
    have hc : 4*a.re^2+2*‖a‖^2 ≤ 6*K^4 := by linarith
    have hv := mul_le_mul_of_nonneg_right hK4 (by positivity : 0 ≤ v^4)
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg v) (sq_nonneg q))
    have hq := mul_le_mul_of_nonneg_right ha4 (by positivity : 0 ≤ q^4)
    nlinarith

def stripConstant : ℝ := 3*Real.exp (Real.pi/6)+2

theorem stripConstant_ge_one : 1 ≤ stripConstant := by
  unfold stripConstant
  linarith [Real.exp_pos (Real.pi/6)]

theorem coefficient_bound (D : ℂ) (hD : ‖D‖ ≤ Real.pi/3) :
    ‖3*Complex.exp (-D/2)-2‖ ≤ stripConstant := by
  have hr : (-D/2).re ≤ Real.pi/6 := by
    have hd := (abs_le.mp (Complex.abs_re_le_norm D)).1
    simp only [Complex.div_ofNat_re,Complex.neg_re]
    linarith
  calc
    _ ≤ ‖(3:ℂ)*Complex.exp (-D/2)‖+‖(2:ℂ)‖ := norm_sub_le _ _
    _ = 3*Real.exp ((-D/2).re)+2 := by rw [norm_mul,Complex.norm_exp]; norm_num
    _ ≤ stripConstant := by unfold stripConstant; gcongr

theorem physical_paired_bound (D : ℝ → ℂ) (hD : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (i : Fin 2) (x : Configuration) :
    ‖transportedValue (D x.1) pointField i x‖^2+
      ‖transportedValue (D (reflection x).1) pointField i (reflection x)‖^2 ≤
    stripConstant^(2*(i.val+1))*(‖powerValue pointField i x‖^2+
      ‖powerValue pointField i (reflection x)‖^2) := by
  have he := paired_bound (3*Complex.exp (-D x.1/2)-2) stripConstant
    stripConstant_ge_one (coefficient_bound (D x.1) (hD x.1)) i (x.2 4) (x.2 2+x.2 3)
  simpa [pairedPower,physical_transported_value,reflection_apply,powerValue,pointField_apply,
    show (2:Fin 5) ≠ 4 by decide,show (3:Fin 5) ≠ 4 by decide,
    Complex.ofReal_add,Complex.ofReal_neg,neg_add,sub_eq_add_neg,mul_neg,mul_add,
    add_comm,add_left_comm,add_assoc] using he

#print axioms paired_linear
#print axioms paired_quadratic
#print axioms paired_bound
#print axioms stripConstant_ge_one
#print axioms coefficient_bound
#print axioms physical_paired_bound
end
end UnifiedTheory.Audit.KFCausalParityPolynomialBound
