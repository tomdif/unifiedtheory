/- Two-width coercivity: exact determinant inequalities, with no width-count extrapolation. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthCoercivity
noncomputable section
open scoped ComplexOrder

theorem cubic_ratio_comparison (A T e d : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (he : 0 ≤ e) (hTA : T ≤ 2*A) (hd : T+4*e ≤ d) :
    T^3*(A+e)^2 ≤ A^2*d^3 := by
  have hT2 : T^2 ≤ 4*A^2 := by nlinarith [sq_nonneg (2*A-T)]
  have h1 : 0 ≤ e*T^2*A*(12*A-2*T) := by
    apply mul_nonneg
    · positivity
    · linarith
  have h2 : 0 ≤ e^2*T*(48*A^2-T^2) := by
    apply mul_nonneg
    · positivity
    · nlinarith [sq_nonneg A]
  have h3 : 0 ≤ 64*A^2*e^3 := by positivity
  have hbase : T^3*(A+e)^2 ≤ A^2*(T+4*e)^3 := by
    nlinarith only [h1,h2,h3]
  have hc : (T+4*e)^3 ≤ d^3 := pow_le_pow_left₀ (by positivity) hd 3
  exact hbase.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg A))

theorem tilted_ratio_comparison (u β d : ℝ) (hu : 1 ≤ u) (hd : 0 < d)
    (hD : (1+u^2)^2+4*β^2*(u^2-1)^2 ≤ d^2) :
    ((u^2+3/4)^2+β^2*(u^2-1)^2)*(1+u^2)^3 ≤ (u^2+3/4)^2*d^3 := by
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hu2 : 1 ≤ u^2 := by nlinarith
  have hAT : (1+u^2)^2 ≤ 2*(u^2+3/4)^2 := by nlinarith [sq_nonneg (u^2)]
  have h := cubic_ratio_comparison ((u^2+3/4)^2) ((1+u^2)^2)
    (β^2*(u^2-1)^2) (d^2) (sq_nonneg _) (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hAT (by nlinarith only [hD])
  have hs :
      (((u^2+3/4)^2+β^2*(u^2-1)^2)*(1+u^2)^3)^2 ≤
      ((u^2+3/4)^2*d^3)^2 := by nlinarith only [h]
  have hleft : 0 ≤ ((u^2+3/4)^2+β^2*(u^2-1)^2)*(1+u^2)^3 := by positivity
  have hright : 0 ≤ (u^2+3/4)^2*d^3 := by positivity
  nlinarith only [hs,hleft,hright]

theorem real_two_width_determinant (u : ℝ) (hu : 1 ≤ u) :
    8*u^3*(u^2+3/4)^2 ≤ (7/4)*(2*u^2-1/4)*(1+u^2)^3 := by
  have hu1 : 0 ≤ u-1 := by linarith
  have h : 0 ≤ (u-1)^2 *
      (56*(u-1)^6+320*(u-1)^5+833*(u-1)^4+1222*(u-1)^3+
       1042*(u-1)^2+472*(u-1)+76) := by positivity
  nlinarith only [h]

theorem two_width_determinant (u β d : ℝ) (hu : 1 ≤ u) (hd : 0 < d)
    (hD : (1+u^2)^2+4*β^2*(u^2-1)^2 ≤ d^2) :
    8*u^3*((u^2+3/4)^2+β^2*(u^2-1)^2) ≤ (7/4)*(2*u^2-1/4)*d^3 := by
  have htilt := tilted_ratio_comparison u β d hu hd hD
  have hbase := real_two_width_determinant u hu
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hQ : 0 < (1+u^2)^3 := by positivity
  have h1 := mul_le_mul_of_nonneg_left htilt (show 0 ≤ 8*u^3 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hbase (show 0 ≤ d^3 by positivity)
  have h : (8*u^3*((u^2+3/4)^2+β^2*(u^2-1)^2))*(1+u^2)^3 ≤
      ((7/4)*(2*u^2-1/4)*d^3)*(1+u^2)^3 := by
    nlinarith only [h1,h2]
  exact le_of_mul_le_mul_right h hQ

theorem two_by_two_positive (d0 d1 : ℝ) (z : ℂ) (h0 : 0 < d0)
    (hdet : Complex.normSq z ≤ d0*d1) :
    Matrix.PosSemidef (!![(d0:ℂ),z;starRingEnd ℂ z,(d1:ℂ)]) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · intro x
    rw [Complex.nonneg_iff]
    have hs := Complex.normSq_nonneg ((d0:ℂ)*x 0+z*x 1)
    have hn := Complex.normSq_nonneg (x 1)
    have hp := mul_nonneg (sub_nonneg.mpr hdet) hn
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_two,Pi.star_apply,Complex.star_def]
    constructor
    · change 0 ≤ (starRingEnd ℂ (x 0)*((d0:ℂ)*x 0+z*x 1)+
        starRingEnd ℂ (x 1)*(starRingEnd ℂ z*x 0+(d1:ℂ)*x 1)).re
      simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
        Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
        sub_zero,add_zero]
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
        Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
        sub_zero,add_zero] at hs hn hp
      apply nonneg_of_mul_nonneg_left (b := d0) ?_ h0
      nlinarith only [hs,hp]
    · change 0 = (starRingEnd ℂ (x 0)*((d0:ℂ)*x 0+z*x 1)+
        starRingEnd ℂ (x 1)*(starRingEnd ℂ z*x 0+(d1:ℂ)*x 1)).im
      simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.add_im,
        Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
      ring

#print axioms cubic_ratio_comparison
#print axioms tilted_ratio_comparison
#print axioms real_two_width_determinant
#print axioms two_width_determinant
#print axioms two_by_two_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthCoercivity
