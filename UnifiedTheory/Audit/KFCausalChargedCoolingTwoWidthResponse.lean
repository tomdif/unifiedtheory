/- Two-width field absorption. The unrestricted-width response estimate is not asserted. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthCoercivity
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthNormalization
import UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthResponse
noncomputable section
open scoped ComplexOrder
open KFCausalChargedCoolingTwoWidthCoercivity KFCausalChargedCoolingTwoWidthNormalization
open KFCausalChargedCoolingWidthPositive KFCausalChargedCoolingFixedV KFCausalChargedCoolingDerivative
open KFCausalPositiveKernelExponential KFCausalChargedCoolingGramIntegral
open KFCausalChargedFourierGaussianMoments (density density_expansion)
open MeasureTheory Matrix

def fieldWeight (x : ℝ) : ℝ := 1+x^2/2+x^4/4
def fieldGradient (x : ℝ) : ℝ := x+x^3

theorem field_weight_positive (x : ℝ) : 0 < fieldWeight x := by
  unfold fieldWeight
  positivity

theorem field_gradient_bound (x : ℝ) : (fieldGradient x)^2 ≤ 4*(fieldWeight x)^2 := by
  have h1 : (fieldGradient x)^2 ≤ 4*x^2*fieldWeight x := by
    unfold fieldGradient fieldWeight
    nlinarith [sq_nonneg x]
  have h2 : x^2 ≤ fieldWeight x := by
    unfold fieldWeight
    nlinarith [sq_nonneg (x^2-1)]
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 4*fieldWeight x by
    exact mul_nonneg (by norm_num) (field_weight_positive x).le)
  nlinarith only [h1,h3]

theorem weighted_scalar_absorption (c v s x : ℝ) (hc : 0 < c) :
    -(s^2/c)*fieldWeight x ≤ c*v^2*fieldWeight x+s*v*fieldGradient x := by
  have hW := field_weight_positive x
  have hg := field_gradient_bound x
  have hs := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hg)
  have hq := sq_nonneg (2*c*v*fieldWeight x+s*fieldGradient x)
  have he : 0 ≤ (c*v^2*fieldWeight x+s*v*fieldGradient x+(s^2/c)*fieldWeight x)*
      (4*c*fieldWeight x) := by
    field_simp
    nlinarith only [hs,hq]
  have hpos : 0 < 4*c*fieldWeight x := by positivity
  have := nonneg_of_mul_nonneg_left he hpos
  linarith

theorem scalar_form_absorption (a c v s x E M : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hE : 0 ≤ E) (hM : c*E ≤ M) :
    -(s^2/(a*c))*fieldWeight x*E ≤
      a*v^2*fieldWeight x*M+s*v*fieldGradient x*E := by
  have hW := field_weight_positive x
  have h1 := mul_le_mul_of_nonneg_right (weighted_scalar_absorption (a*c) v s x
    (mul_pos ha hc)) hE
  have h2 := mul_le_mul_of_nonneg_left hM
    (show 0 ≤ a*v^2*fieldWeight x by positivity)
  nlinarith only [h1,h2]

theorem actual_residual_determinant (α : ℝ) (r : ℂ) (m u : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hm : 0 < m) (hu : 1 ≤ u) :
    Complex.normSq (residual α r m m (m*u^2)) ≤
      (α*r.re*m*(7/4)*diagonalScale (α*(r.re^2-r.im^2)*m))*
      (α*r.re*m*(2*u^2-1/4)*(diagonalScale (α*(r.re^2-r.im^2)*m)/u^3)) := by
  have ha := (actual_parameters_positive r hr).1
  have hA := (actual_parameters_positive r hr).2
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hs : 0 < α*(r.re^2-r.im^2)*m := by positivity
  have hd := normalizedDistance_positive α r m u hα hr hm hu0
  have hn : 0 < ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖ := by
    unfold normalizedDistance at hd
    exact (mul_pos_iff_of_pos_left (by norm_num : (0:ℝ)<2)).mp
      ((div_pos_iff_of_pos_right hs).mp hd)
  have h := two_width_determinant u (r.im/r.re) (normalizedDistance α r m u) hu hd
    (normalizedDistance_lower α r m u hα hr hm)
  have he : normalizedDistance α r m u ^ 3 * (α*(r.re^2-r.im^2)*m)^3 =
      8*‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖^3 := by
    unfold normalizedDistance
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_right h (pow_nonneg hs.le 3)
  rw [mul_assoc ((7/4)*(2*u^2-1/4)),he] at hmul
  have hratio :
      ((u^2+3/4)^2+(r.im/r.re)^2*(u^2-1)^2)/
          ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖^3 ≤
      ((7/4)*(2*u^2-1/4))/((α*(r.re^2-r.im^2)*m)^3*u^3) := by
    apply (div_le_div_iff₀ (pow_pos hn 3) (mul_pos (pow_pos hs 3) (pow_pos hu0 3))).mpr
    nlinarith only [hmul]
  rw [residual_off_normSq α r m u ha.ne']
  calc
    _ = (α*r.re*m)^2 *
        (((u^2+3/4)^2+(r.im/r.re)^2*(u^2-1)^2)/
          ‖widthSum ((α:ℂ)*r^2/2) m (m*u^2)‖^3) := by ring
    _ ≤ (α*r.re*m)^2 *
        (((7/4)*(2*u^2-1/4))/((α*(r.re^2-r.im^2)*m)^3*u^3)) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ = _ := by
      rw [show (α*r.re*m*(7/4)*diagonalScale (α*(r.re^2-r.im^2)*m))*
          (α*r.re*m*(2*u^2-1/4)*(diagonalScale (α*(r.re^2-r.im^2)*m)/u^3)) =
          (α*r.re*m)^2*((7/4)*(2*u^2-1/4))*
            diagonalScale (α*(r.re^2-r.im^2)*m)^2/u^3 by ring,
        diagonalScale_sq _ hs.le]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring

theorem actual_parameterized_coercivity (α : ℝ) (r : ℂ) (m u : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hm : 0 < m) (hu : 1 ≤ u) :
    Matrix.PosSemidef (fun i j : Fin 2 => residual α r m (![m,m*u^2] i) (![m,m*u^2] j)) := by
  have ha := (actual_parameters_positive r hr).1
  have hA := (actual_parameters_positive r hr).2
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hs : 0 < α*(r.re^2-r.im^2)*m := by positivity
  have hk := diagonalScale_positive _ hs
  have hM := two_by_two_positive
    (α*r.re*m*(7/4)*diagonalScale (α*(r.re^2-r.im^2)*m))
    (α*r.re*m*(2*u^2-1/4)*(diagonalScale (α*(r.re^2-r.im^2)*m)/u^3))
    (residual α r m m (m*u^2)) (by positivity)
    (actual_residual_determinant α r m u hα hr hm hu)
  convert hM using 1
  ext i j
  fin_cases i <;> fin_cases j
  · change residual α r m m m =
      (α*r.re*m*(7/4)*diagonalScale (α*(r.re^2-r.im^2)*m):ℝ)
    rw [residual_diagonal α r m m hs.le]
    push_cast
    ring
  · rfl
  · exact residual_conjugate α r m m (m*u^2) hα hr hm (by positivity)
  · change residual α r m (m*u^2) (m*u^2) =
      (α*r.re*m*(2*u^2-1/4)*(diagonalScale (α*(r.re^2-r.im^2)*m)/u^3):ℝ)
    rw [residual_diagonal α r m (m*u^2) (by positivity),
      show α*(r.re^2-r.im^2)*(m*u^2)=(α*(r.re^2-r.im^2)*m)*u^2 by ring,
      diagonalScale_mul_sq _ _ hs.le hu0.le]
    push_cast
    ring

theorem actual_ordered_coercivity (α : ℝ) (r : ℂ) (w z : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : 0 < w) (hwz : w ≤ z) :
    Matrix.PosSemidef (fun i j : Fin 2 => residual α r w (![w,z] i) (![w,z] j)) := by
  have hz : 0 < z := hw.trans_le hwz
  have hu : 1 ≤ Real.sqrt (z/w) := Real.one_le_sqrt.mpr ((le_div_iff₀ hw).mpr (by linarith))
  have he : w*(Real.sqrt (z/w))^2 = z := by
    rw [Real.sq_sqrt (div_pos hz hw).le]
    field_simp
  simpa only [he] using actual_parameterized_coercivity α r w (Real.sqrt (z/w)) hα hr hw hu

theorem actual_two_width_coercivity (α : ℝ) (r : ℂ) (w : Fin 2 → ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => residual α r (min (w 0) (w 1)) (w i) (w j)) := by
  rcases le_total (w 0) (w 1) with h | h
  · have hp := actual_ordered_coercivity α r (w 0) (w 1) hα hr (hw 0) h
    convert hp using 1
    ext i j
    rw [min_eq_left h]
    fin_cases i <;> fin_cases j <;> rfl
  · have hp := (actual_ordered_coercivity α r (w 1) (w 0) hα hr (hw 1) h).submatrix
      (fun i : Fin 2 => 1-i)
    convert hp using 1
    ext i j
    rw [min_eq_right h]
    fin_cases i <;> fin_cases j <;> rfl

theorem fixed_v_coercivity (α : ℝ) (r : ℂ) (w : Fin 2 → ℝ) (v : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j =>
      Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w i) (w j)*(v^2:ℝ))*
        coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j) -
      (α*r.re*min (w 0) (w 1)/4:ℝ)*kernel ((α:ℂ)*r^2/2) (w i) (w j) v) := by
  have hp := schur_positive (gaussian_width_positive ((α:ℂ)*r^2/2) (v^2) w)
    (actual_two_width_coercivity α r w hα hr hw)
  convert hp using 1
  ext i j
  simp only [KFCausalChargedCoolingTwoWidthNormalization.residual,kernel,
    zero_pow (by decide : (2:ℕ) ≠ 0),Complex.ofReal_zero,
    mul_zero,Complex.exp_zero]
  ring

theorem fixed_v_kernel_positive {n : Type*} [Fintype n] (p : ℂ) (hp : 0 < p.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Matrix.PosSemidef (fun i j => kernel p (w i) (w j) v) := by
  have hS (i j : n) : 0 < (widthSum p (w i) (w j)).re := by
    rw [widthSum_re]
    exact mul_pos hp (add_pos (hw i) (hw j))
  have hT (i j : n) : 0 < (widthSum (starRingEnd ℂ p) (w i) (w j)).re := by
    rw [widthSum_re,Complex.conj_re]
    exact mul_pos hp (add_pos (hw i) (hw j))
  have hpos (q : ℝ × ℝ) : Matrix.PosSemidef (fun i j =>
      density (widthSum p (w i) (w j)) (widthSum (starRingEnd ℂ p) (w i) (w j)) 0 0 q.1 v q.2) := by
    have h := schur_positive (gaussian_width_positive p (q.1^2+v^2) w)
      (gaussian_width_positive (starRingEnd ℂ p) q.2 w)
    convert h using 1
    ext i j
    rw [density_expansion]
    simp only [pow_zero,zero_mul,add_zero,one_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h := integral_positive planeMeasure
    (fun q i j => density (widthSum p (w i) (w j))
      (widthSum (starRingEnd ℂ p) (w i) (w j)) 0 0 q.1 v q.2) hpos
    (fun i j => fixed_density_integrable _ _ _ (hS i j) (hT i j) 0 v)
  have hs := h.smul (inv_nonneg.mpr (Real.sqrt_nonneg Real.pi))
  convert hs using 1
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul]
  rw [fixed_density_integral _ _ _ (hS i j) (hT i j)]
  simp only [pow_zero,zero_mul,add_zero,Complex.ofReal_inv,kernel,Complex.ofReal_pow]
  field_simp

theorem fixed_v_coercivity_pullback {n : Type*} (α : ℝ) (r : ℂ)
    (w : Fin 2 → ℝ) (label : n → Fin 2) (v : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j =>
      Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w (label i)) (w (label j))*(v^2:ℝ))*
        coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w (label i)) (w (label j)) -
      (α*r.re*min (w 0) (w 1)/4:ℝ)*
        kernel ((α:ℂ)*r^2/2) (w (label i)) (w (label j)) v) :=
  (fixed_v_coercivity α r w v hα hr hw).submatrix label

theorem two_width_field_absorption (α : ℝ) (r : ℂ) (w : Fin 2 → ℝ) (v s x : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) (f : Fin 2 → ℂ) :
    -(4*s^2/(α*r.re^2*min (w 0) (w 1)))*fieldWeight x*
        (form ((α:ℂ)*r^2/2) w v f).re ≤
      r.re*v^2*fieldWeight x*
        (star f ⬝ᵥ ((fun i j =>
          Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w i) (w j)*(v^2:ℝ))*
          coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)) *ᵥ f)).re+
        s*v*fieldGradient x*(form ((α:ℂ)*r^2/2) w v f).re := by
  have ha := (actual_parameters_positive r hr).1
  have hm : 0 < min (w 0) (w 1) := lt_min (hw 0) (hw 1)
  have hE := (fixed_v_kernel_positive ((α:ℂ)*r^2/2)
    (actual_gamma_re_positive α r hα hr) w hw v).dotProduct_mulVec_nonneg f |>.1
  have hM := (fixed_v_coercivity α r w v hα hr hw).dotProduct_mulVec_nonneg f |>.1
  have he :
      (star f ⬝ᵥ ((fun i j =>
        Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w i) (w j)*(v^2:ℝ))*
          coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)-
        (α*r.re*min (w 0) (w 1)/4:ℝ)*kernel ((α:ℂ)*r^2/2) (w i) (w j) v) *ᵥ f)).re =
      (star f ⬝ᵥ ((fun i j =>
        Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w i) (w j)*(v^2:ℝ))*
          coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)) *ᵥ f)).re-
      (α*r.re*min (w 0) (w 1)/4)*(form ((α:ℂ)*r^2/2) w v f).re := by
    rw [show (α*r.re*min (w 0) (w 1)/4)*(form ((α:ℂ)*r^2/2) w v f).re =
      ((α*r.re*min (w 0) (w 1)/4:ℝ)*(form ((α:ℂ)*r^2/2) w v f)).re by simp,
      ← Complex.sub_re]
    congr 1
    simp only [form,dotProduct,Matrix.mulVec,Fin.sum_univ_two,Pi.star_apply]
    ring
  rw [he] at hM
  simp only [Complex.zero_re] at hE hM
  have h := scalar_form_absorption r.re (α*r.re*min (w 0) (w 1)/4) v s x
    (form ((α:ℂ)*r^2/2) w v f).re
    (star f ⬝ᵥ ((fun i j =>
      Complex.exp (-widthSum ((α:ℂ)*r^2/2) (w i) (w j)*(v^2:ℝ))*
        coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)) *ᵥ f)).re
    ha (by positivity) hE (by linarith only [hM])
  convert h using 1
  congr 2
  field_simp

#print axioms field_weight_positive
#print axioms field_gradient_bound
#print axioms weighted_scalar_absorption
#print axioms scalar_form_absorption
#print axioms actual_residual_determinant
#print axioms actual_parameterized_coercivity
#print axioms actual_ordered_coercivity
#print axioms actual_two_width_coercivity
#print axioms fixed_v_coercivity
#print axioms fixed_v_kernel_positive
#print axioms fixed_v_coercivity_pullback
#print axioms two_width_field_absorption
end
end UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthResponse
