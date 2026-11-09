/- An exact positive remainder in the charged marginal score identity.
All kernels retain the coherent width labels. This supplies a score
inequality, not the unresolved mixed-source response discriminant. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingMarginalDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingBoundaryScore
noncomputable section
open MeasureTheory Matrix
open scoped ComplexConjugate ComplexOrder Topology
open KFCausalChargedCoolingWidthPositive
open KFCausalChargedCoolingFixedV
open KFCausalChargedCoolingDerivative (kernel form)
open KFCausalChargedCoolingGramIntegral (gaussianValue_split)
open KFCausalPositiveKernelExponential (schur_positive integral_positive)
open KFCausalReciprocalWedgeGeometry (gamma)

def baseKernel (p : ℂ) (w z : ℝ) : ℂ :=
  1/(widthSum p w z^(1/2:ℂ)*widthSum (conj p) w z)

def scoreRate (r : ℂ) : ℝ :=
  (3*r.re^2-r.im^2)/(2*r.re*(r.re^2-r.im^2))

def boundaryRate (r : ℂ) : ℝ :=
  (r.re^2+r.im^2)/(2*r.re*(r.re^2-r.im^2))

def boundaryKernel (p : ℂ) (w z v : ℝ) : ℂ :=
  Complex.exp (-widthSum p w z*(v^2:ℝ))*
    ((v^2:ℝ)+1/(2*widthSum p w z))/(widthSum p w z)^(1/2:ℂ)

def radialSlope (p : ℂ) (w z v : ℝ) : ℂ :=
  -2*(v:ℂ)*widthSum p w z*kernel p w z v

private theorem width_ne (p : ℂ) (hp : 0 < p.re) (w z : ℝ)
    (hw : 0 < w) (hz : 0 < z) : widthSum p w z ≠ 0 := by
  have h : 0 < (widthSum p w z).re := by
    rw [widthSum_re]
    exact mul_pos hp (add_pos hw hz)
  intro he
  rw [he] at h
  exact lt_irrefl _ h

private theorem area_pos (r : ℂ) (hr : |r.im| < r.re) :
    0 < r.re^2-r.im^2 := by
  have ha := lt_of_le_of_lt (abs_nonneg r.im) hr
  nlinarith [sq_abs r.im, mul_pos (sub_pos.mpr hr)
    (add_pos_of_pos_of_nonneg ha (abs_nonneg r.im))]

theorem coolingC_remainder_identity (α : ℝ) (r : ℂ) (hα : 0 < α)
    (hr : |r.im| < r.re) (w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
    coolingC (gamma α r) ((α:ℂ)*r) w z-baseKernel (gamma α r) w z/(r.re:ℂ) =
      ((r.re^2+r.im^2)/(4*r.re^2):ℝ)*
        (coolingC (gamma α r) ((α:ℂ)*r) w z+
          coolingB (gamma α r) ((α:ℂ)*r) w z/widthSum (conj (gamma α r)) w z) := by
  have ha : r.re ≠ 0 := ne_of_gt (lt_of_le_of_lt (abs_nonneg _) hr)
  have hac : (r.re:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hp := actual_gamma_re_positive α r hα hr
  change 0 < (gamma α r).re at hp
  have hS := width_ne (gamma α r) hp w z hw hz
  have hT := width_ne (conj (gamma α r)) (by simpa only [Complex.conj_re] using hp) w z hw hz
  have hH : widthSum (gamma α r) w z^(1/2:ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hS)
  have he : 4*(r.re:ℂ)^2*widthSum (conj ((α:ℂ)*r)) w z-
      4*(r.re:ℂ)*widthSum (conj (gamma α r)) w z =
      ((r.re:ℂ)^2+(r.im:ℂ)^2)*
        (widthSum (conj ((α:ℂ)*r)) w z+widthSum ((α:ℂ)*r) w z) := by
    simp only [widthSum,gamma,map_mul,map_pow,map_div₀,Complex.conj_ofReal,
      Complex.conj_ofNat,Complex.conj_conj]
    apply Complex.ext <;>
      simp [Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  unfold coolingC coolingB baseKernel
  push_cast
  field_simp [hH,hT,hac]
  linear_combination he

theorem coolingC_remainder_positive {n : Type*} [Fintype n]
    (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => coolingC (gamma α r) ((α:ℂ)*r) (w i) (w j)-
      baseKernel (gamma α r) (w i) (w j)/(r.re:ℂ)) := by
  have hB := actual_coolingB_positive α r hα hr w hw
  have hC := actual_coolingC_positive α r hα hr w hw
  have hp := actual_gamma_re_positive α r hα hr
  change 0 < (gamma α r).re at hp
  have hT := inverse_width_positive (conj (gamma α r))
    (by simpa only [Complex.conj_re] using hp) w hw
  have h := (hC.add (schur_positive hB hT)).smul
    (show 0 ≤ (r.re^2+r.im^2)/(4*r.re^2) by positivity)
  convert h using 1
  ext i j
  rw [coolingC_remainder_identity α r hα hr _ _ (hw i) (hw j)]
  simp only [Matrix.smul_apply,Matrix.add_apply,Complex.real_smul,div_eq_mul_inv,gamma]

theorem boundaryKernel_integral (p : ℂ) (hp : 0 < p.re)
    (w z v : ℝ) (hw : 0 < w) (hz : 0 < z) :
    (∫ u : ℝ, ((u^2+v^2:ℝ):ℂ)*
      Complex.exp (-widthSum p w z*((u^2+v^2:ℝ):ℂ))) =
      (Real.sqrt Real.pi:ℂ)*boundaryKernel p w z v := by
  have hS : 0 < (widthSum p w z).re := by
    rw [widthSum_re]
    exact mul_pos hp (add_pos hw hz)
  have h0 := KFCausalComplexGaussianMoments.moment_integrable _ hS 0
  have h2 := KFCausalComplexGaussianMoments.moment_integrable _ hS 2
  have he (u : ℝ) : ((u^2+v^2:ℝ):ℂ)*
      Complex.exp (-widthSum p w z*((u^2+v^2:ℝ):ℂ)) =
      (KFCausalComplexGaussianMoments.moment (widthSum p w z) 2 u+
        (v^2:ℝ)*KFCausalComplexGaussianMoments.moment (widthSum p w z) 0 u)*
        Complex.exp (-widthSum p w z*(v^2:ℝ)) := by
    simp only [KFCausalComplexGaussianMoments.moment,pow_zero,one_mul,
      Complex.ofReal_add,Complex.ofReal_pow,mul_add,Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_mul_const,integral_add h2 (h0.const_mul _),integral_const_mul]
  change (KFCausalComplexGaussianMoments.value (widthSum p w z) 2 +
    (v^2:ℝ)*KFCausalComplexGaussianMoments.value (widthSum p w z) 0)*_ = _
  rw [KFCausalComplexGaussianMoments.value_two _ hS,
    KFCausalComplexGaussianMoments.value_zero _ hS,gaussianValue_split _ hS]
  unfold boundaryKernel
  ring

theorem boundaryKernel_positive {n : Type*} [Fintype n]
    (p : ℂ) (hp : 0 < p.re) (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Matrix.PosSemidef (fun i j => boundaryKernel p (w i) (w j) v) := by
  have hi (i j : n) : Integrable (fun u : ℝ => ((u^2+v^2:ℝ):ℂ)*
      Complex.exp (-widthSum p (w i) (w j)*((u^2+v^2:ℝ):ℂ))) := by
    have hS : 0 < (widthSum p (w i) (w j)).re := by
      rw [widthSum_re]
      exact mul_pos hp (add_pos (hw i) (hw j))
    have h0 := KFCausalComplexGaussianMoments.moment_integrable _ hS 0
    have h2 := KFCausalComplexGaussianMoments.moment_integrable _ hS 2
    convert (h2.add (h0.const_mul ((v^2:ℝ):ℂ))).mul_const
      (Complex.exp (-widthSum p (w i) (w j)*(v^2:ℝ))) using 1
    funext u
    simp only [KFCausalComplexGaussianMoments.moment,pow_zero,one_mul,
      Complex.ofReal_add,Complex.ofReal_pow,mul_add,Complex.exp_add,Pi.add_apply]
    ring
  have h := integral_positive volume
    (fun u i j => ((u^2+v^2:ℝ):ℂ)*
      Complex.exp (-widthSum p (w i) (w j)*((u^2+v^2:ℝ):ℂ)))
    (fun u => by simpa only [Matrix.smul_apply,Complex.real_smul] using
      (gaussian_width_positive p (u^2+v^2) w).smul (add_nonneg (sq_nonneg u) (sq_nonneg v))) hi
  have h' := h.smul (show 0 ≤ (Real.sqrt Real.pi)⁻¹ by positivity)
  convert h' using 1
  ext i j
  rw [Matrix.smul_apply,boundaryKernel_integral p hp _ _ v (hw i) (hw j)]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))),one_mul]

private theorem width_slope (α : ℝ) (r : ℂ) (hr : |r.im| < r.re) (w z : ℝ) :
    widthSum ((α:ℂ)*r) w z =
      (scoreRate r:ℂ)*widthSum (gamma α r) w z+
      (boundaryRate r:ℂ)*widthSum (conj (gamma α r)) w z := by
  have ha : r.re ≠ 0 := ne_of_gt (lt_of_le_of_lt (abs_nonneg _) hr)
  have hA := ne_of_gt (area_pos r hr)
  simp only [widthSum,gamma,map_mul,map_pow,map_div₀,Complex.conj_ofReal,
    Complex.conj_ofNat,Complex.conj_conj]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]
  all_goals unfold scoreRate boundaryRate
  all_goals field_simp [ha,hA]
  all_goals ring

theorem score_kernel_identity (α : ℝ) (r : ℂ) (hα : 0 < α)
    (hr : |r.im| < r.re) (w z v : ℝ) (hw : 0 < w) (hz : 0 < z) :
    dissipation (gamma α r) ((α:ℂ)*r) w z v-
      ((scoreRate r/2+1/r.re:ℝ):ℂ)*kernel (gamma α r) w z v+
      ((scoreRate r/2:ℝ):ℂ)*(v:ℂ)*radialSlope (gamma α r) w z v =
      (boundaryRate r:ℂ)*boundaryKernel (gamma α r) w z v+
      Complex.exp (-widthSum (gamma α r) w z*(v^2:ℝ))*
        (coolingC (gamma α r) ((α:ℂ)*r) w z-baseKernel (gamma α r) w z/(r.re:ℂ)) := by
  have hp := actual_gamma_re_positive α r hα hr
  change 0 < (gamma α r).re at hp
  have hS := width_ne (gamma α r) hp w z hw hz
  have hT := width_ne (conj (gamma α r)) (by simpa only [Complex.conj_re] using hp) w z hw hz
  have he := width_slope α r hr w z
  unfold dissipation coolingB
  rw [he]
  unfold radialSlope kernel baseKernel boundaryKernel
  push_cast
  field_simp [hS,hT]
  ring

theorem score_kernel_positive {n : Type*} [Fintype n]
    (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Matrix.PosSemidef (fun i j =>
      dissipation (gamma α r) ((α:ℂ)*r) (w i) (w j) v-
      ((scoreRate r/2+1/r.re:ℝ):ℂ)*kernel (gamma α r) (w i) (w j) v+
      ((scoreRate r/2:ℝ):ℂ)*(v:ℂ)*radialSlope (gamma α r) (w i) (w j) v) := by
  have hp := actual_gamma_re_positive α r hα hr
  have hq : 0 ≤ boundaryRate r := by
    have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
    have hA := area_pos r hr
    unfold boundaryRate
    positivity
  have hB := (boundaryKernel_positive (gamma α r) hp w hw v).smul hq
  have hC := schur_positive (gaussian_width_positive (gamma α r) (v^2) w)
    (coolingC_remainder_positive α r hα hr w hw)
  convert hB.add hC using 1
  ext i j
  rw [score_kernel_identity α r hα hr _ _ v (hw i) (hw j)]
  simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]

theorem radial_kernel_derivative (p : ℂ) (w z v : ℝ) :
    HasDerivAt (fun t : ℝ => kernel p w z t) (radialSlope p w z v) v := by
  have hd := ((((hasDerivAt_id v).pow 2).ofReal_comp.const_mul
    (-widthSum p w z)).cexp).div_const
      (widthSum p w z^(1/2:ℂ)*widthSum (conj p) w z)
  convert hd using 1
  norm_num [radialSlope,kernel]
  ring

#print axioms coolingC_remainder_identity
#print axioms coolingC_remainder_positive
#print axioms boundaryKernel_integral
#print axioms boundaryKernel_positive
#print axioms score_kernel_identity
#print axioms score_kernel_positive
#print axioms radial_kernel_derivative
end
end UnifiedTheory.Audit.KFCausalChargedCoolingBoundaryScore
