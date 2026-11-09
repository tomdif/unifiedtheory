/- Uniform polynomial bounds for the first Gaussian shear coefficient
and its derivative. The neutral component is included explicitly. -/
import UnifiedTheory.Audit.KFCausalGaussianFourthMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction slope)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalShearRadius

def productConstant (M : ℝ) : ℝ := M^2+2*M+8*M*(M+1)
def slopeConstant (M α β : ℝ) (b : Fin 5 → ℂ) : ℝ :=
  ∑ i, (2*M*‖b i‖+2*|widths α β i| *productConstant M)

theorem productConstant_nonnegative (M : ℝ) (hM : 0 ≤ M) : 0 ≤ productConstant M := by
  unfold productConstant
  positivity

theorem slopeConstant_nonnegative (M α β : ℝ) (hM : 0 ≤ M) (b : Fin 5 → ℂ) :
    0 ≤ slopeConstant M α β b := by
  unfold slopeConstant
  apply Finset.sum_nonneg
  intro i _
  have hp := productConstant_nonnegative M hM
  positivity

theorem direction_bound (r : ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ‖r‖ ≤ M)
    (q : Transverse) (i : Fin 5) : ‖direction r q i‖ ≤ 2*M*radius q := by
  have hR := (radius_positive q).le
  by_cases hi : i=4
  · subst i
    have hm : ‖(q 2:ℂ)+(q 3:ℂ)‖ ≤ 2*radius q := by
      simpa only [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs] using mix_abs_le q
    simp only [direction,ite_true,norm_mul]
    have hh := mul_le_mul hr hm (norm_nonneg _) hM
    nlinarith
  · simp only [direction,if_neg hi,norm_div,norm_mul,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul hr (coordinate_abs_le q i) (abs_nonneg _) hM
    nlinarith [mul_nonneg hM hR]

theorem direction_square_bound (r : ℂ) (M : ℝ) (_hM : 0 ≤ M) (hr : ‖r‖ ≤ M)
    (q : Transverse) (i : Fin 5) : ‖direction r q i‖^2 ≤ 4*M^2*radius q := by
  have hr2 := pow_le_pow_left₀ (norm_nonneg r) hr 2
  have hR := (radius_positive q).le
  by_cases hi : i=4
  · subst i
    have hm : ‖(q 2:ℂ)+(q 3:ℂ)‖^2 ≤ 4*radius q := by
      simpa only [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,sq_abs] using mix_square_le q
    simp only [direction,ite_true,norm_mul,mul_pow]
    have hh := mul_le_mul hr2 hm (sq_nonneg _) (sq_nonneg M)
    nlinarith
  · simp only [direction,if_neg hi,norm_div,norm_mul,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs,div_pow,mul_pow,sq_abs]
    have hh := mul_le_mul hr2 (coordinate_square_le q i) (sq_nonneg _) (sq_nonneg M)
    nlinarith [mul_nonneg (sq_nonneg M) hR]

theorem position_direction_bound (r : ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ‖r‖ ≤ M)
    (q : Transverse) (i : Fin 5) :
    ‖position r q i*direction r q i‖ ≤ productConstant M*radius q := by
  have hR := (radius_positive q).le
  have hr2 := pow_le_pow_left₀ (norm_nonneg r) hr 2
  have hc : M^2 ≤ productConstant M := by
    unfold productConstant
    nlinarith [mul_nonneg hM (by linarith : 0 ≤ M+1)]
  by_cases hi : i=4
  · subst i
    have hm : ‖((q 2:ℂ)+(q 3:ℂ))^2‖ ≤ 4*radius q := by
      simpa only [norm_pow,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,sq_abs] using mix_square_le q
    have hn : ‖(q 4:ℂ)*((q 2:ℂ)+(q 3:ℂ))‖ ≤ 2*radius q := by
      simpa only [← Complex.ofReal_add,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs] using neutral_mix_le q
    have hd : ‖r-1‖ ≤ M+1 := (norm_sub_le r 1).trans (by simpa using add_le_add_right hr 1)
    have he : position r q 4*direction r q 4 =
        r*((q 4:ℂ)*((q 2:ℂ)+(q 3:ℂ)))+
          2*r*(r-1)*((q 2:ℂ)+(q 3:ℂ))^2 := by simp [position,direction]; ring
    rw [he]
    apply (norm_add_le _ _).trans
    have h1 := mul_le_mul hr hn (norm_nonneg _) hM
    have h2 := mul_le_mul (mul_le_mul hr hd (norm_nonneg _) hM) hm (norm_nonneg _) (by positivity : 0 ≤ M*(M+1))
    simp only [norm_mul] at h1
    simp only [norm_mul,Complex.norm_ofNat]
    unfold productConstant
    nlinarith [mul_nonneg (sq_nonneg M) hR]
  · simp only [position,direction,if_neg hi,norm_mul,norm_div,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul hr2 (coordinate_square_le q i) (sq_nonneg _) (sq_nonneg M)
    have hcp := mul_le_mul_of_nonneg_right hc hR
    nlinarith [sq_abs (q i),mul_nonneg (sq_nonneg M) hR]

theorem slope_bound (r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ∀ s, ‖r s‖ ≤ M)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    ‖KFCausalRelativeGaussianDifferential.slope r α β b x‖ ≤ slopeConstant M α β b*radius x.2 := by
  unfold KFCausalRelativeGaussianDifferential.slope
  apply (norm_sum_le _ _).trans
  rw [slopeConstant,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have he : (b i-2*(widths α β i:ℂ)*position (r x.1) x.2 i)*direction (r x.1) x.2 i =
      b i*direction (r x.1) x.2 i-2*(widths α β i:ℂ)*(position (r x.1) x.2 i*direction (r x.1) x.2 i) := by ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have h1 := mul_le_mul_of_nonneg_left (direction_bound _ M hM (hr x.1) x.2 i) (norm_nonneg (b i))
  have h2 := mul_le_mul_of_nonneg_left (position_direction_bound _ M hM (hr x.1) x.2 i)
    (show 0 ≤ 2*|widths α β i| by positivity)
  simp only [norm_mul] at h2
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
  nlinarith

#print axioms productConstant_nonnegative
#print axioms slopeConstant_nonnegative
#print axioms direction_bound
#print axioms direction_square_bound
#print axioms position_direction_bound
#print axioms slope_bound
end
end UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds
