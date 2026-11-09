/- The full fixed-v charged cooling kernel is positive, including every width cross term. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingWidthPositive
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingFixedV
noncomputable section
open MeasureTheory Set Matrix
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingWidthPositive KFCausalPositiveKernelExponential
open KFCausalChargedCoolingActualPhase

variable {n : Type*} [Fintype n]

theorem widthSum_re (p : ℂ) (w z : ℝ) : (widthSum p w z).re = p.re*(w+z) := by
  simp [widthSum,Complex.mul_re]
  ring

theorem gaussian_width_positive (p : ℂ) (t : ℝ) (w : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (-widthSum p (w i) (w j)*(t:ℂ))) := by
  have he (i j : n) : starRingEnd ℂ (Complex.exp (-starRingEnd ℂ p*(w i:ℂ)*(t:ℂ)))*
      Complex.exp (-starRingEnd ℂ p*(w j:ℂ)*(t:ℂ)) =
      Complex.exp (-widthSum p (w i) (w j)*(t:ℂ)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul,map_neg,Complex.conj_conj,Complex.conj_ofReal,← Complex.exp_add]
    unfold widthSum
    congr 1
    ring
  simpa only [Matrix.vecMulVec,Pi.star_apply,Complex.star_def,he] using
    Matrix.posSemidef_vecMulVec_star_self
      (fun i => Complex.exp (-starRingEnd ℂ p*(w i:ℂ)*(t:ℂ)))

theorem inverse_width_positive (p : ℂ) (hp : 0 < p.re) (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => (widthSum p (w i) (w j))⁻¹) := by
  have hr (i j : n) : (-widthSum p (w i) (w j)).re < 0 := by
    rw [Complex.neg_re,widthSum_re]
    exact neg_neg_of_pos (mul_pos hp (add_pos (hw i) (hw j)))
  have hi (i j : n) := integrableOn_exp_mul_complex_Ioi (hr i j) 0
  have h := integral_positive (volume.restrict (Ioi (0:ℝ)))
    (fun t i j => Complex.exp (-widthSum p (w i) (w j)*(t:ℂ)))
    (fun t => gaussian_width_positive p t w) hi
  convert h using 1
  ext i j
  rw [integral_exp_mul_complex_Ioi (hr i j) 0]
  simp

theorem actual_gamma_re_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re) :
    0 < ((α:ℂ)*r^2/2).re := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
  have hs : 0 < r.re^2-r.im^2 := by
    nlinarith [sq_abs r.im,mul_pos (sub_pos.mpr hr)
      (add_pos_of_pos_of_nonneg ha (abs_nonneg r.im))]
  have he : ((α:ℂ)*r^2/2).re = α*(r.re^2-r.im^2)/2 := by
    simp [pow_two,Complex.mul_re]
  rw [he]
  positivity

def dissipation (p q : ℂ) (w z v : ℝ) : ℂ :=
  Complex.exp (-widthSum p w z*(v^2:ℝ))*
    ((v^2:ℝ)*coolingB p q w z+coolingB p q w z/(2*widthSum p w z)+coolingC p q w z)

theorem actual_dissipation_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Matrix.PosSemidef (fun i j => dissipation ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j) v) := by
  have hB := actual_coolingB_positive α r hα hr w hw
  have hC := actual_coolingC_positive α r hα hr w hw
  have hS := inverse_width_positive ((α:ℂ)*r^2/2) (actual_gamma_re_positive α r hα hr) w hw
  have hD := ((hB.smul (sq_nonneg v)).add
    ((schur_positive hB hS).smul (by norm_num : (0:ℝ) ≤ 1/2))).add hC
  have h := schur_positive (gaussian_width_positive ((α:ℂ)*r^2/2) (v^2) w) hD
  convert h using 1
  ext i j
  simp only [dissipation,Matrix.smul_apply,Matrix.add_apply,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

theorem actual_dissipation_form_nonnegative (α : ℝ) (r : ℂ) (hα : 0 < α)
    (hr : |r.im| < r.re) (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    0 ≤ (star c ⬝ᵥ ((fun i j => dissipation ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j) v) *ᵥ c)).re := by
  exact (actual_dissipation_positive α r hα hr w hw v).dotProduct_mulVec_nonneg c |>.1

#print axioms widthSum_re
#print axioms gaussian_width_positive
#print axioms inverse_width_positive
#print axioms actual_gamma_re_positive
#print axioms actual_dissipation_positive
#print axioms actual_dissipation_form_nonnegative
end
end UnifiedTheory.Audit.KFCausalChargedCoolingFixedV
