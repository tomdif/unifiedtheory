/- Three actual positive charged widths obstruct extending the two-width
pointwise constant. This is not a counterexample to the integrated response. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingThreeWidthObstruction
noncomputable section
open scoped ComplexOrder
open KFCausalChargedCoolingWidthPositive KFCausalChargedCoolingDerivative
open KFCausalChargedCoolingTwoWidthNormalization
open Matrix

def testWidth : Fin 3 → ℝ := ![1,21/20,11/10]
def testCoefficient : Fin 3 → ℂ := ![1,-2,1]
def radicalResidual (t : ℝ) : ℝ := (2*t-1/4)/(Real.sqrt t*t)

theorem widths_admissible (i : Fin 3) : 1 ≤ testWidth i := by
  fin_cases i <;> norm_num [testWidth]

theorem real_kernel_identity (w z : ℝ) (hs : 0 ≤ (w+z)/2) :
    kernel (1/2:ℂ) w z 0 = (diagonalScale ((w+z)/2):ℂ) := by
  have hS : widthSum (1/2:ℂ) w z = ((w+z)/2:ℝ) := by
    simp [widthSum,Complex.conj_ofNat]
    ring
  simp only [kernel,zero_pow (by decide : (2:ℕ) ≠ 0),Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,widthSum_conjugate,hS,Complex.conj_ofReal]
  have hc : ((w+z)/2:ℝ)^(1/2:ℂ) = (Real.sqrt ((w+z)/2):ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hs]
    norm_num
  rw [hc]
  simp [diagonalScale]

theorem real_residual_identity (w z : ℝ) (hs : 0 ≤ (w+z)/2) :
    residual 1 (1:ℂ) 1 w z = (radicalResidual ((w+z)/2):ℂ) := by
  rw [residual_factor,actual_slopeSum]
  norm_num
  rw [real_kernel_identity w z hs]
  unfold diagonalScale radicalResidual
  push_cast
  ring

theorem radical_residual_bounds (t l u : ℝ) (ht : 1/8 ≤ t) (hl : 0 < l)
    (hu : 0 < u) (hl2 : l^2 ≤ t) (hu2 : t ≤ u^2) :
    (2*t-1/4)/(u*t) ≤ radicalResidual t ∧
      radicalResidual t ≤ (2*t-1/4)/(l*t) := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hlo : l ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hl2
  have hup : Real.sqrt t ≤ u := (Real.sqrt_le_left hu.le).mpr hu2
  have hn : 0 ≤ 2*t-1/4 := by linarith
  unfold radicalResidual
  constructor
  · exact div_le_div_of_nonneg_left hn (mul_pos hs ht0)
      (mul_le_mul_of_nonneg_right hup ht0.le)
  · exact div_le_div_of_nonneg_left hn (mul_pos hl ht0)
      (mul_le_mul_of_nonneg_right hlo ht0.le)

theorem explicit_radical_sum_negative :
    radicalResidual 1-4*radicalResidual (41/40)+6*radicalResidual (21/20)-
      4*radicalResidual (43/40)+radicalResidual (11/10) < 0 := by
  have h1 := radical_residual_bounds (41/40) (2024845673/2000000000)
    (5062114183/5000000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h2 := radical_residual_bounds (21/20) (2049390153/2000000000)
    (5123475383/5000000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h3 := radical_residual_bounds (43/40) (2592055169/2500000000)
    (10368220677/10000000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h4 := radical_residual_bounds (11/10) (10488088481/10000000000)
    (5244044241/5000000000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have he : radicalResidual 1 = 7/4 := by norm_num [radicalResidual]
  norm_num at h1 h2 h3 h4
  rw [he]
  linarith only [h1.1,h2.2,h3.1,h4.2]

theorem actual_three_width_form_negative :
    (star testCoefficient ⬝ᵥ ((fun i j => residual 1 (1:ℂ) 1 (testWidth i) (testWidth j))
      *ᵥ testCoefficient)).re < 0 := by
  have hentry (i j : Fin 3) : residual 1 (1:ℂ) 1 (testWidth i) (testWidth j) =
      (radicalResidual ((testWidth i+testWidth j)/2):ℂ) :=
    real_residual_identity _ _ (by linarith [widths_admissible i,widths_admissible j])
  simp_rw [hentry]
  simp [dotProduct,Matrix.mulVec,Fin.sum_univ_succ,testWidth,testCoefficient,
    Complex.add_re,Complex.mul_re]
  norm_num
  linarith only [explicit_radical_sum_negative]

theorem actual_three_width_not_coercive :
    ¬ Matrix.PosSemidef (fun i j : Fin 3 =>
      residual 1 (1:ℂ) 1 (testWidth i) (testWidth j)) := by
  intro h
  have hn := (h.dotProduct_mulVec_nonneg testCoefficient).1
  exact (not_lt_of_ge hn) actual_three_width_form_negative

#print axioms widths_admissible
#print axioms real_kernel_identity
#print axioms real_residual_identity
#print axioms radical_residual_bounds
#print axioms explicit_radical_sum_negative
#print axioms actual_three_width_form_negative
#print axioms actual_three_width_not_coercive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingThreeWidthObstruction
