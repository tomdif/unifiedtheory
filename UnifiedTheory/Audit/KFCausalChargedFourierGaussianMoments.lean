/- Exact charged Gaussian-Laplace moments for the full neutral Fourier
jet. Arbitrary complex Gaussian and Laplace widths of positive real part
are allowed, and the linear source may vanish. All polynomial degrees
are retained, including the degree-six differentiated quartic moments. -/
import UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalReciprocalWedgeLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargedFourierGaussianMoments
noncomputable section
open MeasureTheory
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalShiftedComplexGaussianMoments (moment value mass normalized)
open KFCausalReciprocalWedgeLaplace (laplace_integrable laplace_integral)

abbrev Charged := (ℝ × ℝ) × ℝ
def chargedMeasure : Measure Charged :=
  (volume.prod volume).prod (volume.restrict (Set.Ioi 0))
def density (S T c : ℂ) (n : ℕ) (u v Y : ℝ) : ℂ :=
  moment S 0 0 u*moment S c n v*Complex.exp (-T*(Y:ℂ))
def integral (S T c : ℂ) (n : ℕ) : ℂ :=
  ∫ Y in Set.Ioi 0, ∫ u, ∫ v, density S T c n u v Y
def kernel (S T c : ℂ) : ℂ :=
  (Real.pi:ℂ)/(S*T)*Complex.exp (c^2/(4*S))

theorem density_expansion (S T c : ℂ) (n : ℕ) (u v Y : ℝ) :
    density S T c n u v Y =
      (v:ℂ)^n*Complex.exp (-S*((u:ℂ)^2+(v:ℂ)^2)-T*(Y:ℂ)+c*(v:ℂ)) := by
  unfold density moment
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  rw [show Complex.exp (-S*(u:ℂ)^2)*((v:ℂ)^n*Complex.exp (-S*(v:ℂ)^2+c*(v:ℂ))) =
      (v:ℂ)^n*(Complex.exp (-S*(u:ℂ)^2)*Complex.exp (-S*(v:ℂ)^2+c*(v:ℂ))) by ring,
    mul_assoc,← Complex.exp_add,← Complex.exp_add]
  congr 2
  ring

theorem density_integrable (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (n : ℕ) :
    Integrable (fun p : Charged => density S T c n p.1.1 p.1.2 p.2) chargedMeasure := by
  exact ((KFCausalShiftedComplexGaussianMoments.moment_integrable S 0 hS 0).mul_prod
    (KFCausalShiftedComplexGaussianMoments.moment_integrable S c hS n)).mul_prod
    (laplace_integrable T hT)

theorem integral_factorization (S T c : ℂ) (hT : 0 < T.re) (n : ℕ) :
    integral S T c n = value S 0 0*value S c n/T := by
  unfold integral density value
  simp_rw [integral_mul_const,integral_const_mul]
  rw [laplace_integral T hT,integral_mul_const]
  ring

theorem integral_moment (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (n : ℕ) :
    integral S T c n = kernel S T c*normalized S c n := by
  rw [integral_factorization S T c hT,
    KFCausalShiftedComplexGaussianMoments.value_zero S 0 hS,
    KFCausalShiftedComplexGaussianMoments.value_all S c hS]
  simp only [mass,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,Complex.exp_zero,mul_one]
  rw [show gaussianValue S*(gaussianValue S*Complex.exp (c^2/(4*S))*normalized S c n) =
      gaussianValue S^2*(Complex.exp (c^2/(4*S))*normalized S c n) by ring,
    KFCausalReciprocalWedgeGeometry.gaussianValue_square]
  unfold kernel
  ring

theorem integral_zero (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    integral S T c 0 = kernel S T c := by
  simpa only [normalized,mul_one] using integral_moment S T c hS hT 0

theorem first_recurrence (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    (2*S)*integral S T c 1 = c*integral S T c 0 := by
  simp_rw [integral_factorization S T c hT]
  have h := KFCausalShiftedComplexGaussianMoments.first_recurrence S c hS
  calc
    _ = value S 0 0*((2*S)*value S c 1)/T := by ring
    _ = _ := by rw [h]; ring

theorem recurrence (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (n : ℕ) :
    (2*S)*integral S T c (n+2) =
      (n+1:ℂ)*integral S T c n+c*integral S T c (n+1) := by
  simp_rw [integral_factorization S T c hT]
  have h := KFCausalShiftedComplexGaussianMoments.recurrence S c hS n
  calc
    _ = value S 0 0*((2*S)*value S c (n+2))/T := by ring
    _ = _ := by rw [h]; ring

theorem integral_one (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    integral S T c 1 = kernel S T c*(c/(2*S)) := by
  exact integral_moment S T c hS hT 1

theorem integral_two (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    integral S T c 2 = kernel S T c*(c^2+2*S)/(4*S^2) := by
  have hn : S ≠ 0 := by intro hz; simp [hz] at hS
  rw [integral_moment S T c hS hT]
  norm_num [normalized]
  field_simp
  ring

theorem integral_three (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    integral S T c 3 = kernel S T c*(c^3+6*S*c)/(8*S^3) := by
  have hn : S ≠ 0 := by intro hz; simp [hz] at hS
  rw [integral_moment S T c hS hT]
  norm_num [normalized]
  field_simp
  ring

theorem integral_four (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) :
    integral S T c 4 = kernel S T c*(c^4+12*S*c^2+12*S^2)/(16*S^4) := by
  have hn : S ≠ 0 := by intro hz; simp [hz] at hS
  rw [integral_moment S T c hS hT]
  norm_num [normalized]
  field_simp
  ring

#print axioms density_expansion
#print axioms density_integrable
#print axioms integral_factorization
#print axioms integral_moment
#print axioms integral_zero
#print axioms first_recurrence
#print axioms recurrence
#print axioms integral_one
#print axioms integral_two
#print axioms integral_three
#print axioms integral_four
end
end UnifiedTheory.Audit.KFCausalChargedFourierGaussianMoments
