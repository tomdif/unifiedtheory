/- Neutral frequency moments have actual L2/L1 domains, derived from
the spatial packet derivative and Plancherel. The derivative of the
Gaussian and polynomial factors is retained exactly. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierMomentum
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralFourierField
open KFCausalNeutralLinePackets (step)
open KFCausalL2FourierIntegral

theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (k : ℝ) :
    (𝓕 (fun x => c*f x)) k = c*(𝓕 f) k := by
  exact congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) f c) k

theorem fourier_add (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (k : ℝ) :
    (𝓕 (fun x => f x+g x)) k = (𝓕 f) k+(𝓕 g) k := by
  simp only [Real.fourier_eq,smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff k).mpr hf)
    ((Real.fourierIntegral_convergent_iff k).mpr hg)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def spatialDerivative (j : ℕ) (a y x : ℝ) : ℂ :=
  (j:ℂ)*fieldLine n β b c P (j-1) a y x+
    fieldLine n β b c (fun i => step β (b i) (P i)) j a y x

theorem line_derivative (y x : ℝ) :
    HasDerivAt (line n β b c P y)
      (line n β b c (fun i => step β (b i) (P i)) y x) x :=
  KFCausalNeutralJointCurvatureForm.translated_family_derivative n β b c P ((y:ℂ)*Complex.I) x

theorem fieldLine_derivative (j : ℕ) (a y x : ℝ) :
    HasDerivAt (fieldLine n β b c P j a y) (spatialDerivative n β b c P j a y x) x := by
  have hp := (((hasDerivAt_id x).add_const a).ofReal_comp.pow j).mul (line_derivative n β b c P y x)
  convert hp using 1
  unfold spatialDerivative fieldLine
  dsimp
  ring

variable (hβ : 0 < β)
include hβ

theorem spatialDerivative_integrable (j : ℕ) (a y : ℝ) :
    Integrable (spatialDerivative n β b c P j a y) :=
  ((fieldLine_integrable n β hβ b c P (j-1) a y).const_mul (j:ℂ)).add
    (fieldLine_integrable n β hβ b c _ j a y)

theorem spatialDerivative_memLp (j : ℕ) (a y : ℝ) :
    MemLp (spatialDerivative n β b c P j a y) 2 volume :=
  ((fieldLine_memLp n β hβ b c P (j-1) a y).const_mul (j:ℂ)).add
    (fieldLine_memLp n β hβ b c _ j a y)

theorem derivative_fourier (j : ℕ) (a y k : ℝ) :
    (𝓕 (spatialDerivative n β b c P j a y)) k =
      (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))*(𝓕 (fieldLine n β b c P j a y)) k := by
  have he : deriv (fieldLine n β b c P j a y) = spatialDerivative n β b c P j a y :=
    funext (fun x => (fieldLine_derivative n β b c P j a y x).deriv)
  have hf := Real.fourier_deriv (fieldLine_integrable n β hβ b c P j a y)
    (fun x => (fieldLine_derivative n β b c P j a y x).differentiableAt)
    (by rw [he]; exact spatialDerivative_integrable n β b c P hβ j a y)
  rw [he] at hf
  exact congrFun hf k

theorem step_fourier (j : ℕ) (a y k : ℝ) :
    (𝓕 (fieldLine n β b c (fun i => step β (b i) (P i)) j a y)) k =
      (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))*(𝓕 (fieldLine n β b c P j a y)) k-
      (j:ℂ)*(𝓕 (fieldLine n β b c P (j-1) a y)) k := by
  have hd := derivative_fourier n β b c P hβ j a y k
  unfold spatialDerivative at hd
  rw [fourier_add _ _
    ((fieldLine_integrable n β hβ b c P (j-1) a y).const_mul (j:ℂ))
    (fieldLine_integrable n β hβ b c _ j a y),fourier_const_mul] at hd
  linear_combination hd

theorem frequency_memLp (j : ℕ) (a y : ℝ) :
    MemLp (fun k : ℝ => (k:ℂ)*(𝓕 (fieldLine n β b c P j a y)) k) 2 volume := by
  have hi := (integralFourier_memLp _ (spatialDerivative_integrable n β b c P hβ j a y)
    (spatialDerivative_memLp n β b c P hβ j a y)).const_mul (1/(2*(Real.pi:ℂ)*Complex.I))
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  convert hi using 1
  funext k
  rw [derivative_fourier n β b c P hβ]
  field_simp

theorem frequencyMoment_integrable (j : ℕ) (a y : ℝ) :
    Integrable (fun k : ℝ => k*KFCausalNeutralFourierEnergy.frequencyMoment n β b c P j a y k) := by
  have hf := integralFourier_memLp _ (fieldLine_integrable n β hβ b c P j a y)
    (fieldLine_memLp n β hβ b c P j a y)
  have hi := (hf.star.integrable_mul (frequency_memLp n β b c P hβ j a y)).re
  change Integrable (fun k : ℝ => (star ((𝓕 (fieldLine n β b c P j a y)) k)*
    ((k:ℂ)*(𝓕 (fieldLine n β b c P j a y)) k)).re) at hi
  have he (k : ℝ) : (star ((𝓕 (fieldLine n β b c P j a y)) k)*
      ((k:ℂ)*(𝓕 (fieldLine n β b c P j a y)) k)).re =
      k*KFCausalNeutralFourierEnergy.frequencyMoment n β b c P j a y k := by
    simp only [Complex.star_def]
    rw [mul_left_comm,Complex.conj_mul']
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
    rw [fieldLine_fourier_square n β hβ]
    rfl
  simpa only [he] using hi

#print axioms fourier_const_mul
#print axioms fourier_add
#print axioms line_derivative
#print axioms fieldLine_derivative
#print axioms spatialDerivative_integrable
#print axioms spatialDerivative_memLp
#print axioms derivative_fourier
#print axioms step_fourier
#print axioms frequency_memLp
#print axioms frequencyMoment_integrable
end
end UnifiedTheory.Audit.KFCausalNeutralFourierMomentum
