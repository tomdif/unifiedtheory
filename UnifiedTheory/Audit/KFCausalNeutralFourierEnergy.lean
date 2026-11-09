/- Plancherel for the full quartic neutral energy, including complex
shear, all sources and arbitrary finite correlated coefficients. The
frequency integral is a sum of three nonnegative squares. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierField
import UnifiedTheory.Audit.KFCausalL2FourierIntegral
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierEnergy
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralFourierShift
open KFCausalNeutralFourierField
open KFCausalQuarticPlaneDomination (potential)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def frequencyMoment (j : ℕ) (d y k : ℝ) : ℝ :=
  Real.exp (-4*Real.pi*k*y)*‖spectrum n β b c P j ((d:ℂ)-(y:ℂ)*Complex.I) k‖^2

def frequencyDensity (d y k : ℝ) : ℝ :=
  frequencyMoment n β b c P 0 d y k+frequencyMoment n β b c P 1 d y k/2+
    frequencyMoment n β b c P 2 d y k/4

theorem frequencyMoment_nonnegative (j : ℕ) (d y k : ℝ) :
    0 ≤ frequencyMoment n β b c P j d y k := by unfold frequencyMoment; positivity

theorem frequencyDensity_nonnegative (d y k : ℝ) :
    0 ≤ frequencyDensity n β b c P d y k := by
  unfold frequencyDensity
  have h0 := frequencyMoment_nonnegative n β b c P 0 d y k
  have h1 := frequencyMoment_nonnegative n β b c P 1 d y k
  have h2 := frequencyMoment_nonnegative n β b c P 2 d y k
  positivity

theorem fieldLine_square (j : ℕ) (d y x : ℝ) :
    ‖fieldLine n β b c P j d y x‖^2 = (x+d)^(2*j)*‖line n β b c P y x‖^2 := by
  rw [fieldLine,norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    ← pow_mul,Nat.mul_comm j 2,pow_mul,sq_abs,← pow_mul]

theorem quartic_density (d y x : ℝ) :
    potential (x+d)*‖line n β b c P y x‖^2 =
      ‖fieldLine n β b c P 0 d y x‖^2+‖fieldLine n β b c P 1 d y x‖^2/2+
        ‖fieldLine n β b c P 2 d y x‖^2/4 := by
  simp only [fieldLine_square,potential]
  norm_num only [Nat.reduceMul,pow_zero,one_mul]
  ring

variable (hβ : 0 < β)
include hβ

theorem fieldLine_square_integrable (j : ℕ) (d y : ℝ) :
    Integrable (fun x => ‖fieldLine n β b c P j d y x‖^2) := by
  have hi := fieldLine_memLp n β hβ b c P j d y
  exact (memLp_two_iff_integrable_sq_norm hi.1).mp hi

theorem frequencyMoment_integrable (j : ℕ) (d y : ℝ) :
    Integrable (frequencyMoment n β b c P j d y) := by
  have hi := KFCausalL2FourierIntegral.integralFourier_memLp _
    (fieldLine_integrable n β hβ b c P j d y) (fieldLine_memLp n β hβ b c P j d y)
  have hs := (memLp_two_iff_integrable_sq_norm hi.1).mp hi
  change Integrable (fun k => frequencyMoment n β b c P j d y k)
  simpa only [fieldLine_fourier_square n β hβ,frequencyMoment] using hs

theorem field_plancherel (j : ℕ) (d y : ℝ) :
    (∫ x, ‖fieldLine n β b c P j d y x‖^2) =
      ∫ k, frequencyMoment n β b c P j d y k := by
  have h1 := fieldLine_integrable n β hβ b c P j d y
  have h2 := fieldLine_memLp n β hβ b c P j d y
  have ht := KFCausalL2FourierIntegral.integralFourier_memLp _ h1 h2
  have he : (∫ k, ‖(𝓕 (fieldLine n β b c P j d y)) k‖^2) =
      ∫ x, ‖fieldLine n β b c P j d y x‖^2 := by
    rw [← KFCausalCoupledFunctionEnergy.toLp_square_integral _ ht,
      ← KFCausalL2FourierIntegral.fourier_toLp_eq _ h1 h2,
      LinearIsometryEquiv.norm_map,KFCausalCoupledFunctionEnergy.toLp_square_integral]
  simpa only [fieldLine_fourier_square n β hβ,frequencyMoment] using he.symm

theorem frequencyDensity_integrable (d y : ℝ) :
    Integrable (frequencyDensity n β b c P d y) :=
  ((frequencyMoment_integrable n β b c P hβ 0 d y).add
    ((frequencyMoment_integrable n β b c P hβ 1 d y).div_const 2)).add
    ((frequencyMoment_integrable n β b c P hβ 2 d y).div_const 4)

theorem quartic_integrable (d y : ℝ) :
    Integrable (fun x => potential (x+d)*‖line n β b c P y x‖^2) := by
  simp_rw [quartic_density]
  exact ((fieldLine_square_integrable n β b c P hβ 0 d y).add
    ((fieldLine_square_integrable n β b c P hβ 1 d y).div_const 2)).add
    ((fieldLine_square_integrable n β b c P hβ 2 d y).div_const 4)

theorem quartic_plancherel (d y : ℝ) :
    (∫ x, potential (x+d)*‖line n β b c P y x‖^2) =
      ∫ k, frequencyDensity n β b c P d y k := by
  have hi := fieldLine_square_integrable n β b c P hβ
  have ht := frequencyMoment_integrable n β b c P hβ
  simp_rw [quartic_density]
  have hs := integral_add ((hi 0 d y).add ((hi 1 d y).div_const 2)) ((hi 2 d y).div_const 4)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add (hi 0 d y) ((hi 1 d y).div_const 2),integral_div,integral_div]
  simp only [field_plancherel n β b c P hβ]
  unfold frequencyDensity
  have hs := integral_add ((ht 0 d y).add ((ht 1 d y).div_const 2)) ((ht 2 d y).div_const 4)
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add (ht 0 d y) ((ht 1 d y).div_const 2),integral_div,integral_div]

#print axioms frequencyMoment_nonnegative
#print axioms frequencyDensity_nonnegative
#print axioms fieldLine_square
#print axioms quartic_density
#print axioms fieldLine_square_integrable
#print axioms frequencyMoment_integrable
#print axioms field_plancherel
#print axioms frequencyDensity_integrable
#print axioms quartic_integrable
#print axioms quartic_plancherel
end
end UnifiedTheory.Audit.KFCausalNeutralFourierEnergy
