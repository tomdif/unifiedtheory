/- Exact extraction of every polynomial degree from a bounded circle
of complex exponential sources. The normalization and the integration
measure are explicit. No finite degree cutoff is used. -/
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def circle (θ : ℝ) : ℂ := circleMap 0 1 (2*Real.pi*θ)

def weight (n : ℕ) (θ : ℝ) : ℂ :=
  circle θ*Complex.I/(circle θ)^(n+1)

def normalization (n : ℕ) : ℂ := (n.factorial:ℂ)/Complex.I

theorem circle_continuous : Continuous circle :=
  (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)

theorem circle_norm (θ : ℝ) : ‖circle θ‖ = 1 := by
  simp [circle]

theorem circle_ne_zero (θ : ℝ) : circle θ ≠ 0 := by
  intro hz
  have hn := circle_norm θ
  rw [hz,norm_zero] at hn
  norm_num at hn

theorem weight_continuous (n : ℕ) : Continuous (weight n) :=
  (circle_continuous.mul continuous_const).div (circle_continuous.pow (n+1))
    (fun θ => pow_ne_zero _ (circle_ne_zero θ))

theorem weight_norm (n : ℕ) (θ : ℝ) : ‖weight n θ‖ = 1 := by
  simp only [weight,norm_div,norm_mul,norm_pow,circle_norm,Complex.norm_I,one_mul,
    one_pow,div_self one_ne_zero]

theorem exponential_coefficient (n : ℕ) (X : ℂ) :
    normalization n*(∫ θ, weight n θ*Complex.exp (X*circle θ) ∂angleMeasure) = X^n := by
  let f : ℝ → ℂ := fun θ =>
    circleMap 0 1 θ*Complex.I/(circleMap 0 1 θ)^(n+1)*
      Complex.exp (X*circleMap 0 1 θ)
  have hc : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (X*z)) (Metric.closedBall 0 1) :=
    (Complex.differentiable_exp.comp (differentiable_id.const_mul X)).differentiableOn
  have hi := hc.circleIntegral_one_div_sub_center_pow_smul (by norm_num : (0:ℝ) < 1) n
  simp only [iteratedDeriv_cexp_const_mul,mul_zero,Complex.exp_zero,mul_one,
    sub_zero,smul_eq_mul] at hi
  have he : (∮ z in C((0:ℂ),1), 1/z^(n+1)*Complex.exp (X*z)) =
      ∫ θ in 0..2*Real.pi, f θ := by
    rw [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [f]
    rw [deriv_circleMap,smul_eq_mul]
    ring
  rw [he] at hi
  have hs : (∫ θ, weight n θ*Complex.exp (X*circle θ) ∂angleMeasure) =
      ((2*Real.pi)⁻¹:ℝ) • (∫ θ in 0..2*Real.pi, f θ) := by
    change (∫ θ in Set.Ioc (0:ℝ) 1, f (2*Real.pi*θ)) = _
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simpa only [mul_zero,mul_one] using
      intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) f (ne_of_gt Real.two_pi_pos)
  rw [hs,hi]
  simp only [normalization,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

#print axioms circle_continuous
#print axioms circle_norm
#print axioms circle_ne_zero
#print axioms weight_continuous
#print axioms weight_norm
#print axioms exponential_coefficient
end
end UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
