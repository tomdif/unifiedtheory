/- Exact derivative-energy scaling of the transverse pullback. This
connects the coupled Gaussian weight obstruction to a transverse momentum
term, rather than inferring it from coordinate growth alone. -/
import UnifiedTheory.Audit.KFCausalTransverseDilationPullback
import UnifiedTheory.Audit.KFCausalCoupledGaussianObstruction
import Mathlib.Analysis.Calculus.Deriv.CompMul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledGaussianObstruction

def direction : Transverse := Pi.single 0 1

def directionalDerivative (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  deriv (fun r : ℝ => ψ (x+r • direction)) 0

theorem flow_line (t r : ℝ) (x : Transverse) :
    flow t (x+r • direction) = flow t x+(scale t*r) • direction := by
  funext i
  fin_cases i <;> simp [flow,direction,mul_add]

theorem partial_const_mul (c : ℂ) (ψ : Transverse → ℂ) (x : Transverse) :
    directionalDerivative (fun y => c*ψ y) x = c*directionalDerivative ψ x := by
  exact deriv_const_mul_field c

theorem partial_pullback (t : ℝ) (ψ : Transverse → ℂ) (x : Transverse) :
    directionalDerivative (pullback t ψ) x = scale (-t) • pullback t (directionalDerivative ψ) x := by
  have he : (fun r : ℝ => pullback t ψ (x+r • direction)) =
      (fun r : ℝ => (Real.exp (-t):ℂ)*ψ (flow (-t) x+(scale (-t)*r) • direction)) := by
    funext r
    rw [pullback,flow_line]
  rw [directionalDerivative,he,deriv_const_mul_field]
  have hh := deriv_comp_mul_left (scale (-t)) (fun r : ℝ => ψ (flow (-t) x+r • direction)) 0
  rw [hh]
  simp only [mul_zero,directionalDerivative,pullback,Complex.real_smul]
  ring

theorem scale_square (t : ℝ) : (scale (-t))^2 = Real.exp (-t) := by
  rw [scale,← Real.exp_nat_mul]
  congr 1
  ring

theorem partial_energy_scaling (t : ℝ) (ψ : Transverse → ℂ) :
    (∫ x, ‖directionalDerivative (pullback t ψ) x‖^2) = Real.exp (-t)*(∫ x, ‖directionalDerivative ψ x‖^2) := by
  have hd (x : Transverse) : ‖directionalDerivative (pullback t ψ) x‖^2 =
      Real.exp (-t)*‖pullback t (directionalDerivative ψ) x‖^2 := by
    have hs : 0 < scale (-t) := Real.exp_pos _
    rw [partial_pullback,norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul_pow,scale_square]
  simp_rw [hd]
  rw [integral_const_mul,pullback_square_integral]

def gaugedGaussian (ε a s : ℝ) (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  (Real.exp (-(a/2)*(chart ε s)^2):ℂ)*pullback (phase ε s) ψ x

theorem gaugedGaussian_derivative_energy (ε a s : ℝ) (ψ : Transverse → ℂ) :
    (Real.exp s+ε)*(∫ x, ‖directionalDerivative (gaugedGaussian ε a s ψ) x‖^2) =
      weightedGaussianDensity ε a s*(∫ x, ‖directionalDerivative ψ x‖^2) := by
  have hd (x : Transverse) : ‖directionalDerivative (gaugedGaussian ε a s ψ) x‖^2 =
      (Real.exp (-(a/2)*(chart ε s)^2))^2 *
        ‖directionalDerivative (pullback (phase ε s) ψ) x‖^2 := by
    change ‖directionalDerivative (fun y => (Real.exp (-(a/2)*(chart ε s)^2):ℂ)*
      pullback (phase ε s) ψ y) x‖^2 = _
    rw [partial_const_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_pow]
  simp_rw [hd]
  rw [integral_const_mul,partial_energy_scaling,← Real.exp_nat_mul]
  have he : 2*(-(a/2)*(chart ε s)^2) = -a*(chart ε s)^2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  unfold weightedGaussianDensity
  rw [show -phase ε s-a*(chart ε s)^2 = -a*(chart ε s)^2+(-phase ε s) by ring,Real.exp_add]
  ring

theorem gaugedGaussian_nonintegrable_energy (ε a : ℝ) (hε : 0 < ε) (ha : 0 ≤ a)
    (ψ : Transverse → ℂ) (hψ : (∫ x, ‖directionalDerivative ψ x‖^2) ≠ 0) :
    ¬ Integrable (fun s => (Real.exp s+ε)*(∫ x, ‖directionalDerivative (gaugedGaussian ε a s ψ) x‖^2)) := by
  simp only [gaugedGaussian_derivative_energy]
  intro hi
  have hh := hi.mul_const (∫ x, ‖directionalDerivative ψ x‖^2)⁻¹
  have he : (fun s => weightedGaussianDensity ε a s*(∫ x, ‖directionalDerivative ψ x‖^2)*(∫ x, ‖directionalDerivative ψ x‖^2)⁻¹) =
      weightedGaussianDensity ε a := by
    funext s
    rw [mul_assoc,mul_inv_cancel₀ hψ,mul_one]
  rw [he] at hh
  exact weightedGaussian_not_integrable ε a hε ha hh

#print axioms flow_line
#print axioms partial_pullback
#print axioms partial_energy_scaling
#print axioms gaugedGaussian_derivative_energy
#print axioms gaugedGaussian_nonintegrable_energy

end
end UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling
