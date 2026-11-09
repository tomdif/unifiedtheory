/- A concrete repair of the failed Gaussian tail ansatz. The additional
factor exp(-epsilon*exp(-q/epsilon)) restores the weighted transverse
derivative energy. This proves that particular integrability condition;
membership in the exponential-longitudinal operator domain is still open. -/
import UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

def dampedGaussian (ε a q : ℝ) : ℝ :=
  Real.exp (-(a/2)*q^2-ε*Real.exp (-q/ε))

def dampedDensity (ε a s : ℝ) : ℝ :=
  (Real.exp s+ε)*Real.exp (-phase ε s-a*(chart ε s)^2-2*ε*Real.exp (-chart ε s/ε))

theorem damping_exponent_bound (ε s : ℝ) (hε : 0 < ε) :
    -phase ε s-2*ε*Real.exp (-chart ε s/ε) ≤ 2-s-ε*Real.exp (-s) := by
  have he : Real.exp (-chart ε s/ε) = Real.exp (-s)*Real.exp (-Real.exp s/ε) := by
    rw [← Real.exp_add]
    congr 1
    unfold chart
    field_simp
    ring
  have hx := Real.add_one_le_exp (-Real.exp s/ε)
  have hm := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ ε*Real.exp (-s))
  have hp : ε*Real.exp (-s)*(Real.exp s/ε) = 1 := by
    field_simp
    rw [← Real.exp_add]
    simp
  rw [he]
  unfold phase
  simp only [neg_div] at *
  nlinarith

theorem damping_weight_bound (ε s : ℝ) (hε : 0 < ε) :
    Real.exp (-phase ε s-2*ε*Real.exp (-chart ε s/ε)) ≤ Real.exp 2/ε := by
  have he := Real.exp_le_exp.mpr (damping_exponent_bound ε s hε)
  have hy : ε*Real.exp (-s) ≤ Real.exp (ε*Real.exp (-s)) := by
    linarith [Real.add_one_le_exp (ε*Real.exp (-s))]
  have hr : Real.exp (-s)/Real.exp (ε*Real.exp (-s)) ≤ 1/ε := by
    apply (div_le_div_iff₀ (Real.exp_pos _) hε).mpr
    simpa only [one_mul,mul_comm] using hy
  have hf : Real.exp (2-s-ε*Real.exp (-s)) =
      Real.exp 2*(Real.exp (-s)/Real.exp (ε*Real.exp (-s))) := by
    rw [Real.exp_sub,show 2-s = 2+(-s) by ring,Real.exp_add]
    ring
  rw [hf] at he
  exact he.trans (by simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left hr (Real.exp_pos 2).le)

theorem chart_gaussian_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s => (Real.exp s+ε)*Real.exp (-a*(chart ε s)^2)) := by
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun s (_ : s ∈ (univ : Set ℝ)) => (chart_derivative ε s).hasDerivWithinAt)
    (chart_strictMono ε hε).injective.injOn (fun q => Real.exp (-a*q^2))
  have hw (s : ℝ) : |Real.exp s+ε| = Real.exp s+ε := abs_of_pos (by positivity)
  have hi : Integrable (fun q : ℝ => Real.exp (-a*q^2)) := integrable_exp_neg_mul_sq ha
  have ht : Integrable (fun q : ℝ => Real.exp (-a*q^2)) ↔
      Integrable (fun s => (Real.exp s+ε)*Real.exp (-a*(chart ε s)^2)) := by
    simpa only [image_univ,(chart_surjective ε hε).range_eq,integrableOn_univ,hw,smul_eq_mul] using hh
  exact ht.mp hi

theorem damped_density_bound (ε a s : ℝ) (hε : 0 < ε) :
    dampedDensity ε a s ≤ (Real.exp 2/ε)*((Real.exp s+ε)*Real.exp (-a*(chart ε s)^2)) := by
  have hh := mul_le_mul_of_nonneg_left (damping_weight_bound ε s hε)
    (by positivity : 0 ≤ (Real.exp s+ε)*Real.exp (-a*(chart ε s)^2))
  unfold dampedDensity
  rw [show -phase ε s-a*(chart ε s)^2-2*ε*Real.exp (-chart ε s/ε) =
    -a*(chart ε s)^2+(-phase ε s-2*ε*Real.exp (-chart ε s/ε)) by ring,Real.exp_add]
  nlinarith

theorem damped_density_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (dampedDensity ε a) := by
  have hi := (chart_gaussian_integrable ε a hε ha).const_mul (Real.exp 2/ε)
  have hc : Continuous (dampedDensity ε a) := by unfold dampedDensity phase chart; fun_prop
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold dampedDensity; positivity)]
  exact damped_density_bound ε a s hε

def gaugedDampedGaussian (ε a s : ℝ) (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  (dampedGaussian ε a (chart ε s):ℂ)*pullback (phase ε s) ψ x

theorem gaugedDampedGaussian_derivative_density (ε a s : ℝ) (ψ : Transverse → ℂ)
    (x : Transverse) : ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2 =
      (dampedGaussian ε a (chart ε s))^2 *
        ‖directionalDerivative (pullback (phase ε s) ψ) x‖^2 := by
  change ‖directionalDerivative (fun y => (dampedGaussian ε a (chart ε s):ℂ)*
    pullback (phase ε s) ψ y) x‖^2 = _
  have hp : 0 < dampedGaussian ε a (chart ε s) := Real.exp_pos _
  rw [partial_const_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]

theorem gaugedDampedGaussian_derivative_energy (ε a s : ℝ) (ψ : Transverse → ℂ) :
    (Real.exp s+ε)*(∫ x, ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2) =
      dampedDensity ε a s*(∫ x, ‖directionalDerivative ψ x‖^2) := by
  simp_rw [gaugedDampedGaussian_derivative_density]
  rw [integral_const_mul,partial_energy_scaling,dampedGaussian,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  unfold dampedDensity
  have he : Real.exp (2*(-(a/2)*(chart ε s)^2-ε*Real.exp (-chart ε s/ε)))*
      Real.exp (-phase ε s) =
      Real.exp (-phase ε s-a*(chart ε s)^2-2*ε*Real.exp (-chart ε s/ε)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp s+ε)*(Real.exp (2*(-(a/2)*(chart ε s)^2-ε*Real.exp (-chart ε s/ε)))*
      Real.exp (-phase ε s))*(∫ x, ‖directionalDerivative ψ x‖^2) := by ring
    _ = _ := by rw [he]

theorem gaugedDampedGaussian_integrable_energy (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : Transverse → ℂ) :
    Integrable (fun s => (Real.exp s+ε)*
      (∫ x, ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2)) := by
  simp only [gaugedDampedGaussian_derivative_energy]
  exact (damped_density_integrable ε a hε ha).mul_const _

theorem gaugedDampedGaussian_slice_integrable (ε a s : ℝ) (ψ : Transverse → ℂ)
    (hψ : Integrable (fun x => ‖directionalDerivative ψ x‖^2)) :
    Integrable (fun x => ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2) := by
  have hi := (pullback_square_integrable_iff (phase ε s) (directionalDerivative ψ)).mpr hψ
  have hu : Integrable (fun x => ‖directionalDerivative (pullback (phase ε s) ψ) x‖^2) := by
    have hs : 0 < scale (-phase ε s) := Real.exp_pos _
    convert hi.const_mul (Real.exp (-phase ε s)) using 1
    funext x
    rw [partial_pullback,norm_smul,Real.norm_eq_abs,abs_of_pos hs,mul_pow,scale_square]
  simp_rw [gaugedDampedGaussian_derivative_density]
  exact hu.const_mul _

/-- Both slice integrability and the weighted outer integral are supplied,
so this statement does not rely on zero values of undefined Bochner integrals. -/
theorem gaugedDampedGaussian_finite_energy (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : Transverse → ℂ) (hψ : Integrable (fun x => ‖directionalDerivative ψ x‖^2)) :
    (∀ s, Integrable (fun x => ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2)) ∧
      Integrable (fun s => (Real.exp s+ε)*
        (∫ x, ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2)) :=
  ⟨fun s => gaugedDampedGaussian_slice_integrable ε a s ψ hψ,
    gaugedDampedGaussian_integrable_energy ε a hε ha ψ⟩

#print axioms damping_exponent_bound
#print axioms damping_weight_bound
#print axioms chart_gaussian_integrable
#print axioms damped_density_bound
#print axioms damped_density_integrable
#print axioms gaugedDampedGaussian_derivative_density
#print axioms gaugedDampedGaussian_derivative_energy
#print axioms gaugedDampedGaussian_integrable_energy
#print axioms gaugedDampedGaussian_slice_integrable
#print axioms gaugedDampedGaussian_finite_energy

end
end UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
