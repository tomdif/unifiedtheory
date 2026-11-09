/- The repaired scalar trial function satisfies the exponential Fourier
energy condition when |hbar| < pi*epsilon. This is a sufficient condition
for these scalar trials, not a no-go threshold for the full six-mode model. -/
import UnifiedTheory.Audit.KFCausalDampedGaussianStrip
import UnifiedTheory.Audit.KFCausalFourierStripDecay
import UnifiedTheory.Audit.KFCausalExponentialFourierDomain
import UnifiedTheory.Audit.KFCausalRegularizedFormDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
open UnifiedTheory.Audit.KFCausalDampedGaussianStrip
open UnifiedTheory.Audit.KFCausalGaussianContourShift
open UnifiedTheory.Audit.KFCausalFourierStripDecay
open UnifiedTheory.Audit.KFCausalExponentialFourierDomain
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

def realTrial (ε a : ℝ) (q : ℝ) : ℂ := dampedGaussian ε a q

theorem line_zero (ε a : ℝ) : line ε a 0 = realTrial ε a := by
  funext q
  simp only [line,Complex.ofReal_zero,zero_mul,add_zero,entire_real,realTrial]

theorem realTrial_continuous (ε a : ℝ) : Continuous (realTrial ε a) := by
  rw [← line_zero]
  exact line_continuous ε a 0

theorem realTrial_ne_zero (ε a q : ℝ) : realTrial ε a q ≠ 0 := by
  unfold realTrial dampedGaussian
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem realTrial_integrable (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    Integrable (realTrial ε a) := by
  rw [← line_zero]
  exact line_integrable ε a 0 hε ha (by simp)

theorem realTrial_square_integrable (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    Integrable (fun q => ‖realTrial ε a q‖^2) := by
  rw [← line_zero]
  exact line_square_integrable ε a 0 hε ha (by simp)

def stripConstant (ε a : ℝ) : ℝ :=
  Real.exp ((a/2)*(Real.pi*ε/2)^2)*(∫ q : ℝ, Real.exp (-(a/2)*q^2))

theorem stripConstant_nonnegative (ε a : ℝ) : 0 ≤ stripConstant ε a := by
  unfold stripConstant
  exact mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))

theorem realTrial_fourier_decay (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (k : ℝ) :
    ‖(𝓕 (realTrial ε a)) k‖ ≤
      Real.exp (-2*Real.pi*(Real.pi*ε/2)*|k|)*stripConstant ε a := by
  have hh := fourier_exponential_decay (entire ε a) (entire_differentiable ε a)
    (a/2) (Real.exp ((a/2)*(Real.pi*ε/2)^2)) (Real.pi*ε/2)
    (by positivity) (by positivity)
    (fun q r hr => strip_gaussian_bound ε a (Real.pi*ε/2) hε ha.le le_rfl r q hr) k
  change ‖(𝓕 (line ε a 0)) k‖ ≤ _ at hh
  rw [line_zero] at hh
  exact hh

theorem realTrial_exponential_momentum_integrable (ε a hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| < Real.pi*ε) :
    Integrable (fun k => Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (realTrial ε a)) k‖^2) := by
  apply weighted_square_integrable (𝓕 (realTrial ε a))
    (fourier_continuous_integrable _ (realTrial_integrable ε a hε.le ha))
    (Real.pi*ε/2) (stripConstant ε a) hbar (stripConstant_nonnegative ε a)
  · linarith
  · exact realTrial_fourier_decay ε a hε ha

/-- The same scalar trial has L1 and L2 integrability, exponential Fourier
energy, and the earlier transverse derivative-energy repair. This does not
identify the coupled unbounded operator or the remaining full energy terms. -/
theorem repaired_trial_joint_conditions (ε a hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| < Real.pi*ε)
    (ψ : Transverse → ℂ) (hψ : Integrable (fun x => ‖directionalDerivative ψ x‖^2)) :
    Integrable (realTrial ε a) ∧ Integrable (fun q => ‖realTrial ε a q‖^2) ∧
      Integrable (fun k => Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (realTrial ε a)) k‖^2) ∧
      (∀ s, Integrable (fun x => ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2)) ∧
      Integrable (fun s => (Real.exp s+ε)*
        (∫ x, ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2)) := by
  exact ⟨realTrial_integrable ε a hε.le ha,realTrial_square_integrable ε a hε.le ha,
    realTrial_exponential_momentum_integrable ε a hbar hε ha hh,
    gaugedDampedGaussian_finite_energy ε a hε ha ψ hψ⟩

#print axioms realTrial_ne_zero
#print axioms realTrial_integrable
#print axioms realTrial_square_integrable
#print axioms realTrial_fourier_decay
#print axioms realTrial_exponential_momentum_integrable
#print axioms repaired_trial_joint_conditions

end
end UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
