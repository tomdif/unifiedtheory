/- All momentum modulations of the repaired scalar trial retain its
exponential Fourier energy. Their complex span is dense in clock L2.
This is not density of a full six-mode common operator domain. -/
import UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
import UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedGaussianTotality
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalFourierUniqueness

open UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

theorem modulated_momentum_integrable (ε a hbar p : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| < Real.pi*ε) :
    Integrable (fun k => Real.exp (2*Real.pi*hbar*k)*
      ‖(𝓕 (modulate p (realTrial ε a))) k‖^2) := by
  have hi := (realTrial_exponential_momentum_integrable ε a hbar hε ha hh).comp_sub_right p
  convert hi.const_mul (Real.exp (2*Real.pi*hbar*p)) using 1
  funext k
  rw [fourier_modulate]
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem realTrial_memLp (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) : MemLp (realTrial ε a) 2 :=
  (memLp_two_iff_integrable_sq_norm (realTrial_continuous ε a).aestronglyMeasurable).mpr
    (realTrial_square_integrable ε a hε ha)

theorem modulated_memLp (ε a p : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    MemLp (modulate p (realTrial ε a)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (modulate_continuous p _ (realTrial_continuous ε a)).aestronglyMeasurable).mpr
  simpa only [modulate_norm] using realTrial_square_integrable ε a hε ha

theorem ae_zero_of_orthogonal_modulations (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (f : ℝ → ℂ) (hf : MemLp f 2)
    (ho : ∀ p : ℝ, (∫ q, star (modulate p (realTrial ε a) q)*f q)=0) :
    ∀ᵐ q, f q=0 := by
  let g : ℝ → ℂ := fun q => star (realTrial ε a q)*f q
  have hg : Integrable g := (realTrial_memLp ε a hε ha).star.integrable_mul hf
  have hF : ∀ p : ℝ, (𝓕 g) p=0 := by
    intro p
    rw [Real.fourier_real_eq]
    convert ho p using 1
    congr 1
    funext q
    simp only [g,modulate,Circle.smul_def,smul_eq_mul,star_mul,Complex.star_def,
      ← Circle.coe_inv_eq_conj,← AddChar.map_neg_eq_inv]
    rw [mul_comm p q]
    ring
  have hz := integrable_zero_of_fourier_zero g hg hF
  filter_upwards [hz] with q hq
  exact (mul_eq_zero.mp hq).resolve_left (star_ne_zero.mpr (realTrial_ne_zero ε a q))

def modulatedLp (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (p : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (modulated_memLp ε a p hε ha).toLp (modulate p (realTrial ε a))

theorem dense_modulated_span (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (modulatedLp ε a hε ha))).topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply ae_zero_of_orthogonal_modulations ε a hε ha f (Lp.memLp f)
  intro p
  have hm : modulatedLp ε a hε ha p ∈
      Submodule.span ℂ (Set.range (modulatedLp ε a hε ha)) :=
    Submodule.subset_span ⟨p,rfl⟩
  have ho := Submodule.inner_right_of_mem_orthogonal hm hf
  rw [L2.inner_def] at ho
  convert ho using 1
  apply integral_congr_ae
  filter_upwards [(modulated_memLp ε a p hε ha).coeFn_toLp] with q hq
  change star (modulate p (realTrial ε a) q)*f q =
    inner ℂ (((modulated_memLp ε a p hε ha).toLp _) q) (f q)
  rw [hq,RCLike.inner_apply']
  rfl

def modulatedGauged (ε a p s : ℝ) (ψ : Transverse → ℂ) (x : Transverse) : ℂ :=
  modulate p (realTrial ε a) (chart ε s)*pullback (phase ε s) ψ x

theorem modulatedGauged_derivative_density (ε a p s : ℝ) (ψ : Transverse → ℂ)
    (x : Transverse) :
    ‖directionalDerivative (modulatedGauged ε a p s ψ) x‖^2 =
      ‖directionalDerivative (gaugedDampedGaussian ε a s ψ) x‖^2 := by
  have he : modulatedGauged ε a p s ψ = fun y =>
      (Real.fourierChar (p*chart ε s):ℂ)*gaugedDampedGaussian ε a s ψ y := by
    funext y
    unfold modulatedGauged modulate realTrial gaugedDampedGaussian
    ring
  rw [he,partial_const_mul,norm_mul]
  simp

theorem modulatedGauged_finite_energy (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : Transverse → ℂ) (hψ : Integrable (fun x => ‖directionalDerivative ψ x‖^2)) :
    (∀ s, Integrable (fun x => ‖directionalDerivative (modulatedGauged ε a p s ψ) x‖^2)) ∧
      Integrable (fun s => (Real.exp s+ε)*
        (∫ x, ‖directionalDerivative (modulatedGauged ε a p s ψ) x‖^2)) := by
  simpa only [modulatedGauged_derivative_density] using
    gaugedDampedGaussian_finite_energy ε a hε ha ψ hψ

#print axioms modulated_momentum_integrable
#print axioms realTrial_memLp
#print axioms modulated_memLp
#print axioms ae_zero_of_orthogonal_modulations
#print axioms dense_modulated_span
#print axioms modulatedGauged_derivative_density
#print axioms modulatedGauged_finite_energy

end
end UnifiedTheory.Audit.KFCausalDampedGaussianTotality
