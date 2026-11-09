/- The same explicit physical trial has both actual longitudinal
half-exponential domain membership and finite full-configuration first
transverse derivative energy. Other full Hamiltonian terms remain separate. -/
import UnifiedTheory.Audit.KFCausalDampedProductDomain
import UnifiedTheory.Audit.KFCausalSchwartzTransversePacket

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedProductJointEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalLongitudinalExponential

def transverseDerivative (ε a p : ℝ) (ψ : TailSpace → ℂ) (z : Configuration) : ℂ :=
  directionalDerivative (fun x => trialFunction ε a p ψ (z.1,x)) z.2

theorem trialFunction_transverse_differentiable (ε a p s : ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    Differentiable ℝ (fun x : Transverse => trialFunction ε a p ψ (s,x)) := by
  have hp : Differentiable ℝ (fun x : Transverse =>
      (ψ ∘ transverseCoordinates) (flow (-phase ε s) x)) :=
    (unflattenSchwartz ψ).differentiable.comp (flowCLM (-phase ε s)).differentiable
  change Differentiable ℝ (fun x : Transverse =>
    (Real.sqrt (Real.exp s+ε):ℂ) *
      (modulate p (realTrial ε a) (chart ε s) *
        ((Real.exp (-phase ε s):ℂ) * (ψ ∘ transverseCoordinates) (flow (-phase ε s) x))))
  exact hp.const_mul _ |>.const_mul _ |>.const_mul _

theorem transverseDerivative_density (ε a p : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ)
    (s : ℝ) (x : Transverse) :
    ‖transverseDerivative ε a p ψ (s,x)‖^2 =
      (Real.exp s+ε)*‖directionalDerivative (modulatedGauged ε a p s (ψ ∘ transverseCoordinates)) x‖^2 := by
  change ‖directionalDerivative (fun y => (Real.sqrt (Real.exp s+ε):ℂ)*
    modulatedGauged ε a p s (ψ ∘ transverseCoordinates) y) x‖^2 = _
  rw [partial_const_mul,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]

theorem transverseDerivative_continuous (ε a p : ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    Continuous (transverseDerivative ε a p ψ) := by
  have hd : Continuous (directionalDerivative (ψ ∘ transverseCoordinates)) := by
    have he : (directionalSchwartz ψ : Transverse → ℂ) = directionalDerivative (ψ ∘ transverseCoordinates) :=
      funext (directionalSchwartz_apply ψ)
    rw [← he]
    exact (directionalSchwartz ψ).continuous
  have hg : Continuous (fun s => modulate p (realTrial ε a) (chart ε s)) :=
    (modulate_continuous p _ (realTrial_continuous ε a)).comp (chart_continuous ε)
  have hflow : Continuous (fun z : Configuration => flow (-phase ε z.1) z.2) :=
    flow_joint_continuous.comp (((phase_continuous ε).comp continuous_fst).neg.prodMk continuous_snd)
  have hp := phase_continuous ε
  change Continuous (fun z : Configuration =>
    directionalDerivative (fun x => trialFunction ε a p ψ (z.1,x)) z.2)
  simp only [trialFunction,modulatedGauged,partial_const_mul]
  simp only [partial_pullback]
  simp only [pullback,Complex.real_smul]
  unfold scale
  refine Continuous.mul (by fun_prop) (Continuous.mul (hg.comp continuous_fst) ?_)
  exact Continuous.mul (by fun_prop) (Continuous.mul (by fun_prop) (hd.comp hflow))

theorem transverseDerivative_slices (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) :
    (∀ s, Integrable (fun x : Transverse => ‖transverseDerivative ε a p ψ (s,x)‖^2)) ∧
      Integrable (fun s => ∫ x : Transverse, ‖transverseDerivative ε a p ψ (s,x)‖^2) := by
  have he := modulatedGauged_finite_energy ε a p hε ha (ψ ∘ transverseCoordinates) (packet_directional_energy ψ)
  constructor
  · intro s
    simpa only [transverseDerivative_density ε a p hε] using (he.1 s).const_mul (Real.exp s+ε)
  · simpa only [transverseDerivative_density ε a p hε,integral_const_mul] using he.2

theorem transverseDerivative_energy (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) :
    Integrable (fun z : Configuration => ‖transverseDerivative ε a p ψ z‖^2) := by
  have hm : AEStronglyMeasurable (fun z : Configuration => ‖transverseDerivative ε a p ψ z‖^2) volume :=
    ((transverseDerivative_continuous ε a p ψ).norm.pow 2).aestronglyMeasurable
  have he := transverseDerivative_slices ε a p hε ha ψ
  rw [Measure.volume_eq_prod ℝ Transverse] at hm ⊢
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall he.1,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  exact he.2

theorem transverseDerivative_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) : MemLp (transverseDerivative ε a p ψ) 2 :=
  (memLp_two_iff_integrable_sq_norm (transverseDerivative_continuous ε a p ψ).aestronglyMeasurable).mpr
    (transverseDerivative_energy ε a p hε ha ψ)

theorem repaired_product_joint_conditions (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) :
    MemLp (trialFunction ε a p ψ) 2 ∧
      trialState ε a p hε ha ψ (ψ.memLp 2 volume) ∈
        (longitudinalExponential ε hε hbar (1/2)).domain ∧
      MemLp (transverseDerivative ε a p ψ) 2 :=
  ⟨trialFunction_memLp ε a p hε ha ψ (ψ.memLp 2 volume),
    trialState_half_domain ε a p hbar hε ha hh ψ ψ.integrable (ψ.memLp 2 volume),
    transverseDerivative_memLp ε a p hε ha ψ⟩

#print axioms trialFunction_transverse_differentiable
#print axioms transverseDerivative_density
#print axioms transverseDerivative_continuous
#print axioms transverseDerivative_slices
#print axioms transverseDerivative_energy
#print axioms transverseDerivative_memLp
#print axioms repaired_product_joint_conditions

end
end UnifiedTheory.Audit.KFCausalDampedProductJointEnergy
