/- Exact transverse derivatives of the revised product-core trial.
The full shear derivative is retained in every transverse direction. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoreStates
import UnifiedTheory.Audit.KFCausalTransverseTrialDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoreDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph (flow_joint_continuous)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalTransverseClockWeights (baseDensity)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative packetGradient gradientNorm gradientNorm_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates

theorem trialFunction_transverse_differentiable (ε a p s : ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    Differentiable ℝ (fun x : Transverse => trialFunction ε a p ψ (s,x)) := by
  have hp := (unflattenSchwartz ψ).differentiable.comp (flowCLM (-s)).differentiable
  exact hp.const_mul (Real.exp (-s):ℂ) |>.const_mul (modulate p (realTrial ε a) (chart ε s))
    |>.const_mul (Real.sqrt (Real.exp s+ε):ℂ)

theorem gradientNorm_pullback_continuous (ψ : SchwartzMap TailSpace ℂ) :
    Continuous (fun z : Configuration => pullback z.1 (gradientNorm ψ) z.2) := by
  have hflow : Continuous (fun z : Configuration => flow (-z.1) z.2) :=
    flow_joint_continuous.comp (continuous_fst.neg.prodMk continuous_snd)
  change Continuous (fun z : Configuration => (Real.exp (-z.1):ℂ)*gradientNorm ψ (flow (-z.1) z.2))
  exact Continuous.mul (by fun_prop) ((gradientNorm_continuous ψ).comp hflow)

theorem derivative_formula (ε a p : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse)
    (s : ℝ) (x : Transverse) :
    derivative v (trialFunction ε a p ψ) (s,x) = (Real.sqrt (Real.exp s+ε):ℂ)*
      (modulate p (realTrial ε a) (chart ε s)*((Real.exp (-s):ℂ)*
        (packetGradient ψ (flow (-s) x)) (flow (-s) v))) := by
  have h := ((unflattenSchwartz ψ).hasFDerivAt (flow (-s) x)).comp x (flowCLM (-s)).hasFDerivAt
  have hc := ((h.const_mul (Real.exp (-s):ℂ)).const_mul
    (modulate p (realTrial ε a) (chart ε s))).const_mul (Real.sqrt (Real.exp s+ε):ℂ)
  exact (hc.hasLineDerivAt v).lineDeriv

theorem derivative_continuous (ε a p : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    Continuous (derivative v (trialFunction ε a p ψ)) := by
  have hg : Continuous (fun s => modulate p (realTrial ε a) (chart ε s)) :=
    (modulate_continuous p _ (realTrial_continuous ε a)).comp (chart_continuous ε)
  have hflow : Continuous (fun z : Configuration => flow (-z.1) z.2) :=
    flow_joint_continuous.comp (continuous_fst.neg.prodMk continuous_snd)
  have hv : Continuous (fun z : Configuration => flow (-z.1) v) :=
    flow_joint_continuous.comp (continuous_fst.neg.prodMk continuous_const)
  have he : derivative v (trialFunction ε a p ψ) = fun z : Configuration =>
      (Real.sqrt (Real.exp z.1+ε):ℂ)*(modulate p (realTrial ε a) (chart ε z.1)*
        ((Real.exp (-z.1):ℂ)*(packetGradient ψ (flow (-z.1) z.2)) (flow (-z.1) v))) :=
    funext (fun z => derivative_formula ε a p ψ v z.1 z.2)
  rw [he]
  refine Continuous.mul (by fun_prop) (Continuous.mul (hg.comp continuous_fst) ?_)
  exact Continuous.mul (by fun_prop) (((packetGradient ψ).continuous.comp hflow).clm_apply hv)

theorem derivative_density_bound (ε a p : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (v : Transverse) (s : ℝ) (x : Transverse) :
    ‖derivative v (trialFunction ε a p ψ) (s,x)‖^2 ≤
      baseDensity ε a s*‖flow (-s) v‖^2*‖pullback s (gradientNorm ψ) x‖^2 := by
  have hg := (packetGradient ψ (flow (-s) x)).le_opNorm (flow (-s) v)
  have hgs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc
    _ = ‖(Real.sqrt (Real.exp s+ε):ℂ)‖^2 * ‖modulate p (realTrial ε a) (chart ε s)‖^2 *
        ‖(Real.exp (-s):ℂ)‖^2 * ‖(packetGradient ψ (flow (-s) x)) (flow (-s) v)‖^2 := by
      rw [derivative_formula]
      simp only [norm_mul,mul_pow]
      ring
    _ ≤ ‖(Real.sqrt (Real.exp s+ε):ℂ)‖^2 * ‖modulate p (realTrial ε a) (chart ε s)‖^2 *
        ‖(Real.exp (-s):ℂ)‖^2 * (‖packetGradient ψ (flow (-s) x)‖ * ‖flow (-s) v‖)^2 :=
      mul_le_mul_of_nonneg_left hgs (by positivity)
    _ = _ := by
      simp only [baseDensity,pullback,gradientNorm,norm_mul,mul_pow,Complex.norm_real,norm_norm,modulate_norm]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
      ring

#print axioms trialFunction_transverse_differentiable
#print axioms gradientNorm_pullback_continuous
#print axioms derivative_formula
#print axioms derivative_continuous
#print axioms derivative_density_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorCoreDerivative
