/- Exact derivatives of the repaired physical trial in every transverse
direction, with a bound retaining the full derivative of the shear flow. -/
import UnifiedTheory.Audit.KFCausalDampedProductJointEnergy
import UnifiedTheory.Audit.KFCausalTransverseClockWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalTransverseClockWeights

def derivative (v : Transverse) (f : Configuration → ℂ) (z : Configuration) : ℂ :=
  lineDeriv ℝ (fun y : Transverse => f (z.1,y)) z.2 v

def packetGradient (ψ : SchwartzMap TailSpace ℂ) : SchwartzMap Transverse (Transverse →L[ℝ] ℂ) :=
  SchwartzMap.fderivCLM ℝ Transverse ℂ (unflattenSchwartz ψ)

def gradientNorm (ψ : SchwartzMap TailSpace ℂ) (x : Transverse) : ℂ := ‖packetGradient ψ x‖

theorem gradientNorm_continuous (ψ : SchwartzMap TailSpace ℂ) : Continuous (gradientNorm ψ) :=
  Complex.continuous_ofReal.comp (packetGradient ψ).continuous.norm

theorem gradientNorm_square_integrable (ψ : SchwartzMap TailSpace ℂ) :
    Integrable (fun x => ‖gradientNorm ψ x‖^2) := by
  simpa only [gradientNorm,Complex.norm_real,norm_norm] using
    (memLp_two_iff_integrable_sq_norm ((packetGradient ψ).memLp 2 volume).aestronglyMeasurable).mp
      ((packetGradient ψ).memLp 2 volume)

theorem gradientNorm_pullback_continuous (ε : ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    Continuous (fun z : Configuration => pullback (phase ε z.1) (gradientNorm ψ) z.2) := by
  have hp := phase_continuous ε
  have hflow : Continuous (fun z : Configuration => flow (-phase ε z.1) z.2) :=
    flow_joint_continuous.comp ((hp.comp continuous_fst).neg.prodMk continuous_snd)
  change Continuous (fun z : Configuration => (Real.exp (-phase ε z.1):ℂ)*gradientNorm ψ (flow (-phase ε z.1) z.2))
  exact Continuous.mul (by fun_prop) ((gradientNorm_continuous ψ).comp hflow)

theorem derivative_formula (ε a p : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse)
    (s : ℝ) (x : Transverse) :
    derivative v (trialFunction ε a p ψ) (s,x) = (Real.sqrt (Real.exp s+ε):ℂ)*
      (modulate p (realTrial ε a) (chart ε s)*((Real.exp (-phase ε s):ℂ)*
        (packetGradient ψ (flow (-phase ε s) x)) (flow (-phase ε s) v))) := by
  have h := ((unflattenSchwartz ψ).hasFDerivAt (flow (-phase ε s) x)).comp x
    (flowCLM (-phase ε s)).hasFDerivAt
  have hc := ((h.const_mul (Real.exp (-phase ε s):ℂ)).const_mul
    (modulate p (realTrial ε a) (chart ε s))).const_mul (Real.sqrt (Real.exp s+ε):ℂ)
  exact (hc.hasLineDerivAt v).lineDeriv

theorem derivative_continuous (ε a p : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    Continuous (derivative v (trialFunction ε a p ψ)) := by
  have hp := phase_continuous ε
  have hg : Continuous (fun s => modulate p (realTrial ε a) (chart ε s)) :=
    (modulate_continuous p _ (realTrial_continuous ε a)).comp (chart_continuous ε)
  have hflow : Continuous (fun z : Configuration => flow (-phase ε z.1) z.2) :=
    flow_joint_continuous.comp ((hp.comp continuous_fst).neg.prodMk continuous_snd)
  have hv : Continuous (fun z : Configuration => flow (-phase ε z.1) v) :=
    flow_joint_continuous.comp ((hp.comp continuous_fst).neg.prodMk continuous_const)
  have he : derivative v (trialFunction ε a p ψ) = fun z : Configuration =>
      (Real.sqrt (Real.exp z.1+ε):ℂ)*(modulate p (realTrial ε a) (chart ε z.1)*
        ((Real.exp (-phase ε z.1):ℂ)*(packetGradient ψ (flow (-phase ε z.1) z.2)) (flow (-phase ε z.1) v))) :=
    funext (fun z => derivative_formula ε a p ψ v z.1 z.2)
  rw [he]
  refine Continuous.mul (by fun_prop) (Continuous.mul (hg.comp continuous_fst) ?_)
  exact Continuous.mul (by fun_prop) (((packetGradient ψ).continuous.comp hflow).clm_apply hv)

theorem derivative_density_bound (ε a p : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (v : Transverse) (s : ℝ) (x : Transverse) :
    ‖derivative v (trialFunction ε a p ψ) (s,x)‖^2 ≤
      baseDensity ε a s*‖flow (-phase ε s) v‖^2*‖pullback (phase ε s) (gradientNorm ψ) x‖^2 := by
  have hg := (packetGradient ψ (flow (-phase ε s) x)).le_opNorm (flow (-phase ε s) v)
  have hgs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc
    _ = ‖(Real.sqrt (Real.exp s+ε):ℂ)‖^2 * ‖modulate p (realTrial ε a) (chart ε s)‖^2 *
        ‖(Real.exp (-phase ε s):ℂ)‖^2 * ‖(packetGradient ψ (flow (-phase ε s) x)) (flow (-phase ε s) v)‖^2 := by
      rw [derivative_formula]
      simp only [norm_mul,mul_pow]
      ring
    _ ≤ ‖(Real.sqrt (Real.exp s+ε):ℂ)‖^2 * ‖modulate p (realTrial ε a) (chart ε s)‖^2 *
        ‖(Real.exp (-phase ε s):ℂ)‖^2 * (‖packetGradient ψ (flow (-phase ε s) x)‖ * ‖flow (-phase ε s) v‖)^2 :=
      mul_le_mul_of_nonneg_left hgs (by positivity)
    _ = _ := by
      simp only [baseDensity,pullback,gradientNorm,norm_mul,mul_pow,Complex.norm_real,norm_norm,modulate_norm]
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
      ring

#print axioms gradientNorm_continuous
#print axioms gradientNorm_square_integrable
#print axioms gradientNorm_pullback_continuous
#print axioms derivative_formula
#print axioms derivative_continuous
#print axioms derivative_density_bound

end
end UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
