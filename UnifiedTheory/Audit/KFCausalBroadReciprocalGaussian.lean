/- A concrete broad reciprocal Gaussian for the two-shear quotient argument.
The charged width is 1/4 and the neutral width is alpha/512. Its actual
ordered and full longitudinal exponential graphs are constructed using a
negative squeeze parameter. No mixed-factor or full Hamiltonian graph is
claimed here. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianDomain
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalBroadReciprocalGaussian
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorInvariantTrial (clockFunction)
open KFCausalReciprocalGaussianStates (configurationDensity)
open KFCausalReciprocalSqueezeTransport
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)

def squeezeParameter : ℝ := -Real.log 2

private theorem exp_two_log : Real.exp (2*Real.log 2) = 4 := by
  rw [show 2*Real.log 2=Real.log 2+Real.log 2 by ring,Real.exp_add]
  norm_num [Real.exp_log]

theorem charged_width : Real.exp (2*squeezeParameter) = 1/4 := by
  rw [squeezeParameter,show 2*(-Real.log 2)=-(2*Real.log 2) by ring,
    Real.exp_neg,exp_two_log]
  norm_num

theorem neutral_width (α : ℝ) : (α/512)*Real.exp (-2*squeezeParameter) = α/128 := by
  rw [squeezeParameter,show -2*(-Real.log 2)=2*Real.log 2 by ring,exp_two_log]
  ring

variable (ε a α : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)

include hα in
private theorem base_positive : 0 < α/128 := by positivity
include hα in
private theorem base_bound : 32*(α/128) ≤ α := by linarith

def base : Hilbert :=
  KFCausalClockFloorSourcedClockMomentum.state ε a α (α/128) hε ha hα
    (base_positive α hα) (base_bound α hα) 1 0 0

def state : Hilbert := (Real.exp (-squeezeParameter/2):ℂ) •
  transport (-squeezeParameter) (base ε a α hε ha hα)

theorem state_coe : state ε a α hε ha hα =ᵐ[volume]
    configurationDensity α (α/512) (1/4) (clockFunction ε a) := by
  let f := base ε a α hε ha hα
  filter_upwards [Lp.coeFn_smul (Real.exp (-squeezeParameter/2):ℂ)
      (transport (-squeezeParameter) f),transport_coe (-squeezeParameter) f,
    (squeezeFlow_quasiMeasurePreserving (-squeezeParameter)).ae
      (KFCausalClockFloorSourcedClockMomentum.state_coe ε a α (α/128) hε ha hα
        (base_positive α hα) (base_bound α hα) 1 0 0)] with x hc ht hf
  change f (squeezeFlow (-squeezeParameter) x) = _ at hf
  change ((Real.exp (-squeezeParameter/2):ℂ) • transport (-squeezeParameter) f) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,ht]
  change (Real.exp (-squeezeParameter/2):ℂ)*
    ((Real.exp (-(-squeezeParameter)/2):ℂ)*f (squeezeFlow (-squeezeParameter) x)) = _
  rw [hf]
  simp only [squeezeFlow_apply,neg_neg]
  rw [← neutral_width α,
    KFCausalReciprocalGaussianDomain.profile_squeeze,charged_width,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -squeezeParameter/2+squeezeParameter/2=0 by ring,
    Real.exp_zero,Complex.ofReal_one,one_mul]

def output (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) : Hilbert :=
  (Real.exp (-squeezeParameter/2):ℂ) • transport (-squeezeParameter)
    (KFCausalClockFloorSourcedSpectral.shiftedOutput ε a α (α/128) hε ha hα
      (base_positive α hα) (base_bound α hα) 1 0 0 h hb)

theorem output_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    (state ε a α hε ha hα,output ε a α hε ha hα h hb) ∈
      (orderedExponential ε hε h).graph :=
  (orderedExponential ε hε h).graph.smul_mem _
    (KFCausalReciprocalSqueezeExponential.ordered_graph_squeeze ε hε h
      (-squeezeParameter) _ _
      (KFCausalClockFloorSourcedSpectral.state_ordered_graph ε a α (α/128)
        hε ha hα (base_positive α hα) (base_bound α hα) 1 0 0 h hb))

theorem spectral_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    (inverseL ε hε (state ε a α hε ha hα),output ε a α hε ha hα h hb) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  (ordered_graph_iff ε hε h _ _).mp (output_graph ε a α hε ha hα h hb)

theorem full_spectral_graph (h : ℝ) (hb : |2*h| ≤ 2*Real.pi*ε/3) :
    (inverseL ε hε (state ε a α hε ha hα),output ε a α hε ha hα (2*h) hb) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := spectral_graph ε a α hε ha hα (2*h) hb
  have hr := (KFCausalClockFloorVacuumSquare.exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using hr

#print axioms charged_width
#print axioms neutral_width
#print axioms state_coe
#print axioms output_graph
#print axioms spectral_graph
#print axioms full_spectral_graph
end
end UnifiedTheory.Audit.KFCausalBroadReciprocalGaussian
