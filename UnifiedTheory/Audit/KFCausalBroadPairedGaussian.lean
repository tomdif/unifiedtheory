/- A physical mixed-chart Gaussian baseline with common charged width alpha*w.
It is obtained from an actual sourced Gaussian by the paired squeeze, so
its full longitudinal exponential graph is constructed for every w>0.
Choosing w=1/(4W) makes all four charged widths alpha/(4W). -/
import UnifiedTheory.Audit.KFCausalPairedGaussianStates
import UnifiedTheory.Audit.KFCausalPairedSqueezeExponential
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalBroadPairedGaussian
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous clockFunction_memLp)
open KFCausalPairedGaussianStates (quadratic configurationDensity coordinateDensity)
open KFCausalPairedSqueezeFlow
open KFCausalPairedSqueezeTransport
open KFCausalQuarticChargeProfiles (chargedRadius)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)

private theorem exp_square (t : ℝ) : Real.exp (2*t) = (Real.exp t)^2 := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem quadratic_squeeze (t : ℝ) (q : Transverse) :
    chargedRadius (squeeze t q) = quadratic (Real.exp (2*t)) q := by
  simp only [quadratic,exp_square t]
  dsimp [chargedRadius,squeeze,diagonal,offDiagonal]
  rw [Real.exp_neg]
  ring

private theorem neutral_rescaling (β t : ℝ) (q : Transverse) :
    (β*Real.exp (-2*t))*(squeeze t q 4)^2 = β*(q 4)^2 := by
  change (β*Real.exp (-2*t))*(Real.exp t*q 4)^2 = _
  rw [mul_pow,← exp_square]
  calc
    _ = β*(Real.exp (-2*t)*Real.exp (2*t))*q 4^2 := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem profile_squeeze (α β t : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    KFCausalClockFloorCoherentDerivative.physicalProfile 1 0 α (β*Real.exp (-2*t)) 0 g
      (x.1,squeeze t x.2) = configurationDensity α β (Real.exp (2*t)) g x := by
  simp only [KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,zero_mul,
    Complex.exp_zero,one_mul,KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,Pi.zero_apply,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul,
    KFCausalClockFloorShearBounds.physicalGaussian,configurationDensity]
  congr 2
  have hs : (∑ i : Fin 4, (squeeze t x.2 i.castSucc)^2) = chargedRadius (squeeze t x.2) := by
    simp [Fin.sum_univ_succ,chargedRadius]
    ring
  rw [hs,quadratic_squeeze,neutral_rescaling]

def squeezeParameter (w : ℝ) : ℝ := Real.log w/2

theorem charged_width (w : ℝ) (hw : 0 < w) : Real.exp (2*squeezeParameter w) = w := by
  rw [squeezeParameter,show 2*(Real.log w/2)=Real.log w by ring,Real.exp_log hw]

theorem neutral_width (α w : ℝ) (hw : 0 < w) :
    (α*w/128)*Real.exp (-2*squeezeParameter w) = α/128 := by
  rw [show -2*squeezeParameter w=-(2*squeezeParameter w) by ring,
    Real.exp_neg,charged_width w hw]
  field_simp

variable (ε a α w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hw : 0 < w)

include hα in
private theorem base_positive : 0 < α/128 := by positivity
include hα in
private theorem base_bound : 32*(α/128) ≤ α := by linarith

def base : Hilbert :=
  KFCausalClockFloorSourcedClockMomentum.state ε a α (α/128) hε ha hα
    (base_positive α hα) (base_bound α hα) 1 0 0

def state : Hilbert := KFCausalPairedGaussianStates.state α (α*w/128) w hα
  (by positivity) hw (clockFunction ε a) (clockFunction_continuous ε a)
    (clockFunction_memLp ε a hε ha)

theorem state_configuration_coe : state ε a α w hε ha hα hw =ᵐ[volume]
    configurationDensity α (α*w/128) w (clockFunction ε a) :=
  KFCausalPairedGaussianStates.state_configuration_coe _ _ _ _ _ _ _ _ _

theorem state_coordinates_coe (c : ℝ) (hmatch : Real.pi^2/α = α*c^2) :
    KFCausalPhysicalCircleAction.chargeCoordinates (state ε a α w hε ha hα hw) =ᵐ[volume]
      coordinateDensity α (α*w/128) w c (clockFunction ε a) :=
  KFCausalPairedGaussianStates.state_coordinates_coe _ _ _ _ _ _ _ _ _ c hmatch

theorem state_transport : state ε a α w hε ha hα hw =
    (Real.exp (-squeezeParameter w/2):ℂ) •
      transport (-squeezeParameter w) (base ε a α hε ha hα) := by
  apply Lp.ext
  let f := base ε a α hε ha hα
  filter_upwards [state_configuration_coe ε a α w hε ha hα hw,
    Lp.coeFn_smul (Real.exp (-squeezeParameter w/2):ℂ)
      (transport (-squeezeParameter w) f),transport_coe (-squeezeParameter w) f,
    (squeezeFlow_quasiMeasurePreserving (-squeezeParameter w)).ae
      (KFCausalClockFloorSourcedClockMomentum.state_coe ε a α (α/128) hε ha hα
        (base_positive α hα) (base_bound α hα) 1 0 0)] with x hx hc ht hf
  change f (squeezeFlow (-squeezeParameter w) x) = _ at hf
  rw [hx,hc,Pi.smul_apply,smul_eq_mul,ht]
  change _ = (Real.exp (-squeezeParameter w/2):ℂ)*
    ((Real.exp (-(-squeezeParameter w)/2):ℂ)*f (squeezeFlow (-squeezeParameter w) x))
  rw [hf]
  simp only [squeezeFlow_apply,neg_neg]
  rw [← neutral_width α w hw,profile_squeeze,charged_width w hw,
    ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show -squeezeParameter w/2+squeezeParameter w/2=0 by ring,
    Real.exp_zero,Complex.ofReal_one,one_mul]

def output (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) : Hilbert :=
  (Real.exp (-squeezeParameter w/2):ℂ) • transport (-squeezeParameter w)
    (KFCausalClockFloorSourcedSpectral.shiftedOutput ε a α (α/128) hε ha hα
      (base_positive α hα) (base_bound α hα) 1 0 0 h hb)

theorem output_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) :
    (state ε a α w hε ha hα hw,output ε a α w hε ha hα h hb) ∈
      (orderedExponential ε hε h).graph := by
  rw [state_transport]
  exact (orderedExponential ε hε h).graph.smul_mem _
    (KFCausalPairedSqueezeExponential.ordered_graph_squeeze ε hε h
      (-squeezeParameter w) _ _
      (KFCausalClockFloorSourcedSpectral.state_ordered_graph ε a α (α/128)
        hε ha hα (base_positive α hα) (base_bound α hα) 1 0 0 h hb))

theorem full_spectral_graph (h : ℝ) (hb : |2*h| ≤ 2*Real.pi*ε/3) :
    (inverseL ε hε (state ε a α w hε ha hα hw),output ε a α w hε ha hα (2*h) hb) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := (ordered_graph_iff ε hε (2*h) _ _).mp
    (output_graph ε a α w hε ha hα hw (2*h) hb)
  have hr := (KFCausalClockFloorVacuumSquare.exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using hr

#print axioms quadratic_squeeze
#print axioms profile_squeeze
#print axioms charged_width
#print axioms neutral_width
#print axioms state_configuration_coe
#print axioms state_coordinates_coe
#print axioms state_transport
#print axioms output_graph
#print axioms full_spectral_graph
end
end UnifiedTheory.Audit.KFCausalBroadPairedGaussian
