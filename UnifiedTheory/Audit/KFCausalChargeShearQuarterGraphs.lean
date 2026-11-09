/- Four charge-conjugated actual shear momenta cancel on their common
graph domain when the state has a differentiable mixed representative.
The graph hypotheses are explicit. No weighted-force sign or invariance
of the Hamiltonian domain is claimed. -/
import UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity
import UnifiedTheory.Audit.KFCausalTransverseShearDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (JointHilbert)
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow
open UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (flowEquiv flow_preserves_volume momentumScale momentumScale_ne_zero)
open UnifiedTheory.Audit.KFCausalMixedCircleAction (action action_coe)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearGroup shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution (momentum_graph_iff inverse_coefficient)

def conjugateTransport (c : ℝ) (hc : c ≠ 0) (θ t : ℝ) :
    JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  (action c hc θ).trans ((jointTransport t).trans (action c hc (-θ)))

theorem rotatedFlow_quasiMeasurePreserving (c : ℝ) (hc : c ≠ 0) (θ t : ℝ) :
    Measure.QuasiMeasurePreserving (rotatedFlow c hc θ t) volume volume :=
  (flow_preserves_volume c hc θ).quasiMeasurePreserving.comp
    ((flow_quasiMeasurePreserving t).comp (flow_preserves_volume c hc (-θ)).quasiMeasurePreserving)

theorem conjugateTransport_coe (c : ℝ) (hc : c ≠ 0) (θ t : ℝ) (f : JointHilbert 2 4) :
    conjugateTransport c hc θ t f =ᵐ[volume] fun x => f (rotatedFlow c hc θ t x) := by
  filter_upwards [action_coe c hc (-θ) (jointTransport t (action c hc θ f)),
    (flow_preserves_volume c hc (-θ)).quasiMeasurePreserving.ae
      (jointTransport_coe t (action c hc θ f)),
    ((flow_quasiMeasurePreserving t).comp (flow_preserves_volume c hc (-θ)).quasiMeasurePreserving).ae
      (action_coe c hc θ f)] with x ha hb hd
  exact ha.trans (hb.trans hd)

theorem derivative_representative (c : ℝ) (hc : c ≠ 0) (θ : ℝ)
    (f v : JointHilbert 2 4) (φ : Space → ℂ) (hφ : f =ᵐ[volume] φ)
    (hs : Differentiable ℝ φ)
    (hd : HasDerivAt (fun t => conjugateTransport c hc θ t f) v 0) :
    v =ᵐ[volume] differential c hc θ φ := by
  apply KFCausalLpDerivativeRepresentative.derivative_representative
    (fun t => conjugateTransport c hc θ t f) v
    (fun t x => φ (rotatedFlow c hc θ t x)) (differential c hc θ φ) _ hd
    (fun x => expression_derivative c hc θ φ x (hs x))
  intro t
  filter_upwards [conjugateTransport_coe c hc θ t f,
    (rotatedFlow_quasiMeasurePreserving c hc θ t).ae hφ] with x ha hb
  exact ha.trans hb

def reverseOutput (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (g : Hilbert) : JointHilbert 2 4 :=
  action (momentumScale h) (momentumScale_ne_zero h hh) (-θ) (chargeCoordinates g)

theorem physical_graph_derivative (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert)
    (hfg : (KFCausalPhysicalCircleAction.action h hh θ f,g) ∈ (shearMomentum h).graph) :
    HasDerivAt (fun t => conjugateTransport (momentumScale h) (momentumScale_ne_zero h hh)
      θ t (chargeCoordinates f)) ((Complex.I/(h:ℂ)) • reverseOutput h hh θ g) 0 := by
  let A := action (momentumScale h) (momentumScale_ne_zero h hh) (-θ)
  let Q := chargeCoordinates.trans A
  have hd := ((Q : Hilbert →L[ℂ] JointHilbert 2 4).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff shearGroup h hh _ g).mp hfg)
  change HasDerivAt (fun t => A (chargeCoordinates (KFCausalTransverseShearTransport.transport t
    (KFCausalPhysicalCircleAction.action h hh θ f))))
    (A (chargeCoordinates ((Complex.I/(h:ℂ)) • g))) 0 at hd
  simpa only [physical_charge_transport,KFCausalPhysicalCircleAction.action_coordinates,map_smul,
    conjugateTransport,LinearIsometryEquiv.trans_apply,reverseOutput,A] using hd

theorem physical_graph_representative (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert)
    (φ : Space → ℂ) (hφ : chargeCoordinates f =ᵐ[volume] φ) (hs : Differentiable ℝ φ)
    (hfg : (KFCausalPhysicalCircleAction.action h hh θ f,g) ∈ (shearMomentum h).graph) :
    reverseOutput h hh θ g =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*differential (momentumScale h) (momentumScale_ne_zero h hh) θ φ x := by
  have he := derivative_representative (momentumScale h) (momentumScale_ne_zero h hh) θ
    (chargeCoordinates f) ((Complex.I/(h:ℂ)) • reverseOutput h hh θ g) φ hφ hs
    (physical_graph_derivative h hh θ f g hfg)
  filter_upwards [he,Lp.coeFn_smul (Complex.I/(h:ℂ)) (reverseOutput h hh θ g)] with x hx hg
  rw [hg] at hx
  change (Complex.I/(h:ℂ))*reverseOutput h hh θ g x = _ at hx
  calc
    _ = ((-Complex.I*(h:ℂ))*(Complex.I/(h:ℂ)))*reverseOutput h hh θ g x := by
      rw [mul_comm (-Complex.I*(h:ℂ)),inverse_coefficient h hh,one_mul]
    _ = _ := by rw [mul_assoc,hx]

theorem four_graph_outputs_cancel (h : ℝ) (hh : h ≠ 0) (f g₀ g₁ g₂ g₃ : Hilbert)
    (φ : Space → ℂ) (hφ : chargeCoordinates f =ᵐ[volume] φ) (hs : Differentiable ℝ φ)
    (h₀ : (KFCausalPhysicalCircleAction.action h hh 0 f,g₀) ∈ (shearMomentum h).graph)
    (h₁ : (KFCausalPhysicalCircleAction.action h hh (Real.pi/2) f,g₁) ∈ (shearMomentum h).graph)
    (h₂ : (KFCausalPhysicalCircleAction.action h hh Real.pi f,g₂) ∈ (shearMomentum h).graph)
    (h₃ : (KFCausalPhysicalCircleAction.action h hh (-Real.pi/2) f,g₃) ∈ (shearMomentum h).graph) :
    reverseOutput h hh 0 g₀ + reverseOutput h hh (Real.pi/2) g₁ +
      reverseOutput h hh Real.pi g₂ + reverseOutput h hh (-Real.pi/2) g₃ = 0 := by
  let v₀ := reverseOutput h hh 0 g₀
  let v₁ := reverseOutput h hh (Real.pi/2) g₁
  let v₂ := reverseOutput h hh Real.pi g₂
  let v₃ := reverseOutput h hh (-Real.pi/2) g₃
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (v₀+v₁+v₂) v₃,Lp.coeFn_add (v₀+v₁) v₂,Lp.coeFn_add v₀ v₁,
    Lp.coeFn_zero ℂ 2 (volume : Measure Space),
    physical_graph_representative h hh 0 f g₀ φ hφ hs h₀,
    physical_graph_representative h hh (Real.pi/2) f g₁ φ hφ hs h₁,
    physical_graph_representative h hh Real.pi f g₂ φ hφ hs h₂,
    physical_graph_representative h hh (-Real.pi/2) f g₃ φ hφ hs h₃] with x ha hb hc hz h0 h1 h2 h3
  change (v₀+v₁+v₂+v₃) x = _
  simp only [ha,hb,hc,Pi.add_apply,hz,Pi.zero_apply,v₀,v₁,v₂,v₃,h0,h1,h2,h3,
    ← mul_add,differential_quarters,mul_zero]

#print axioms rotatedFlow_quasiMeasurePreserving
#print axioms conjugateTransport_coe
#print axioms derivative_representative
#print axioms physical_graph_derivative
#print axioms physical_graph_representative
#print axioms four_graph_outputs_cancel
end
end UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs
