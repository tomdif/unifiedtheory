/- The actual self-adjoint paired-squeeze momentum, with its maximal
strong derivative domain and an actual graph core. Charge rotations
preserve the entire graph. No Hamiltonian-evolution virial is assumed. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity
import UnifiedTheory.Audit.KFCausalChargeSqueezeJointFlow
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

def squeezeGroup : StrongUnitaryGroup Hilbert where
  action := transport
  initial := transport_initial
  compose := transport_compose
  continuous_orbit := transport_strong_continuous

def squeezeMomentum (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert := momentum squeezeGroup h

theorem squeeze_domain (h : ℝ) (f : Hilbert) :
    f ∈ (squeezeMomentum h).domain ↔ DifferentiableAt ℝ (fun a => transport a f) 0 := Iff.rfl

theorem squeeze_dense (h : ℝ) : Dense ((squeezeMomentum h).domain : Set Hilbert) :=
  momentum_dense squeezeGroup h

theorem squeeze_selfAdjoint (h : ℝ) (hh : h ≠ 0) : IsSelfAdjoint (squeezeMomentum h) :=
  momentum_selfAdjoint squeezeGroup h hh

theorem squeeze_closed (h : ℝ) (hh : h ≠ 0) : (squeezeMomentum h).IsClosed :=
  (squeeze_selfAdjoint h hh).isClosed

theorem squeeze_graph_derivative (h : ℝ) (hh : h ≠ 0) (f g : Hilbert) :
    (f,g) ∈ (squeezeMomentum h).graph ↔
      HasDerivAt (fun a => transport a f) ((Complex.I/(h:ℂ)) • g) 0 :=
  momentum_graph_iff squeezeGroup h hh f g

theorem squeeze_strong_derivative (h : ℝ) (hh : h ≠ 0)
    (f : (squeezeMomentum h).domain) (a : ℝ) :
    HasDerivAt (fun b => transport b (f:Hilbert))
      ((Complex.I/(h:ℂ)) • transport a (squeezeMomentum h f)) a :=
  momentum_orbit_derivative squeezeGroup h hh f a

theorem squeeze_average_core (h : ℝ) (hh : h ≠ 0) :
    (Submodule.span ℂ (averagedGraph squeezeGroup h)).topologicalClosure = (squeezeMomentum h).graph :=
  averagedGraph_span_closure squeezeGroup h hh

theorem bounded_commutation (h : ℝ) (hh : h ≠ 0) (B : Hilbert →L[ℂ] Hilbert)
    (hc : ∀ (a : ℝ) (f : Hilbert), B (transport a f) = transport a (B f))
    (f g : Hilbert) (hfg : (f,g) ∈ (squeezeMomentum h).graph) :
    (B f,B g) ∈ (squeezeMomentum h).graph := by
  apply (squeeze_graph_derivative h hh _ _).mpr
  have hd := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((squeeze_graph_derivative h hh f g).mp hfg)
  change HasDerivAt (fun a => B (transport a f)) (B ((Complex.I/(h:ℂ)) • g)) 0 at hd
  simpa only [hc,map_smul] using hd

theorem squeeze_charge_graph (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (squeezeMomentum h).graph) :
    (KFCausalPhysicalCircleAction.action h hh θ f,KFCausalPhysicalCircleAction.action h hh θ g) ∈
      (squeezeMomentum h).graph :=
  bounded_commutation h hh (KFCausalPhysicalCircleAction.action h hh θ)
    (fun a x => (KFCausalChargeSqueezeJointFlow.physical_charge a h hh θ x).symm) f g hfg

theorem squeeze_charge_domain (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    KFCausalPhysicalCircleAction.action h hh θ f ∈ (squeezeMomentum h).domain ↔
      f ∈ (squeezeMomentum h).domain := by
  have forward (φ : ℝ) (x : Hilbert) (hx : x ∈ (squeezeMomentum h).domain) :
      KFCausalPhysicalCircleAction.action h hh φ x ∈ (squeezeMomentum h).domain := by
    obtain ⟨y,hy⟩ := LinearPMap.mem_domain_iff.mp hx
    exact LinearPMap.mem_domain_of_mem_graph (squeeze_charge_graph h hh φ x y hy)
  constructor
  · intro hf
    simpa only [KFCausalPhysicalCircleAction.action_reverse] using forward (-θ) _ hf
  · exact forward θ f

#print axioms squeeze_domain
#print axioms squeeze_dense
#print axioms squeeze_selfAdjoint
#print axioms squeeze_closed
#print axioms squeeze_graph_derivative
#print axioms squeeze_strong_derivative
#print axioms squeeze_average_core
#print axioms bounded_commutation
#print axioms squeeze_charge_graph
#print axioms squeeze_charge_domain

end
end UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator
