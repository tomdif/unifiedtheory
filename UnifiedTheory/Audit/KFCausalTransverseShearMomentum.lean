/- The actual self-adjoint transverse shear momentum, with maximal strong
L2 domain and a derived graph formula on a canonical common domain. -/
import UnifiedTheory.Audit.KFCausalTransverseShearTransport
import UnifiedTheory.Audit.KFCausalStrongUnitaryProductDerivative
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransverseShearMomentum
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearTransport
open UnifiedTheory.Audit.KFCausalTransverseShearCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumCore
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockGroup clockMomentum)

def shearGroup : StrongUnitaryGroup Hilbert where
  action := transport
  initial := transport_initial
  compose := transport_compose
  continuous_orbit := transport_strong_continuous

def shearMomentum (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert := momentum shearGroup h

theorem shear_domain (h : ℝ) (f : Hilbert) :
    f ∈ (shearMomentum h).domain ↔ DifferentiableAt ℝ (fun t => transport t f) 0 := Iff.rfl

theorem shear_dense (h : ℝ) : Dense ((shearMomentum h).domain : Set Hilbert) :=
  momentum_dense shearGroup h

theorem shear_selfAdjoint (h : ℝ) (hh : h ≠ 0) : IsSelfAdjoint (shearMomentum h) :=
  momentum_selfAdjoint shearGroup h hh

theorem shear_closed (h : ℝ) (hh : h ≠ 0) : (shearMomentum h).IsClosed :=
  (shear_selfAdjoint h hh).isClosed

theorem shear_strong_derivative (h : ℝ) (hh : h ≠ 0)
    (f : (shearMomentum h).domain) (t : ℝ) :
    HasDerivAt (fun s => transport s (f:Hilbert))
      ((Complex.I/(h:ℂ)) • transport t (shearMomentum h f)) t :=
  momentum_orbit_derivative shearGroup h hh f t

theorem shear_average_core (h : ℝ) (hh : h ≠ 0) :
    (Submodule.span ℂ (averagedGraph shearGroup h)).topologicalClosure = (shearMomentum h).graph :=
  averagedGraph_span_closure shearGroup h hh

theorem graph_difference (h : ℝ) (hh : h ≠ 0) (f p q : Hilbert)
    (hp : (f,p) ∈ (clockMomentum h).graph)
    (hq : (coordinates.symm f,q) ∈ (clockMomentum h).graph) :
    (f,coordinates q-p) ∈ (shearMomentum h).graph := by
  have hd := KFCausalStrongUnitaryProductDerivative.conjugate_difference_derivative
    clockGroup coordinates f ((Complex.I/(h:ℂ)) • p) ((Complex.I/(h:ℂ)) • q)
    ((momentum_graph_iff clockGroup h hh _ _).mp hp)
    ((momentum_graph_iff clockGroup h hh _ _).mp hq)
  apply (momentum_graph_iff shearGroup h hh _ _).mpr
  change HasDerivAt (fun t => transport t f) ((Complex.I/(h:ℂ)) • (coordinates q-p)) 0
  change HasDerivAt (fun t => transport t f)
    (coordinates ((Complex.I/(h:ℂ)) • q)-(Complex.I/(h:ℂ)) • p) 0 at hd
  simpa only [map_smul,← smul_sub] using hd

theorem domain_of_clock_domains (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (hf : f ∈ (clockMomentum h).domain)
    (hv : coordinates.symm f ∈ (clockMomentum h).domain) : f ∈ (shearMomentum h).domain := by
  obtain ⟨p,hp⟩ := LinearPMap.mem_domain_iff.mp hf
  obtain ⟨q,hq⟩ := LinearPMap.mem_domain_iff.mp hv
  exact LinearPMap.mem_domain_of_mem_graph (graph_difference h hh f p q hp hq)

#print axioms shearGroup
#print axioms shear_domain
#print axioms shear_dense
#print axioms shear_selfAdjoint
#print axioms shear_closed
#print axioms shear_strong_derivative
#print axioms shear_average_core
#print axioms graph_difference
#print axioms domain_of_clock_domains
end
end UnifiedTheory.Audit.KFCausalTransverseShearMomentum
