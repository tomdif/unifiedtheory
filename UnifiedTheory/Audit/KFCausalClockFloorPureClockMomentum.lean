/- The selfadjoint pure-clock momentum is constructed from the complete
unitary clock-only flow. Its maximal graph is unitarily equivalent to the
canonical clock-momentum graph. No Hamiltonian-domain premise is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCore
import UnifiedTheory.Audit.KFCausalCanonicalClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockGroup clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)

def pureGroup (ε : ℝ) (hε : 0 < ε) : StrongUnitaryGroup Hilbert where
  action := transport ε hε
  initial := transport_initial ε hε
  compose := transport_compose ε hε
  continuous_orbit := transport_strong_continuous ε hε

def pureMomentum (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  momentum (pureGroup ε hε) hbar

theorem pure_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) :
    f ∈ (pureMomentum ε hε hbar).domain ↔
      DifferentiableAt ℝ (fun t => transport ε hε t f) 0 := Iff.rfl

theorem pure_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    Dense ((pureMomentum ε hε hbar).domain : Set Hilbert) :=
  momentum_dense (pureGroup ε hε) hbar

theorem pure_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    IsSelfAdjoint (pureMomentum ε hε hbar) :=
  momentum_selfAdjoint (pureGroup ε hε) hbar hh

theorem pure_closed (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    (pureMomentum ε hε hbar).IsClosed :=
  (pure_selfAdjoint ε hε hbar hh).isClosed

theorem pure_strong_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : (pureMomentum ε hε hbar).domain) (t : ℝ) :
    HasDerivAt (fun s => transport ε hε s (f:Hilbert))
      ((Complex.I/(hbar:ℂ)) • transport ε hε t (pureMomentum ε hε hbar f)) t :=
  momentum_orbit_derivative (pureGroup ε hε) hbar hh f t

theorem pure_domain_invariant (ε : ℝ) (hε : 0 < ε) (hbar t : ℝ)
    (f : (pureMomentum ε hε hbar).domain) :
    transport ε hε t f ∈ (pureMomentum ε hε hbar).domain :=
  (domainAction (pureGroup ε hε) t f).property

theorem pure_average (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) (a : ℝ) :
    pureMomentum ε hε hbar (averageState (pureGroup ε hε) hbar f a) =
      (-Complex.I*(hbar:ℂ)) • (a⁻¹ • (transport ε hε a f-f)) :=
  average_momentum (pureGroup ε hε) hbar f a

theorem pure_average_tendsto (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    Tendsto (fun a : ℝ => a⁻¹ • (∫ t in 0..a, transport ε hε t f)) (𝓝[≠] 0) (𝓝 f) :=
  average_tendsto (pureGroup ε hε) f

theorem pure_average_core (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (averagedGraph (pureGroup ε hε) hbar)).topologicalClosure =
      (pureMomentum ε hε hbar).graph :=
  averagedGraph_span_closure (pureGroup ε hε) hbar hh

theorem coordinates_derivative_iff (ε : ℝ) (hε : 0 < ε) (f g : Hilbert) :
    HasDerivAt (fun t => transport ε hε t (coordinates ε hε f)) (coordinates ε hε g) 0 ↔
      HasDerivAt (fun t => translation t f) g 0 := by
  constructor
  · intro hd
    have hh := (((coordinates ε hε).symm : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => (coordinates ε hε).symm (transport ε hε t (coordinates ε hε f)))
      ((coordinates ε hε).symm (coordinates ε hε g)) 0 at hh
    simpa only [transport_apply,LinearIsometryEquiv.symm_apply_apply] using hh
  · intro hd
    have hh := ((coordinates ε hε : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => coordinates ε hε (translation t f)) (coordinates ε hε g) 0 at hh
    simpa only [transport_apply,LinearIsometryEquiv.symm_apply_apply] using hh

theorem momentum_graph_conjugacy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f g : Hilbert) :
    (f,g) ∈ (clockMomentum hbar).graph ↔
      (coordinates ε hε f,coordinates ε hε g) ∈ (pureMomentum ε hε hbar).graph := by
  change (f,g) ∈ (KFCausalUnitaryMomentumSelfAdjoint.momentum clockGroup hbar).graph ↔
    (coordinates ε hε f,coordinates ε hε g) ∈
      (KFCausalUnitaryMomentumSelfAdjoint.momentum (pureGroup ε hε) hbar).graph
  rw [momentum_graph_iff _ hbar hh,momentum_graph_iff _ hbar hh]
  change HasDerivAt (fun t => translation t f) ((Complex.I/(hbar:ℂ)) • g) 0 ↔
    HasDerivAt (fun t => transport ε hε t (coordinates ε hε f))
      ((Complex.I/(hbar:ℂ)) • coordinates ε hε g) 0
  rw [← map_smul (coordinates ε hε)]
  exact (coordinates_derivative_iff ε hε f ((Complex.I/(hbar:ℂ)) • g)).symm

theorem momentum_domain_conjugacy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : Hilbert) :
    f ∈ (clockMomentum hbar).domain ↔
      coordinates ε hε f ∈ (pureMomentum ε hε hbar).domain := by
  constructor
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((momentum_graph_conjugacy ε hε hbar hh f (clockMomentum hbar ⟨f,hf⟩)).mp
        ((clockMomentum hbar).mem_graph ⟨f,hf⟩))
  · intro hf
    let g := pureMomentum ε hε hbar ⟨coordinates ε hε f,hf⟩
    have hg : (coordinates ε hε f,coordinates ε hε ((coordinates ε hε).symm g)) ∈
        (pureMomentum ε hε hbar).graph := by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (pureMomentum ε hε hbar).mem_graph ⟨coordinates ε hε f,hf⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((momentum_graph_conjugacy ε hε hbar hh f ((coordinates ε hε).symm g)).mpr hg)

theorem graph_fourier (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (f g : Hilbert) :
    (f,g) ∈ (pureMomentum ε hε h).graph ↔
      KFCausalEuclideanConfiguration.fourierCoordinates ((coordinates ε hε).symm g) =ᵐ[volume]
        fun k => (KFCausalClockFloorFourierMultiplier.symbol h k:ℂ)*
          KFCausalEuclideanConfiguration.fourierCoordinates ((coordinates ε hε).symm f) k := by
  have he := momentum_graph_conjugacy ε hε h hne ((coordinates ε hε).symm f)
    ((coordinates ε hε).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm.trans (KFCausalCanonicalClockDerivative.clock_graph_fourier h hne _ _)

#print axioms coordinates_derivative_iff
#print axioms momentum_graph_conjugacy
#print axioms momentum_domain_conjugacy
#print axioms graph_fourier

#print axioms pureGroup
#print axioms pure_domain
#print axioms pure_dense
#print axioms pure_selfAdjoint
#print axioms pure_closed
#print axioms pure_strong_derivative
#print axioms pure_domain_invariant
#print axioms pure_average
#print axioms pure_average_tendsto
#print axioms pure_average_core

end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
