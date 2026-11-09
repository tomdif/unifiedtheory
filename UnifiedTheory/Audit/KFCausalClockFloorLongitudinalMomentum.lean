/- The optional clock-floor transport has a densely defined self-adjoint
longitudinal momentum. Its maximal domain is actual strong L2
differentiability. No full Hamiltonian or cutoff limit is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
import UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumCore

def clockGroup : StrongUnitaryGroup Hilbert where
  action := translation
  initial := translation_initial
  compose := translation_compose
  continuous_orbit := translation_strong_continuous

def coupledGroup (ε : ℝ) (hε : 0 < ε) : StrongUnitaryGroup Hilbert where
  action := transport ε hε
  initial := transport_initial ε hε
  compose := transport_compose ε hε
  continuous_orbit := transport_strong_continuous ε hε

def clockMomentum (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert := momentum clockGroup hbar

def longitudinalMomentum (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  momentum (coupledGroup ε hε) hbar

theorem longitudinal_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) :
    f ∈ (longitudinalMomentum ε hε hbar).domain ↔
      DifferentiableAt ℝ (fun t => transport ε hε t f) 0 := Iff.rfl

theorem longitudinal_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    Dense ((longitudinalMomentum ε hε hbar).domain : Set Hilbert) :=
  momentum_dense (coupledGroup ε hε) hbar

theorem longitudinal_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    IsSelfAdjoint (longitudinalMomentum ε hε hbar) :=
  momentum_selfAdjoint (coupledGroup ε hε) hbar hh

theorem longitudinal_closed (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    (longitudinalMomentum ε hε hbar).IsClosed :=
  (longitudinal_selfAdjoint ε hε hbar hh).isClosed

theorem longitudinal_strong_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : (longitudinalMomentum ε hε hbar).domain) (t : ℝ) :
    HasDerivAt (fun s => transport ε hε s (f:Hilbert))
      ((Complex.I/(hbar:ℂ)) • transport ε hε t (longitudinalMomentum ε hε hbar f)) t :=
  momentum_orbit_derivative (coupledGroup ε hε) hbar hh f t

theorem longitudinal_domain_invariant (ε : ℝ) (hε : 0 < ε) (hbar t : ℝ)
    (f : (longitudinalMomentum ε hε hbar).domain) :
    transport ε hε t f ∈ (longitudinalMomentum ε hε hbar).domain :=
  (domainAction (coupledGroup ε hε) t f).property

theorem longitudinal_average (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) (a : ℝ) :
    longitudinalMomentum ε hε hbar (averageState (coupledGroup ε hε) hbar f a) =
      (-Complex.I*(hbar:ℂ)) • (a⁻¹ • (transport ε hε a f-f)) :=
  average_momentum (coupledGroup ε hε) hbar f a

theorem longitudinal_average_tendsto (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    Tendsto (fun a : ℝ => a⁻¹ • (∫ t in 0..a, transport ε hε t f)) (𝓝[≠] 0) (𝓝 f) :=
  average_tendsto (coupledGroup ε hε) f

theorem clock_selfAdjoint (hbar : ℝ) (hh : hbar ≠ 0) : IsSelfAdjoint (clockMomentum hbar) :=
  momentum_selfAdjoint clockGroup hbar hh

theorem longitudinal_average_core (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    (Submodule.span ℂ (averagedGraph (coupledGroup ε hε) hbar)).topologicalClosure =
      (longitudinalMomentum ε hε hbar).graph :=
  averagedGraph_span_closure (coupledGroup ε hε) hbar hh

#print axioms coupledGroup
#print axioms longitudinal_domain
#print axioms longitudinal_dense
#print axioms longitudinal_selfAdjoint
#print axioms longitudinal_closed
#print axioms longitudinal_strong_derivative
#print axioms longitudinal_domain_invariant
#print axioms longitudinal_average
#print axioms longitudinal_average_tendsto
#print axioms clock_selfAdjoint
#print axioms longitudinal_average_core

end
end UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum
