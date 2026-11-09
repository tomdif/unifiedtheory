/- An actual graph core for exp(L/2) whose inputs and outputs both lie
in the maximal longitudinal momentum domain. It is constructed from the
existing Gaussian packets, using both signs of their exponential moments. -/
import UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph
import UnifiedTheory.Audit.KFCausalClockFloorGaussianCore
import UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumCore
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorGaussianCore
open UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl (two_exponential_domain)
open UnifiedTheory.Audit.KFCausalClockFloorPlanckSign (exponential_sign_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "L" => longitudinalMomentum ε hε h
local notation "E" => longitudinalExponential ε hε h (1/2)

def packetInput (v : Space) : Hilbert := (packet ε hε 0 v).1
def packetOutput (a : ℝ) (v : Space) : Hilbert := (packet ε hε (2*a*h) v).2

theorem packet_exponential_graph (a : ℝ) (v : Space) :
    (packetInput ε hε v,packetOutput ε hε h a v) ∈ (longitudinalExponential ε hε h a).graph := by
  have hg := packet_mem_graph ε hε (2*a*h) v
  change (packetInput ε hε v,packetOutput ε hε h a v) ∈
    (longitudinalExponential ε hε (2*a*h) (1/2)).graph at hg
  rw [longitudinal_exponential_graph] at hg ⊢
  filter_upwards [hg] with k hk
  have he : (1/2:ℝ)*symbol (2*a*h) k = a*symbol h k := by unfold symbol; ring
  simpa only [he] using hk

theorem output_exponential_graph (a b : ℝ) (v : Space) :
    (packetOutput ε hε h a v,packetOutput ε hε h (a+b) v) ∈
      (longitudinalExponential ε hε h b).graph := by
  have ha := packet_exponential_graph ε hε h a v
  have hab := packet_exponential_graph ε hε h (a+b) v
  rw [longitudinal_exponential_graph] at ha hab ⊢
  filter_upwards [ha,hab] with k hk hj
  rw [hk,hj,show (a+b)*symbol h k = b*symbol h k+a*symbol h k by ring,
    Real.exp_add,Complex.ofReal_mul,mul_assoc]

theorem packet_input_momentum_domain (hne : h ≠ 0) (v : Space) : packetInput ε hε v ∈ (L).domain :=
  two_exponential_domain ε hε h hne _ _ _ (packet_exponential_graph ε hε h (1/2) v)
    ((exponential_sign_graph ε hε h (1/2) _ _).mpr (packet_exponential_graph ε hε h (-(1/2)) v))

theorem packet_output_momentum_domain (hne : h ≠ 0) (a : ℝ) (v : Space) :
    packetOutput ε hε h a v ∈ (L).domain :=
  two_exponential_domain ε hε h hne _ _ _ (output_exponential_graph ε hε h a (1/2) v)
    ((exponential_sign_graph ε hε h (1/2) _ _).mpr (output_exponential_graph ε hε h a (-(1/2)) v))

def regularGraph : Submodule ℂ (Hilbert × Hilbert) := (E).graph ⊓ (L).domain.prod (L).domain

theorem packet_mem_regular (hne : h ≠ 0) (v : Space) : packet ε hε h v ∈ regularGraph ε hε h := by
  refine ⟨packet_mem_graph ε hε h v,packet_input_momentum_domain ε hε h hne v,?_⟩
  have he : 2*(1/2:ℝ)*h = h := by ring
  simpa only [packetOutput,he] using packet_output_momentum_domain ε hε h hne (1/2) v

theorem regular_graph_core (hne : h ≠ 0) :
    (regularGraph ε hε h).topologicalClosure = (E).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1)
      (longitudinal_exponential_closed ε hε h (1/2))
  · have hi : Submodule.span ℂ (Set.range (packet ε hε h)) ≤ regularGraph ε hε h := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      exact packet_mem_regular ε hε h hne v
    have hc := Submodule.topologicalClosure_mono hi
    rw [graph_core] at hc
    exact hc

#print axioms packet_exponential_graph
#print axioms output_exponential_graph
#print axioms packet_input_momentum_domain
#print axioms packet_output_momentum_domain
#print axioms packet_mem_regular
#print axioms regular_graph_core
end
end UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumCore
