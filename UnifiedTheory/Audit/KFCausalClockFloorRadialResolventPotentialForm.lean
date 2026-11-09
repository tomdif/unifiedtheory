/- Strong convergence of the radial complement regularizers in the actual
completed potential form norm, together with simultaneous membership of
every regularized potential-form vector in the full maximal radial operator
domain and the potential-output closure domain. No potential operator domain
invariance or residual-form reconstruction is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotential

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_graph radial_domain)
open KFCausalClockFloorRadialResolventPotential
  (formAction domain_action graph_sequence_tendsto)

variable (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
  (hb : |h|≤Real.pi*ε/3) (hh : h≠0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

theorem formAction_radial_graph (u : PV) :
    (PJ (formAction ε hε h N hN hb hh m g k u),
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (PJ u))∈(K).graph :=
  radial_graph ε hε h N hN (PJ u)

theorem formAction_radial_domain (u : PV) :
    PJ (formAction ε hε h N hN hb hh m g k u)∈(K).domain :=
  radial_domain ε hε h N hN (PJ u)

theorem domain_intersection_action (f : Hilbert) (hf : f∈(T).domain) :
    action ε hε h N hN f∈(K).domain ∧ action ε hε h N hN f∈(T).domain :=
  ⟨radial_domain ε hε h N hN f,domain_action ε hε h N hN hb hh m g k f hf⟩

theorem form_sequence_tendsto (u : PV) :
    Tendsto (fun n : ℕ=>
      formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u) atTop (𝓝 u) := by
  have hg := graph_sequence_tendsto ε hε h hb (PJ u) (PB u)
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.tendsto
    (WithLp.ofLp u.val)).comp hg

theorem energy_sequence_tendsto (u : PV) :
    Tendsto (fun n : ℕ=>
      ‖PB (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k u)‖^2)
      atTop (𝓝 (‖PB u‖^2)) :=
  (((PB).continuous.tendsto u).comp
    (form_sequence_tendsto ε hε h hb hh m g k u)).norm.pow 2

#print axioms formAction_radial_graph
#print axioms formAction_radial_domain
#print axioms domain_intersection_action
#print axioms form_sequence_tendsto
#print axioms energy_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm
