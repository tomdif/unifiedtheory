/- Clock energy is controlled by the full averaged energy for every averaged
form vector, including nonzero-charge states. The proof retains the natural
unbounded half-clock graph and then transfers to the propagator's form space. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
import UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf (clockHalf_graph_action)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain (form_clock_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t
local notation "L" => sectionMap ε hε h hb hh m g κ t

theorem averaged_clock_graph (u : V) : ∃ y : Hilbert, (J u,y) ∈ (clockHalf ε).graph := by
  let θ := Classical.choose (orbit_lift_ae ε hε h hb hh m g κ t u).exists
  have hθ := Classical.choose_spec (orbit_lift_ae ε hε h hb hh m g κ t u).exists
  let y := Classical.choose (form_clock_bound ε hε h hb m g κ t (L u θ))
  have hy := (Classical.choose_spec (form_clock_bound ε hε h hb m g κ t (L u θ))).1
  change KFCausalClosedGraphForm.embedding B (L u θ) = _ at hθ
  change (KFCausalClosedGraphForm.embedding B (L u θ),y) ∈ (clockHalf ε).graph at hy
  have hy' := (congrArg (fun f : Hilbert => (f,y) ∈ (clockHalf ε).graph) hθ).mp hy
  have hr := clockHalf_graph_action ε hε h hh (-(2*Real.pi*θ)) _ _ hy'
  exact ⟨action h hh (-(2*Real.pi*θ)) y,
    (congrArg (fun f : Hilbert => (f,action h hh (-(2*Real.pi*θ)) y) ∈ (clockHalf ε).graph)
      (action_reverse h hh (2*Real.pi*θ) (J u))).mp hr⟩

theorem averaged_clock_energy (u : V) (y : Hilbert) (hy : (J u,y) ∈ (clockHalf ε).graph) :
    ‖y‖^2 ≤ 2*‖A u‖^2 := by
  have hp : ∀ᵐ θ ∂angleMeasure,
      ‖y‖^2 ≤ 2*‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2 := by
    filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
    let z := Classical.choose (form_clock_bound ε hε h hb m g κ t (L u θ))
    have hz := (Classical.choose_spec (form_clock_bound ε hε h hb m g κ t (L u θ))).1
    have hbound := (Classical.choose_spec (form_clock_bound ε hε h hb m g κ t (L u θ))).2
    change (KFCausalClosedGraphForm.embedding B (L u θ),z) ∈ (clockHalf ε).graph at hz
    change ‖z‖^2 ≤ 2*‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2 at hbound
    have hz' := (congrArg (fun f : Hilbert => (f,z) ∈ (clockHalf ε).graph) hθ).mp hz
    have he := (clockHalf ε).mem_graph_snd_inj' hz'
      (clockHalf_graph_action ε hε h hh (2*Real.pi*θ) _ _ hy) rfl
    have hn : ‖z‖^2 = ‖y‖^2 := (congrArg (fun v : Hilbert => ‖v‖^2) he).trans
      (congrArg (fun x : ℝ => x^2) ((action h hh (2*Real.pi*θ)).norm_map y))
    exact hn.symm.trans_le hbound
  have hi : Integrable (fun θ => ‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2) angleMeasure := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A u))).mp (Lp.memLp (A u))
    apply hi.congr
    filter_upwards [(KFCausalClosedGraphForm.energyOutput B).coeFn_compLp (L u)] with θ hθ
    change ‖(KFCausalClosedGraphForm.energyOutput B).compLp (L u) θ‖^2 = _
    exact congrArg (fun v => ‖v‖^2) hθ
  have he := integral_mono_ae (integrable_const (‖y‖^2)) (hi.const_mul 2) hp
  have hc : (∫ _θ : ℝ, ‖y‖^2 ∂angleMeasure) = ‖y‖^2 := by simp
  have hs : (∫ θ, 2*‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2 ∂angleMeasure) = 2*‖A u‖^2 :=
    (integral_const_mul 2 _).trans (congrArg (fun x : ℝ => 2*x)
      (energy_integral ε hε h hb hh m g κ t u).symm)
  exact hc.symm.trans_le (he.trans_eq hs)

omit hb in
theorem form_clock_graph_bound (hs : |h| ≤ 2*Real.pi*ε/3)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ t) :
    ∃ y : Hilbert,
      (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u,y) ∈ (clockHalf ε).graph ∧
      ‖y‖^2 ≤ 2*‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t u‖^2 := by
  let v := Classical.choose (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  have hv := Classical.choose_spec (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  change KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hs m g κ t v = u at hv
  let y := Classical.choose (averaged_clock_graph ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t v)
  have hy := Classical.choose_spec (averaged_clock_graph ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t v)
  change (embedding ε hε h (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t v,y) ∈ _ at hy
  have he := averaged_clock_energy ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t v y hy
  have hJ := congrArg (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t) hv
  have hA := congrArg (fun z => ‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t z‖^2) hv
  refine ⟨y,?_,?_⟩
  · exact (congrArg (fun f : Hilbert => (f,y) ∈ (clockHalf ε).graph) hJ).mp hy
  · exact he.trans_eq (congrArg (fun x : ℝ => 2*x) hA)

omit hb in
theorem reference_clock_graph_bound (hs : |h| ≤ 2*Real.pi*ε/3)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ 0) :
    ∃ y : Hilbert,
      (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0 u,y) ∈ (clockHalf ε).graph ∧
      ‖y‖^2 ≤ 2*KFCausalClockFloorAveragedTimeControl.timeEnergy ε hε h hh hs m g κ t u := by
  let v := KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hs m g κ 0 t u
  let y := Classical.choose (form_clock_graph_bound ε hε h hh m g κ t hs v)
  have hy := (Classical.choose_spec (form_clock_graph_bound ε hε h hh m g κ t hs v)).1
  have he := (Classical.choose_spec (form_clock_graph_bound ε hε h hh m g κ t hs v)).2
  change (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t
    (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hs m g κ 0 t u),y) ∈ _ at hy
  change ‖y‖^2 ≤ 2*‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t
    (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hs m g κ 0 t u)‖^2 at he
  refine ⟨y,?_,?_⟩
  · exact (congrArg (fun f : Hilbert => (f,y) ∈ (clockHalf ε).graph)
      (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hs m g κ 0 t u)).mp hy
  · exact he.trans_eq (congrArg (fun x : ℝ => 2*x)
      (KFCausalClockFloorAveragedTimeControl.timeEnergy_actual ε hε h hh hs m g κ t u))

#print axioms averaged_clock_graph
#print axioms averaged_clock_energy
#print axioms form_clock_graph_bound
#print axioms reference_clock_graph_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound
