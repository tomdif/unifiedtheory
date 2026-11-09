/- Actual radial complement cutoffs preserve the literal original
potential-output closure, and converge in its graph norm. The proof
transports original reference sources first and then closes the graph;
it imposes no separate natural-factor or Hamiltonian domain premise. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventSections
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaGrowing
import UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotential
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound growingAction growingActionLp)
open KFCausalClockFloorRadialYosidaEnergy (factorOutput)
open KFCausalJointGraphBoundedCorrection (outputMap)
open KFCausalClockFloorRadialResolventRegularizer (action)
open KFCausalClockFloorRadialResolventSections (outputAction outputActionLp)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound)

private theorem range_closure_transport
    {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (j : V →L[ℂ] X) (b : V →L[ℂ] Y) (d : X →L[ℂ] X) (l : Y →L[ℂ] Y)
    (hs : ∀ u, ∃ v, j v=d (j u) ∧ b v=l (b u))
    (x : X) (y : Y) (hxy : (x,y) ∈ (j.prod b).toLinearMap.range.topologicalClosure) :
    (d x,l y) ∈ (j.prod b).toLinearMap.range.topologicalClosure := by
  let S := (j.prod b).toLinearMap.range
  let P := d.prodMap l
  have hS : S ≤ S.topologicalClosure.comap P.toLinearMap := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hvJ,hvB⟩ := hs u
    exact S.le_topologicalClosure ⟨v,Prod.ext hvJ hvB⟩
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage P.continuous) hxy

variable (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
  (hb : |h|≤Real.pi*ε/3) (hh : h≠0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "A" => KFCausalClockFloorRadialYosidaOrderedTransport.shifted
  ε hε h N hN (-h/2) (shift_bound ε h hb)
local notation "R" => outputMap (fun _ : Fin 8=>(A))
def yosidaOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  ContinuousLinearMap.compLpL 2 angleMeasure R
local notation "L" => yosidaOutputLp ε hε h N hN hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RB" => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k
local notation "PB" => KFCausalClockFloorPotentialOutputClosure.potentialMap ε hε h hh hw m g k
local notation "T" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k

private theorem selected_transport (z : EnergyOutputSpace) :
    orderedOutputLp (growingActionLp ε hε h N hN hb z)=L (orderedOutputLp z) := by
  apply Lp.ext
  filter_upwards [orderedOutput.coeFn_compLp (growingActionLp ε hε h N hN hb z),
    (growingAction ε hε h N hN hb).coeFn_compLp z,
    (R).coeFn_compLp (orderedOutputLp z),orderedOutput.coeFn_compLp z]
      with θ h1 h2 h3 h4
  change orderedOutput.compLp (growingActionLp ε hε h N hN hb z) θ=
    (R).compLp (orderedOutputLp z) θ
  rw [h1,h3]
  change orderedOutput ((growingAction ε hε h N hN hb).compLp z θ)=
    (R) (orderedOutput.compLp z θ)
  rw [h2,h4]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [orderedOutput,KFCausalFiniteOutputRescaling.selected_apply,
    KFCausalClockFloorRadialYosidaReference.growingAction_apply,factorOutput,outputMap]

private theorem yosida_graph (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z)∈(T).graph) : (M f,L z)∈(T).graph := by
  have hs : ∀ u : RV, ∃ v : RV, RJ v=M (RJ u) ∧ PB v=L (PB u) := by
    intro u
    obtain ⟨v,hj,hb'⟩ := KFCausalClockFloorRadialYosidaGrowing.reference_stability
      ε hε h N hN hb hh m g k u
    refine ⟨v,hj,?_⟩
    simp only [KFCausalClockFloorPotentialOutputClosure.potentialMap,
      ContinuousLinearMap.comp_apply,hb']
    exact selected_transport ε hε h N hN hb (RB u)
  rw [KFCausalClockFloorPotentialOutputClosure.operator_graph,
    KFCausalClockFloorPotentialOutputClosure.initialGraph] at hz ⊢
  exact range_closure_transport (RJ) (PB) (M) (L) hs f z hz

private theorem output_complement (z : EnergyOutputSpace) :
    z-(N⁻¹:ℂ) • L z=outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb) z := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub z ((N⁻¹:ℂ) • L z),Lp.coeFn_smul (N⁻¹:ℂ) (L z),
    (R).coeFn_compLp z,
    (outputAction ε hε h N hN (-h/2) (shift_bound ε h hb)).coeFn_compLp z]
      with θ hs hc hR hJ
  change (z-(N⁻¹:ℂ) • L z) θ=(outputAction ε hε h N hN (-h/2) (shift_bound ε h hb)).compLp z θ
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hc]
  simp only [Pi.smul_apply]
  change z θ-(N⁻¹:ℂ) • (R).compLp z θ=(outputAction ε hε h N hN (-h/2) (shift_bound ε h hb)).compLp z θ
  rw [hR,hJ]
  apply PiLp.ext
  intro i
  rfl

theorem graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z)∈(T).graph) :
    (action ε hε h N hN f,outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb) z)∈(T).graph := by
  have hm := yosida_graph ε hε h N hN hb hh m g k f z hz
  have he := (T).graph.sub_mem hz ((T).graph.smul_mem (N⁻¹:ℂ) hm)
  change (f-(N⁻¹:ℂ) • M f,z-(N⁻¹:ℂ) • L z)∈(T).graph at he
  rw [output_complement ε hε h N hN hb] at he
  exact he

def formAction : PV →L[ℂ] PV :=
  KFCausalClosedGraphDiagonalAction.action PD (action ε hε h N hN)
    (outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb))
    (graph_action ε hε h N hN hb hh m g k)

theorem formAction_embedding (u : PV) :
    KFCausalClosedGraphForm.embedding PD (formAction ε hε h N hN hb hh m g k u)=
      action ε hε h N hN (KFCausalClosedGraphForm.embedding PD u) := rfl

theorem formAction_output (u : PV) :
    KFCausalClosedGraphForm.energyOutput PD (formAction ε hε h N hN hb hh m g k u)=
      outputActionLp ε hε h N hN (-h/2) (shift_bound ε h hb)
        (KFCausalClosedGraphForm.energyOutput PD u) := rfl

theorem domain_action (f : Hilbert) (hf : f∈(T).domain) :
    action ε hε h N hN f∈(T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (graph_action ε hε h N hN hb hh m g k f _ ((T).mem_graph ⟨f,hf⟩))

theorem graph_sequence_tendsto (f : Hilbert) (z : EnergyOutputSpace) :
    Tendsto (fun n : ℕ=>(action ε hε h ((n:ℝ)+1) (by positivity) f,
      outputActionLp ε hε h ((n:ℝ)+1) (by positivity) (-h/2) (shift_bound ε h hb) z))
      atTop (𝓝 (f,z)) :=
  (KFCausalClockFloorRadialResolventRegularizer.sequence_tendsto ε hε h f).prodMk_nhds
    (KFCausalClockFloorRadialResolventSections.output_section_tendsto
      ε hε h (-h/2) (shift_bound ε h hb) z)

#print axioms graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms domain_action
#print axioms graph_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotential
