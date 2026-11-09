/- The rational radial cutoff preserves the actual closed growing-output
graph. This follows from the original full reference-form transport,
then a bounded-map closure argument; no maximal-factor intersection or
common operator core is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaReference
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClosedGraphDiagonalAction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaGrowing
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaReference (wide_bound growingActionLp)

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
    apply S.le_topologicalClosure
    exact ⟨v,Prod.ext hvJ hvB⟩
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage P.continuous) hxy

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => action ε hε h N hN
local notation "L" => growingActionLp ε hε h N hN hb
local notation "T" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hne hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hne hw m g k
local notation "J" => KFCausalClosedGraphForm.embedding GD
local notation "B" => KFCausalClosedGraphForm.energyOutput GD

local notation "hs" => KFCausalClockFloorRadialYosidaEnergy.energy_bound ε hε h hb
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hne m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hne m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hne m g k 0
open KFCausalClockFloorRadialYosidaReference (averagedAction averagedAction_embedding averagedAction_growing)
open KFCausalAveragedOutputRescaling (growingOutputLp)
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hne hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hne hw m g k 0
local notation "RB" => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hne hw m g k

theorem reference_stability (u : RV) :
    ∃ v : RV, RJ v=action ε hε h N hN (RJ u) ∧
      RB v=growingActionLp ε hε h N hN hb (RB u) := by
  let lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hne hw m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hne hw m g k 0
  let a := Classical.choose (hl u)
  have ha := Classical.choose_spec (hl u)
  refine ⟨lift (averagedAction ε hε h N hN hb hne m g k a),?_,?_⟩
  · have hj : AJ a=RJ u := congrArg RJ ha
    exact (averagedAction_embedding ε hε h N hN hb hne m g k a).trans
      (congrArg (action ε hε h N hN) hj)
  · have he : growingOutputLp (AA a)=RB u := congrArg RB ha
    exact (averagedAction_growing ε hε h N hN hb hne m g k a).trans
      (congrArg (growingActionLp ε hε h N hN hb) he)

theorem growing_graph_action (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (T).graph) : (M f,L y) ∈ (T).graph := by
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hy ⊢
  exact range_closure_transport (RJ) (RB) (M) (L)
    (reference_stability ε hε h N hN hb hne m g k) f y hy

def formAction : GV →L[ℂ] GV :=
  KFCausalClosedGraphDiagonalAction.action GD M L
    (growing_graph_action ε hε h N hN hb hne m g k)

theorem formAction_embedding (u : GV) :
    J (formAction ε hε h N hN hb hne m g k u)=M (J u) := rfl

theorem formAction_output (u : GV) :
    B (formAction ε hε h N hN hb hne m g k u)=L (B u) := rfl

theorem growing_domain_action (f : Hilbert) (hf : f ∈ (T).domain) : M f ∈ (T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (growing_graph_action ε hε h N hN hb hne m g k f _ ((T).mem_graph ⟨f,hf⟩))

#print axioms reference_stability
#print axioms growing_graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms growing_domain_action
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaGrowing
