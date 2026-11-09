/- Clock Gaussian actions on the ORIGINAL growing form. Natural graph
transport is passed through the simultaneous weighted graph closure,
then through actual charge sections, and finally through the growing
output closure. No separate maximal-domain intersection is substituted. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingTransport
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
import UnifiedTheory.Audit.KFCausalAveragedFormAction
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClosedGraphDiagonalAction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingForm
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output jointGraph)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorGaussianGrowingTransport (action action_charge forward_graph)
open KFCausalAnalyticClockSecondTransport (firstShift)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalJointGraphBoundedCorrection (outputMap correctionMap)
open KFCausalPhysicalEnergyTransport (growingOutput)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace growingOutputLp)
open KFCausalPhysicalCircleAction (group)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

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

variable (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (y : ℝ) (m g k : ℝ)

def factorOutput (i : Fin 8) : Hilbert →L[ℂ] Hilbert := action ε a ha (y+firstShift h i)
def outputAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε a ha h y)
def growingAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  growingOutput.comp (outputAction ε a ha h y)
def growingActionLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (growingAction ε a ha h y).compLpL 2 angleMeasure

theorem growingAction_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    growingAction ε a ha h y z i=
      if i.val<3 then 0 else action ε a ha (y+firstShift h i) (z i) := by
  simp only [growingAction,ContinuousLinearMap.comp_apply,growingOutput,
    KFCausalFiniteOutputRescaling.selected_apply,outputAction,outputMap,factorOutput]
  split_ifs <;> rfl

local notation "hs" => hamiltonian_bound ε h hb
local notation "BD" => KFCausalClockFloorFormHamiltonian.formData ε hε h hs m g k 0
local notation "BJ" => KFCausalClosedGraphForm.embedding BD
local notation "BA" => KFCausalClosedGraphForm.energyOutput BD

include hh in
private theorem closed_graph (f : Hilbert) (z : Output (Fin 8) Hilbert)
    (hz : (f,z) ∈ (BD).operator.graph) :
    (action ε a ha y f,outputAction ε a ha h y z) ∈ (BD).operator.graph := by
  change (action ε a ha y f,outputAction ε a ha h y z) ∈
    (KFCausalClockFloorJointEnergy.closedEnergy ε hε h modelDirections pointField m g k 0).graph
  change (f,z) ∈ (KFCausalClockFloorJointEnergy.closedEnergy ε hε h modelDirections pointField m g k 0).graph at hz
  rw [KFCausalClockFloorJointEnergy.closedEnergy_graph ε hε h modelDirections pointField m g k 0 hs] at hz ⊢
  have hf (i : Fin 8) (u v : Hilbert)
      (huv : (u,v) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
      (action ε a ha y u,factorOutput ε a ha h y i v+(0 : Hilbert →L[ℂ] Hilbert) u) ∈
        (energyFactor ε hε h modelDirections pointField i).graph := by
    simpa only [ContinuousLinearMap.zero_apply,add_zero] using
      forward_graph ε hε a ha h hh y i u v huv
  have he := KFCausalJointGraphBoundedCorrection.joint_closure
    (energyFactor ε hε h modelDirections pointField) (action ε a ha y)
    (factorOutput ε a ha h y) (fun _ => 0) hf (energyWeight m g k 0) f z hz
  have hc : correctionMap (fun _ : Fin 8 => (0 : Hilbert →L[ℂ] Hilbert)) (energyWeight m g k 0) f=0 := by
    apply PiLp.ext
    intro i
    simp only [correctionMap,ContinuousLinearMap.zero_apply,smul_zero,PiLp.zero_apply]
    rfl
  simpa only [hc,add_zero] using he

private def baseAction : KFCausalClosedGraphForm.FormSpace BD →L[ℂ] KFCausalClosedGraphForm.FormSpace BD :=
  KFCausalClosedGraphDiagonalAction.action BD (action ε a ha y) (outputAction ε a ha h y)
    (closed_graph ε hε a ha h hh hb y m g k)

private theorem base_embedding (u : KFCausalClosedGraphForm.FormSpace BD) :
    BJ (baseAction ε hε a ha h hh hb y m g k u)=action ε a ha y (BJ u) := rfl

private theorem base_growing (u : KFCausalClosedGraphForm.FormSpace BD) :
    growingOutput (BA (baseAction ε hε a ha h hh hb y m g k u))=
      growingAction ε a ha h y (growingOutput (BA u)) := by
  change growingOutput (outputAction ε a ha h y (BA u))=_
  apply PiLp.ext
  intro i
  simp only [growingAction,ContinuousLinearMap.comp_apply,growingOutput,
    KFCausalFiniteOutputRescaling.selected_apply,outputAction,outputMap]
  split_ifs with hi
  · rfl
  · change factorOutput ε a ha h y i (BA u i)=
      factorOutput ε a ha h y i ((KFCausalFiniteOutputRescaling.selected (fun j : Fin 8 => ¬j.val<3) (BA u)) i)
    rw [KFCausalFiniteOutputRescaling.selected_apply,if_pos hi]

local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hh m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hh m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hh m g k 0
local notation "AS" => KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hs hh m g k 0
local notation "BF" => baseAction ε hε a ha h hh hb y m g k

private def averagedAction : AV →L[ℂ] AV := by
  let f : KFCausalClosedGraphForm.FormSpace BD →L[ℂ] KFCausalClosedGraphForm.FormSpace BD := BF
  let j : KFCausalClosedGraphForm.FormSpace BD →L[ℂ] Hilbert := BJ
  have hf : ∀ u, j (f u)=action ε a ha y (j u) := base_embedding ε hε a ha h hh hb y m g k
  have hc : ∀ (θ : ℝ) (x : Hilbert), action ε a ha y ((group h hh).action θ x)=
      (group h hh).action θ (action ε a ha y x) := action_charge ε a ha y h hh
  let z := KFCausalAveragedFormAction.formAction (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace BD) (group h hh) (2*Real.pi) j
    (action ε a ha y) f hf hc
  exact z

private theorem averaged_embedding (u : AV) :
    AJ (averagedAction ε hε a ha h hh hb y m g k u)=action ε a ha y (AJ u) := rfl

private theorem averaged_growing (u : AV) :
    growingOutputLp (AA (averagedAction ε hε a ha h hh hb y m g k u))=
      growingActionLp ε a ha h y (growingOutputLp (AA u)) := by
  let v := AS u
  change growingOutput.compLp ((BA).compLp ((BF).compLp v))=
    (growingAction ε a ha h y).compLp (growingOutput.compLp ((BA).compLp v))
  apply Lp.ext
  filter_upwards [growingOutput.coeFn_compLp ((BA).compLp ((BF).compLp v)),
    (BA).coeFn_compLp ((BF).compLp v),(BF).coeFn_compLp v,
    (growingAction ε a ha h y).coeFn_compLp (growingOutput.compLp ((BA).compLp v)),
    growingOutput.coeFn_compLp ((BA).compLp v),(BA).coeFn_compLp v]
      with θ h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h4,h5,h6]
  exact base_growing ε hε a ha h hh hb y m g k (v θ)

local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "RB" => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hb m g k

theorem reference_stability (u : RV) :
    ∃ v : RV, RJ v=action ε a ha y (RJ u) ∧ RB v=growingActionLp ε a ha h y (RB u) := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k 0
  let z := Classical.choose (hl u)
  have hz := Classical.choose_spec (hl u)
  refine ⟨lift (averagedAction ε hε a ha h hh hb y m g k z),?_,?_⟩
  · have hj : AJ z=RJ u := congrArg RJ hz
    exact (averaged_embedding ε hε a ha h hh hb y m g k z).trans (congrArg (action ε a ha y) hj)
  · have he : growingOutputLp (AA z)=RB u := congrArg RB hz
    exact (averaged_growing ε hε a ha h hh hb y m g k z).trans (congrArg (growingActionLp ε a ha h y) he)

local notation "T" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hb m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hb m g k
local notation "J" => KFCausalClosedGraphForm.embedding GD
local notation "B" => KFCausalClosedGraphForm.energyOutput GD

theorem growing_graph_action (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (T).graph) :
    (action ε a ha y f,growingActionLp ε a ha h y z) ∈ (T).graph := by
  rw [KFCausalClockFloorGrowingOutputClosure.operator_graph] at hz ⊢
  exact range_closure_transport (RJ) (RB) (action ε a ha y) (growingActionLp ε a ha h y)
    (reference_stability ε hε a ha h hh hb y m g k) f z hz

def formAction : GV →L[ℂ] GV :=
  KFCausalClosedGraphDiagonalAction.action GD (action ε a ha y) (growingActionLp ε a ha h y)
    (growing_graph_action ε hε a ha h hh hb y m g k)

theorem formAction_embedding (u : GV) :
    J (formAction ε hε a ha h hh hb y m g k u)=action ε a ha y (J u) := rfl

theorem formAction_output (u : GV) :
    B (formAction ε hε a ha h hh hb y m g k u)=growingActionLp ε a ha h y (B u) := rfl

#print axioms growingAction_apply
#print axioms reference_stability
#print axioms growing_graph_action
#print axioms formAction_embedding
#print axioms formAction_output
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingForm
