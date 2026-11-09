/- Clock Gaussian actions on the full reference form and the completed
residual form. Simultaneous transport on all eight output rows lifts through
orbit averaging and descends to the time-weighted residual form closure,
intertwining with the canonical projection to the potential form. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialDomain
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianResidualForm
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorGaussianGrowingTransport (action action_charge forward_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalJointGraphBoundedCorrection (outputMap correctionMap)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalPhysicalCircleAction (group)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorGaussianGrowingForm (factorOutput outputAction)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp sourceMap)
open KFCausalClockFloorResidualFormSplit (potentialLift potentialLift_embedding)

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

def outputActionLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (outputAction ε a ha h y).compLpL 2 angleMeasure

def residualOutputAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  selectedOutput.comp (outputAction ε a ha h y)

def residualOutputActionLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (residualOutputAction ε a ha h y).compLpL 2 angleMeasure

private theorem outputAction_apply (z : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction ε a ha h y z i=factorOutput ε a ha h y i (z i) := rfl

theorem timeOutput_outputAction (t : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput 0 t (outputAction ε a ha h y z)=
      outputAction ε a ha h y (timeOutput 0 t z) := by
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3 <;>
    simp only [timeOutput_apply,outputAction_apply,h3,if_true,if_false,map_smul]

theorem selectedOutput_outputAction (z : Output (Fin 8) Hilbert) :
    selectedOutput (outputAction ε a ha h y z)=
      residualOutputAction ε a ha h y (selectedOutput z) := by
  apply PiLp.ext
  intro i
  by_cases hr : retained i <;>
    simp only [residualOutputAction,ContinuousLinearMap.comp_apply,selectedOutput,
      selected_apply,outputAction_apply,hr,if_true,if_false,map_zero]

private theorem source_point_action (t : ℝ) (z : Output (Fin 8) Hilbert) :
    selectedOutput (timeOutput 0 t (outputAction ε a ha h y z))=
      residualOutputAction ε a ha h y (selectedOutput (timeOutput 0 t z)) := by
  rw [timeOutput_outputAction,selectedOutput_outputAction]

private theorem source_lp_action (t : ℝ) (z : EnergyOutputSpace) :
    selectedOutputLp (timeOutputLp 0 t (outputActionLp ε a ha h y z))=
      residualOutputActionLp ε a ha h y (selectedOutputLp (timeOutputLp 0 t z)) := by
  let o := outputActionLp ε a ha h y z
  let to1 := timeOutputLp 0 t o
  let to2 := timeOutputLp 0 t z
  let s2 := selectedOutputLp to2
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp to1,(timeOutput 0 t).coeFn_compLp o,
    (outputAction ε a ha h y).coeFn_compLp z,
    (residualOutputAction ε a ha h y).coeFn_compLp s2,
    selectedOutput.coeFn_compLp to2,(timeOutput 0 t).coeFn_compLp z]
    with θ h1 h2 h3 h4 h5 h6
  change (selectedOutput.compLp to1) θ=((residualOutputAction ε a ha h y).compLp s2) θ
  rw [h1,h4]
  change selectedOutput (((timeOutput 0 t).compLp o) θ)=
    residualOutputAction ε a ha h y ((selectedOutput.compLp to2) θ)
  rw [h2,h5]
  change selectedOutput (timeOutput 0 t (((outputAction ε a ha h y).compLp z) θ))=
    residualOutputAction ε a ha h y (selectedOutput (((timeOutput 0 t).compLp z) θ))
  rw [h3,h6,source_point_action]

private theorem source_output_eq (t : ℝ) (p q : EnergyOutputSpace)
    (hpq : p=outputActionLp ε a ha h y q) :
    selectedOutputLp (timeOutputLp 0 t p)=
      residualOutputActionLp ε a ha h y (selectedOutputLp (timeOutputLp 0 t q)) := by
  rw [hpq,source_lp_action]

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

private theorem base_output (u : KFCausalClosedGraphForm.FormSpace BD) :
    BA (baseAction ε hε a ha h hh hb y m g k u)=outputAction ε a ha h y (BA u) := rfl

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

private theorem averaged_output (u : AV) :
    AA (averagedAction ε hε a ha h hh hb y m g k u)=outputActionLp ε a ha h y (AA u) := by
  let v := AS u
  change (BA).compLp ((BF).compLp v)=(outputAction ε a ha h y).compLp ((BA).compLp v)
  apply Lp.ext
  filter_upwards [(BA).coeFn_compLp ((BF).compLp v),(BF).coeFn_compLp v,
    (outputAction ε a ha h y).coeFn_compLp ((BA).compLp v),(BA).coeFn_compLp v]
    with θ h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  exact base_output ε hε a ha h hh hb y m g k (v θ)

private theorem averaged_residual (t : ℝ) (u : AV) :
    selectedOutputLp (timeOutputLp 0 t (AA (averagedAction ε hε a ha h hh hb y m g k u)))=
      residualOutputActionLp ε a ha h y (selectedOutputLp (timeOutputLp 0 t (AA u))) :=
  source_output_eq ε a ha h y t _ _ (averaged_output ε hε a ha h hh hb y m g k u)

local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0

theorem reference_full_stability (u : RV) :
    ∃ v : RV, RJ v=action ε a ha y (RJ u) ∧ RA v=outputActionLp ε a ha h y (RA u) := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k 0
  let z := Classical.choose (hl u)
  have hz := Classical.choose_spec (hl u)
  refine ⟨lift (averagedAction ε hε a ha h hh hb y m g k z),?_,?_⟩
  · have hj : AJ z=RJ u := congrArg RJ hz
    exact (averaged_embedding ε hε a ha h hh hb y m g k z).trans (congrArg (action ε a ha y) hj)
  · have he : AA z=RA u := congrArg RA hz
    exact (averaged_output ε hε a ha h hh hb y m g k z).trans (congrArg (outputActionLp ε a ha h y) he)

theorem residual_reference_stability (t : ℝ) (u : RV) :
    ∃ v : RV, RJ v=action ε a ha y (RJ u) ∧
      sourceMap ε hε h hh hb m g k t v=
        residualOutputActionLp ε a ha h y (sourceMap ε hε h hh hb m g k t u) := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k 0
  let z := Classical.choose (hl u)
  have hz := Classical.choose_spec (hl u)
  refine ⟨lift (averagedAction ε hε a ha h hh hb y m g k z),?_,?_⟩
  · have hj : AJ z=RJ u := congrArg RJ hz
    exact (averaged_embedding ε hε a ha h hh hb y m g k z).trans (congrArg (action ε a ha y) hj)
  · have he : selectedOutputLp (timeOutputLp 0 t (AA z))=sourceMap ε hε h hh hb m g k t u :=
      congrArg (sourceMap ε hε h hh hb m g k t) hz
    exact (averaged_residual ε hε a ha h hh hb y m g k t z).trans
      (congrArg (residualOutputActionLp ε a ha h y) he)

theorem residual_graph_action (t : ℝ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).graph) :
    (action ε a ha y f,residualOutputActionLp ε a ha h y z) ∈
      (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t).graph := by
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph] at hz ⊢
  exact range_closure_transport (RJ) (sourceMap ε hε h hh hb m g k t)
    (action ε a ha y) (residualOutputActionLp ε a ha h y)
    (residual_reference_stability ε hε a ha h hh hb y m g k t) f z hz

local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hb m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k

def residualFormAction (t : ℝ) : SV t →L[ℂ] SV t :=
  KFCausalClosedGraphDiagonalAction.action (SD t) (action ε a ha y) (residualOutputActionLp ε a ha h y)
    (residual_graph_action ε hε a ha h hh hb y m g k t)

theorem residualFormAction_embedding (t : ℝ) (w : SV t) :
    KFCausalClosedGraphForm.embedding (SD t)
      (residualFormAction ε hε a ha h hh hb y m g k t w)=
        action ε a ha y (KFCausalClosedGraphForm.embedding (SD t) w) := rfl

theorem residualFormAction_output (t : ℝ) (w : SV t) :
    KFCausalClosedGraphForm.energyOutput (SD t)
      (residualFormAction ε hε a ha h hh hb y m g k t w)=
        residualOutputActionLp ε a ha h y (KFCausalClosedGraphForm.energyOutput (SD t) w) := rfl

theorem potentialLift_residualFormAction (t : ℝ) (w : SV t) :
    potentialLift ε hε h hh hb m g k t
      (residualFormAction ε hε a ha h hh hb y m g k t w)=
        KFCausalClockFloorGaussianPotentialForm.formAction ε hε a ha h hh hb y m g k
          (potentialLift ε hε h hh hb m g k t w) := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (potentialLift_embedding ε hε h hh hb m g k t
    (residualFormAction ε hε a ha h hh hb y m g k t w)).trans
    ((residualFormAction_embedding ε hε a ha h hh hb y m g k t w).trans
      ((congrArg (action ε a ha y) (potentialLift_embedding ε hε h hh hb m g k t w).symm).trans
        (KFCausalClockFloorGaussianPotentialForm.formAction_embedding ε hε a ha h hh hb y m g k
          (potentialLift ε hε h hh hb m g k t w)).symm))

#print axioms timeOutput_outputAction
#print axioms selectedOutput_outputAction
#print axioms reference_full_stability
#print axioms residual_reference_stability
#print axioms residual_graph_action
#print axioms residualFormAction_embedding
#print axioms residualFormAction_output
#print axioms potentialLift_residualFormAction
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianResidualForm
