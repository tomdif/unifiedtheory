/- The rational radial multiplier acts on the original charge-averaged
form. Transport is first proved through the literal joint graph closure;
only then is it lifted to L2 circle sections and the physical reference
form. The static Leibniz defect vanishes under the growing selector. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaForm
import UnifiedTheory.Audit.KFCausalAveragedFormAction
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaReference
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorRadialYosidaSymbol (action action_charge)
open KFCausalClockFloorRadialYosidaEnergy (energy_bound factorOutput factorCorrection)
open KFCausalClockFloorRadialYosidaForm (outputAction extra)
open KFCausalPhysicalEnergyTransport (growingOutput)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace growingOutputLp)
open KFCausalPhysicalCircleAction (group)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)

include hε hb in
theorem wide_bound : |h| ≤ 2*Real.pi*ε/3 := by nlinarith [Real.pi_pos]

local notation "hs" => energy_bound ε hε h hb
local notation "hw" => wide_bound ε hε h hb
local notation "BD" => KFCausalClockFloorFormHamiltonian.formData ε hε h hs m g k 0
local notation "BJ" => KFCausalClosedGraphForm.embedding BD
local notation "BA" => KFCausalClosedGraphForm.energyOutput BD
local notation "BF" => KFCausalClockFloorRadialYosidaForm.formAction ε hε h N hN hb hne m g k 0
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hne m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hne m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hne m g k 0
local notation "AS" => KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hs hne m g k 0

def growingAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  growingOutput.comp (outputAction ε hε h N hN hb)

def growingActionLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (growingAction ε hε h N hN hb).compLpL 2 angleMeasure

theorem growingAction_apply (y : Output (Fin 8) Hilbert) (i : Fin 8) :
    growingAction ε hε h N hN hb y i=
      if i.val<3 then 0 else factorOutput ε hε h N hN hb i (y i) := by
  simp only [growingAction,ContinuousLinearMap.comp_apply,growingOutput,
    KFCausalFiniteOutputRescaling.selected_apply,outputAction,
    KFCausalJointGraphBoundedCorrection.outputMap]
  split_ifs <;> rfl

private theorem base_growing (u : KFCausalClosedGraphForm.FormSpace BD) :
    growingOutput (BA (BF u))=growingAction ε hε h N hN hb (growingOutput (BA u)) := by
  rw [KFCausalClockFloorRadialYosidaForm.formAction_output]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [growingAction,outputAction,extra,growingOutput,
    KFCausalFiniteOutputRescaling.selected_apply,KFCausalJointGraphBoundedCorrection.outputMap,
    KFCausalJointGraphBoundedCorrection.correctionMap,factorOutput,factorCorrection,
    KFCausalClockFloorRadialYosidaKinetics.correction]

def averagedAction : AV →L[ℂ] AV := by
  let f : KFCausalClosedGraphForm.FormSpace BD →L[ℂ] KFCausalClosedGraphForm.FormSpace BD := BF
  let j : KFCausalClosedGraphForm.FormSpace BD →L[ℂ] Hilbert := BJ
  have hf : ∀ u, j (f u)=action ε hε h N hN (j u) :=
    KFCausalClockFloorRadialYosidaForm.formAction_embedding ε hε h N hN hb hne m g k 0
  have hc : ∀ (θ : ℝ) (x : Hilbert), action ε hε h N hN ((group h hne).action θ x)=
      (group h hne).action θ (action ε hε h N hN x) :=
    action_charge ε hε h N hN hne
  let z := KFCausalAveragedFormAction.formAction (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace BD) (group h hne) (2*Real.pi) j
    (action ε hε h N hN) f hf hc
  exact z

theorem averagedAction_embedding (u : AV) :
    AJ (averagedAction ε hε h N hN hb hne m g k u)=action ε hε h N hN (AJ u) := rfl

theorem averagedAction_growing (u : AV) :
    growingOutputLp (AA (averagedAction ε hε h N hN hb hne m g k u))=
      growingActionLp ε hε h N hN hb (growingOutputLp (AA u)) := by
  let v := AS u
  change growingOutput.compLp ((BA).compLp ((BF).compLp v))=
    (growingAction ε hε h N hN hb).compLp (growingOutput.compLp ((BA).compLp v))
  apply Lp.ext
  filter_upwards [growingOutput.coeFn_compLp ((BA).compLp ((BF).compLp v)),
    (BA).coeFn_compLp ((BF).compLp v),(BF).coeFn_compLp v,
    (growingAction ε hε h N hN hb).coeFn_compLp (growingOutput.compLp ((BA).compLp v)),
    growingOutput.coeFn_compLp ((BA).compLp v),(BA).coeFn_compLp v]
      with θ h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h4,h5,h6]
  exact base_growing ε hε h N hN hb hne m g k (v θ)


#print axioms wide_bound
#print axioms growingAction_apply
#print axioms averagedAction_embedding
#print axioms averagedAction_growing
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaReference
