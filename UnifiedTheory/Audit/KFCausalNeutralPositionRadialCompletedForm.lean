/- The radial observable acts on the completed form of the existing
charge-averaged Hamiltonian, with the full eight-output estimate. This
action commutes with the existing form transfers between times. No
Hamiltonian operator-domain preservation or response derivative is claimed. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm (OutputSpace transformed transformed_bound energy_graph_action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound (outputAction extra amplification)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph (responseConstant)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (formData)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (orbit angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)

local notation "W" => WithLp 2 (Hilbert × OutputSpace)

def ambientAction : W →L[ℂ] W :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert OutputSpace
  let R := (outputAction ε hε h δ v hδ hh).compLpL 2 angleMeasure
  let C := ((extra ε hε h δ v hδ).compLpL 2 angleMeasure).comp
    (orbit (group h hne) (2*Real.pi)).toContinuousLinearMap
  let b := ((action h δ v hδ).comp (ContinuousLinearMap.fst ℂ Hilbert OutputSpace)).prod
    (R.comp (ContinuousLinearMap.snd ℂ Hilbert OutputSpace)+
      C.comp (ContinuousLinearMap.fst ℂ Hilbert OutputSpace))
  e.symm.toContinuousLinearMap.comp (b.comp e.toContinuousLinearMap)

theorem ambient_mem (t : ℝ) (u : FormSpace ε hε h hne hh m g k t) :
    ambientAction ε hε h δ v hδ hh hne u.val ∈
      KFCausalClosedGraphForm.energyGraph (formData ε hε h hne hh m g k t) :=
  energy_graph_action ε hε h δ v hδ hh hne m g k t
    (embedding ε hε h hne hh m g k t u) (energyOutput ε hε h hne hh m g k t u) u.property

def formAction (t : ℝ) : FormSpace ε hε h hne hh m g k t →L[ℂ] FormSpace ε hε h hne hh m g k t where
  toFun u := ⟨ambientAction ε hε h δ v hδ hh hne u.val,
    ambient_mem ε hε h δ v hδ hh hne m g k t u⟩
  map_add' u w := by
    apply Subtype.ext
    exact (ambientAction ε hε h δ v hδ hh hne).map_add u.val w.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambientAction ε hε h δ v hδ hh hne).map_smul c u.val
  cont := ((ambientAction ε hε h δ v hδ hh hne).continuous.comp continuous_subtype_val).subtype_mk _

theorem formAction_embedding (t : ℝ) (u : FormSpace ε hε h hne hh m g k t) :
    embedding ε hε h hne hh m g k t (formAction ε hε h δ v hδ hh hne m g k t u) =
      action h δ v hδ (embedding ε hε h hne hh m g k t u) := rfl

theorem formAction_output (t : ℝ) (u : FormSpace ε hε h hne hh m g k t) :
    energyOutput ε hε h hne hh m g k t (formAction ε hε h δ v hδ hh hne m g k t u) =
      transformed ε hε h δ v hδ hh hne
        (embedding ε hε h hne hh m g k t u) (energyOutput ε hε h hne hh m g k t u) := rfl

theorem formAction_output_bound (t : ℝ) (u : FormSpace ε hε h hne hh m g k t) :
    ‖energyOutput ε hε h hne hh m g k t (formAction ε hε h δ v hδ hh hne m g k t u)‖ ≤
      amplification ε h δ v*‖energyOutput ε hε h hne hh m g k t u‖+
        |h| *responseConstant ε δ v*‖embedding ε hε h hne hh m g k t u‖ :=
  transformed_bound ε hε h δ v hδ hh hne _ _

theorem formAction_transfer (s t : ℝ) (u : FormSpace ε hε h hne hh m g k s) :
    formTransfer ε hε h hne hh m g k s t (formAction ε hε h δ v hδ hh hne m g k s u) =
      formAction ε hε h δ v hδ hh hne m g k t (formTransfer ε hε h hne hh m g k s t u) := by
  have hl := (transfer_embedding ε hε h hne hh m g k s t
    (formAction ε hε h δ v hδ hh hne m g k s u)).trans
      (formAction_embedding ε hε h δ v hδ hh hne m g k s u)
  have hr := (formAction_embedding ε hε h δ v hδ hh hne m g k t
    (formTransfer ε hε h hne hh m g k s t u)).trans
      (congrArg (action h δ v hδ) (transfer_embedding ε hε h hne hh m g k s t u))
  exact embedding_injective ε hε h hne hh m g k t (hl.trans hr.symm)

#print axioms ambient_mem
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_output_bound
#print axioms formAction_transfer

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm
