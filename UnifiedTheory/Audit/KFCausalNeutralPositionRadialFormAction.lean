/- The actual radial observable lifts to a bounded map of the physical
eight-factor closed graph form. Its embedding and output identities are
derived from the simultaneous graph theorem, not assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialFormAction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy (energy_bound closed_graph)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound
open UnifiedTheory.Audit.KFCausalClosedGraphForm (FormSpace embedding energyOutput energyGraph)
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian (formData)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k t : ℝ)

local notation "𝒟" => formData ε hε h (energy_bound ε hε h hh) m g k t
local notation "W" => WithLp 2 (Hilbert × Output (Fin 8) Hilbert)

def ambientAction : W →L[ℂ] W :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert (Output (Fin 8) Hilbert)
  let b := ((action h δ v hδ).comp (ContinuousLinearMap.fst ℂ Hilbert (Output (Fin 8) Hilbert))).prod
      ((outputAction ε hε h δ v hδ hh).comp (ContinuousLinearMap.snd ℂ Hilbert (Output (Fin 8) Hilbert))+
        (extra ε hε h δ v hδ).comp (ContinuousLinearMap.fst ℂ Hilbert (Output (Fin 8) Hilbert)))
  e.symm.toContinuousLinearMap.comp (b.comp e.toContinuousLinearMap)

include hne in
theorem ambient_mem (u : FormSpace 𝒟) :
    ambientAction ε hε h δ v hδ hh u.val ∈ energyGraph 𝒟 := by
  have hg := closed_graph ε δ v hε hδ h hh hne m g k t
    (embedding 𝒟 u) (energyOutput 𝒟 u) u.property
  rw [transformedOutput_eq] at hg
  exact hg

def formAction : FormSpace 𝒟 →L[ℂ] FormSpace 𝒟 where
  toFun u := ⟨ambientAction ε hε h δ v hδ hh u.val,
    ambient_mem ε hε h δ v hδ hh hne m g k t u⟩
  map_add' u w := by
    apply Subtype.ext
    exact (ambientAction ε hε h δ v hδ hh).map_add u.val w.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambientAction ε hε h δ v hδ hh).map_smul c u.val
  cont := ((ambientAction ε hε h δ v hδ hh).continuous.comp continuous_subtype_val).subtype_mk _

theorem formAction_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formAction ε hε h δ v hδ hh hne m g k t u) =
      action h δ v hδ (embedding 𝒟 u) := rfl

theorem formAction_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formAction ε hε h δ v hδ hh hne m g k t u) =
      outputAction ε hε h δ v hδ hh (energyOutput 𝒟 u)+extra ε hε h δ v hδ (embedding 𝒟 u) := rfl

theorem formAction_output_bound (u : FormSpace 𝒟) :
    ‖energyOutput 𝒟 (formAction ε hε h δ v hδ hh hne m g k t u)‖ ≤
      amplification ε h δ v*‖energyOutput 𝒟 u‖+
        |h| *KFCausalNeutralPositionRadialKineticGraph.responseConstant ε δ v*‖embedding 𝒟 u‖ :=
  output_bound ε hε h δ v hδ hh _ _

#print axioms ambient_mem
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_output_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialFormAction
