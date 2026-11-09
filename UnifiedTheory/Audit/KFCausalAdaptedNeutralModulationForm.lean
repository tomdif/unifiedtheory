/- The adapted neutral phase has an invertible bounded action on the
complete unaveraged energy form, including vanishing matter weights.
Its output correction is uniformly O(abs(hbar)) and independent of time.
This does not assert preservation of the charge-averaged form. -/
import UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationGraph
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationForm
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates (action action_inverse)
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationGraph
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseAction_norm_bound)
open UnifiedTheory.Audit.KFCausalClosedGraphForm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε) (hne : h ≠ 0)
  (m g k t v : ℝ)
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε h hh m g k t

def formAction : FormSpace 𝒟 →L[ℂ] FormSpace 𝒟 := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Outputs
  let P : WithLp 2 (Hilbert × Outputs) →L[ℂ] WithLp 2 (Hilbert × Outputs) :=
    e.symm.toContinuousLinearMap.comp
      ((pairAction ε hε h v (energyWeight m g k t)).comp e.toContinuousLinearMap)
  exact (P.comp (energyGraph 𝒟).subtypeL).codRestrict (energyGraph 𝒟) (fun u =>
    closed_energy_graph_action ε hε h hne v m g k t hh
      (embedding 𝒟 u) (energyOutput 𝒟 u) u.property)

theorem formAction_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formAction ε hε h hh hne m g k t v u) = action v (embedding 𝒟 u) := rfl

theorem formAction_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formAction ε hε h hh hne m g k t v u) =
      modulateOutput v (energyOutput 𝒟 u+extra ε hε h v (energyWeight m g k t) (embedding 𝒟 u)) := rfl

theorem formAction_inverse (u : FormSpace 𝒟) :
    formAction ε hε h hh hne m g k t (-v)
      (formAction ε hε h hh hne m g k t v u) = u := by
  apply embedding_injective 𝒟
  simp only [formAction_embedding,action_inverse]

theorem formAction_surjective : Function.Surjective (formAction ε hε h hh hne m g k t v) := by
  intro u
  refine ⟨formAction ε hε h hh hne m g k t (-v) u,?_⟩
  simpa only [neg_neg] using formAction_inverse ε hε h hh hne m g k t (-v) u

theorem output_correction_norm (u : FormSpace 𝒟) :
    ‖energyOutput 𝒟 (formAction ε hε h hh hne m g k t v u)-modulateOutput v (energyOutput 𝒟 u)‖ =
      3*|h| * |v| *Real.sqrt (1/2)*‖inverseL ε hε (embedding 𝒟 u)‖ := by
  rw [formAction_output,map_add,add_sub_cancel_left,modulateOutput_norm,extra_norm]
  have hw : ‖energyWeight m g k t 2‖ = Real.sqrt (1/2) := by
    simp [energyWeight]
  rw [hw]

theorem output_correction_bound (u : FormSpace 𝒟) :
    ‖energyOutput 𝒟 (formAction ε hε h hh hne m g k t v u)-modulateOutput v (energyOutput 𝒟 u)‖ ≤
      |h| *(3*|v| *Real.sqrt (1/2)*(Real.sqrt ε)⁻¹)*‖embedding 𝒟 u‖ := by
  rw [output_correction_norm]
  have hi := inverseAction_norm_bound ε hε (embedding 𝒟 u)
  change ‖inverseL ε hε (embedding 𝒟 u)‖ ≤ _ at hi
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 3*|h| * |v| *Real.sqrt (1/2))).trans_eq (by ring)

#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_inverse
#print axioms formAction_surjective
#print axioms output_correction_norm
#print axioms output_correction_bound

end
end UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationForm
