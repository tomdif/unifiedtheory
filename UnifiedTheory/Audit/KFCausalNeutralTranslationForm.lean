/- A bounded lift of neutral translation to the complete unaveraged
physical energy form. Its embedding and all energy outputs are exact.
The positive coupling hypotheses retain all eight controlled channels. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationForm
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors (action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationMatter (shiftValue)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClosedGraphForm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε)
  (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k) (r : ℝ)
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε h hh m g k t
local notation "R" => outputAction (energyWeight m g k t) (shiftValue pointField r) r

def formAction : FormSpace 𝒟 →L[ℂ] FormSpace 𝒟 := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Outputs
  let P : WithLp 2 (Hilbert × Outputs) →L[ℂ] WithLp 2 (Hilbert × Outputs) :=
    e.symm.toContinuousLinearMap.comp ((pairAction r pointField (energyWeight m g k t)).comp e.toContinuousLinearMap)
  exact (P.comp (energyGraph 𝒟).subtypeL).codRestrict (energyGraph 𝒟) (fun u =>
    closed_energy_graph_action ε hε h r modelDirections pointField m g k t hm hg hk hh
      (embedding 𝒟 u) (energyOutput 𝒟 u) u.property)

theorem formAction_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formAction ε hε h hh m g k t hm hg hk r u) = action r (embedding 𝒟 u) := rfl

theorem formAction_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formAction ε hε h hh m g k t hm hg hk r u) = R (energyOutput 𝒟 u) := rfl

theorem formAction_inverse (u : FormSpace 𝒟) :
    formAction ε hε h hh m g k t hm hg hk (-r)
      (formAction ε hε h hh m g k t hm hg hk r u) = u := by
  apply embedding_injective 𝒟
  simp only [formAction_embedding,action_inverse]

theorem formAction_surjective :
    Function.Surjective (formAction ε hε h hh m g k t hm hg hk r) := by
  intro u
  refine ⟨formAction ε hε h hh m g k t hm hg hk (-r) u,?_⟩
  simpa only [neg_neg] using formAction_inverse ε hε h hh m g k t hm hg hk (-r) u

theorem formAction_energy (u : FormSpace 𝒟) :
    ‖energyOutput 𝒟 (formAction ε hε h hh m g k t hm hg hk r u)‖ =
      ‖weightedMix (energyWeight m g k t) (shiftValue pointField r) (energyOutput 𝒟 u)‖ := by
  rw [formAction_output]
  exact translateOutput_norm r _

#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_inverse
#print axioms formAction_surjective
#print axioms formAction_energy

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationForm
