/- Neutral translation acts on the entire actual charge-averaged energy
form, with exact output covariance and preservation in both directions.
The charge commutation and unaveraged domain facts are derived. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationForm
import UnifiedTheory.Audit.KFCausalNeutralTranslationCharge
import UnifiedTheory.Audit.KFCausalAveragedFormAction
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationAveragedForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors (action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationMatter (shiftValue)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε) (hne : h ≠ 0)
  (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k) (r : ℝ)
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε h hh m g k t
local notation "𝒱" => AveragedSpace ε hε h hh hne m g k t
local notation "J" => KFCausalClosedGraphForm.embedding 𝒟
local notation "A" => KFCausalClosedGraphForm.energyOutput 𝒟
local notation "F" => KFCausalNeutralTranslationForm.formAction ε hε h hh m g k t hm hg hk r
local notation "R" => outputAction (energyWeight m g k t) (shiftValue pointField r) r

def formAction : 𝒱 →L[ℂ] 𝒱 := by
  let G : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] KFCausalClosedGraphForm.FormSpace 𝒟 := F
  let emb : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] Hilbert := J
  have hG : ∀ u, emb (G u) = action r (emb u) :=
    KFCausalNeutralTranslationForm.formAction_embedding ε hε h hh m g k t hm hg hk r
  have hC : ∀ (θ : ℝ) (f : Hilbert), action r ((group h hne).action θ f) =
      (group h hne).action θ (action r f) :=
    KFCausalNeutralTranslationCharge.action_charge h hne r
  let L := KFCausalAveragedFormAction.formAction (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace 𝒟) (group h hne) (2*Real.pi) J
    (action r : Hilbert →L[ℂ] Hilbert) G hG hC
  exact L

theorem formAction_embedding (u : 𝒱) :
    embedding ε hε h hh hne m g k t (formAction ε hε h hh hne m g k t hm hg hk r u) =
      action r (embedding ε hε h hh hne m g k t u) := rfl

theorem formAction_section (u : 𝒱) :
    sectionMap ε hε h hh hne m g k t (formAction ε hε h hh hne m g k t hm hg hk r u) =
      (F).compLp (sectionMap ε hε h hh hne m g k t u) := rfl

theorem formAction_output (u : 𝒱) :
    energyOutput ε hε h hh hne m g k t (formAction ε hε h hh hne m g k t hm hg hk r u) =
      (R).compLp (energyOutput ε hε h hh hne m g k t u) := by
  let z := sectionMap ε hε h hh hne m g k t u
  change (A).compLp ((F).compLp z) = (R).compLp ((A).compLp z)
  apply Lp.ext
  filter_upwards [(A).coeFn_compLp ((F).compLp z),(F).coeFn_compLp z,
    (R).coeFn_compLp ((A).compLp z),(A).coeFn_compLp z] with θ ha hf hr hz
  rw [ha,hf,hr,hz]
  exact KFCausalNeutralTranslationForm.formAction_output ε hε h hh m g k t hm hg hk r _

theorem formAction_inverse (u : 𝒱) :
    formAction ε hε h hh hne m g k t hm hg hk (-r)
      (formAction ε hε h hh hne m g k t hm hg hk r u) = u := by
  apply embedding_injective ε hε h hh hne m g k t
  simp only [formAction_embedding,action_inverse]

include hm hg hk in
theorem energy_domain_action (f : Hilbert)
    (hf : f ∈ (energyOperator ε hε h hh hne m g k t).domain) :
    action r f ∈ (energyOperator ε hε h hh hne m g k t).domain := by
  obtain ⟨u,rfl⟩ := (energy_domain ε hε h hh hne m g k t f).mp hf
  exact (energy_domain ε hε h hh hne m g k t _).mpr
    ⟨formAction ε hε h hh hne m g k t hm hg hk r u,rfl⟩

include hm hg hk in
theorem energy_domain_action_iff (f : Hilbert) :
    action r f ∈ (energyOperator ε hε h hh hne m g k t).domain ↔
      f ∈ (energyOperator ε hε h hh hne m g k t).domain := by
  refine ⟨fun hf => ?_,energy_domain_action ε hε h hh hne m g k t hm hg hk r f⟩
  simpa only [action_inverse] using
    energy_domain_action ε hε h hh hne m g k t hm hg hk (-r) _ hf

#print axioms formAction_embedding
#print axioms formAction_section
#print axioms formAction_output
#print axioms formAction_inverse
#print axioms energy_domain_action
#print axioms energy_domain_action_iff

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationAveragedForm
