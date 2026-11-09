/- Neutral translation on the graph presentation of the completed
charge-averaged form used by the actual propagator. Exact physical and
output identities persist, and the action commutes with form transfer. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralReferenceForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (formData graphFormVector graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors (action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (pointField_shift)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def outputActionLp (m g k t r : ℝ) : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (KFCausalNeutralTranslationOutput.outputAction (energyWeight m g k t) (r:ℂ) r).compLpL 2 angleMeasure

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
local notation "𝒱" => FormSpace ε hε h hne hh m g k
local notation "J" => embedding ε hε h hne hh m g k
local notation "E" => energyOutput ε hε h hne hh m g k
local notation "R" => outputActionLp m g k
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "hb" => hamiltonian_bound ε h hh

include hm hg hk in
theorem graph_action (t r : ℝ) (u : 𝒱 t) :
    WithLp.toLp 2 (action r (J t u),R t r (E t u)) ∈
      KFCausalClosedGraphForm.energyGraph (formData ε hε h hne hh m g k t) := by
  let v := Classical.choose (graphFormVector_surjective ε hε h hne hh m g k t u)
  have hv := Classical.choose_spec (graphFormVector_surjective ε hε h hne hh m g k t u)
  have he : KFCausalClockFloorAveragedEnergy.embedding ε hε h hb hne m g k t v = J t u :=
    congrArg (J t) hv
  have ho : KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hb hne m g k t v = E t u :=
    congrArg (E t) hv
  have hp := (graphFormVector ε hε h hne hh m g k t
    (KFCausalNeutralTranslationAveragedForm.formAction ε hε h hb hne m g k t hm hg hk r v)).property
  have he' := (KFCausalNeutralTranslationAveragedForm.formAction_embedding
    ε hε h hb hne m g k t hm hg hk r v).trans (congrArg (action r) he)
  have hout := KFCausalNeutralTranslationAveragedForm.formAction_output
    ε hε h hb hne m g k t hm hg hk r v
  have ho' : KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hb hne m g k t
      (KFCausalNeutralTranslationAveragedForm.formAction ε hε h hb hne m g k t hm hg hk r v) =
      R t r (E t u) := by
    simpa only [pointField_shift,ho] using hout
  have heq := congrArg₂ (fun (f : Hilbert) (y : EnergyOutputSpace) => WithLp.toLp 2 (f,y)) he' ho'
  exact (congrArg (fun z => z ∈ KFCausalClosedGraphForm.energyGraph
    (formData ε hε h hne hh m g k t)) heq).mp hp

def formAction (t r : ℝ) : 𝒱 t →L[ℂ] 𝒱 t := by
  let D := formData ε hε h hne hh m g k t
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace
  let P : WithLp 2 (Hilbert × EnergyOutputSpace) →L[ℂ] WithLp 2 (Hilbert × EnergyOutputSpace) :=
    e.symm.toContinuousLinearMap.comp
      (((action r : Hilbert →L[ℂ] Hilbert).prodMap (R t r)).comp e.toContinuousLinearMap)
  exact (P.comp (KFCausalClosedGraphForm.energyGraph D).subtypeL).codRestrict
    (KFCausalClosedGraphForm.energyGraph D) (graph_action ε hε h hne hh m g k hm hg hk t r)

theorem formAction_embedding (t r : ℝ) (u : 𝒱 t) :
    J t (formAction ε hε h hne hh m g k hm hg hk t r u) = action r (J t u) := rfl

theorem formAction_output (t r : ℝ) (u : 𝒱 t) :
    E t (formAction ε hε h hne hh m g k hm hg hk t r u) = R t r (E t u) := rfl

theorem formAction_inverse (t r : ℝ) (u : 𝒱 t) :
    formAction ε hε h hne hh m g k hm hg hk t (-r)
      (formAction ε hε h hne hh m g k hm hg hk t r u) = u := by
  apply embedding_injective ε hε h hne hh m g k t
  simp only [formAction_embedding,action_inverse]

theorem formAction_transfer (s t r : ℝ) (u : 𝒱 s) :
    T s t (formAction ε hε h hne hh m g k hm hg hk s r u) =
      formAction ε hε h hne hh m g k hm hg hk t r (T s t u) := by
  apply embedding_injective ε hε h hne hh m g k t
  simp only [transfer_embedding,formAction_embedding]

#print axioms graph_action
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_inverse
#print axioms formAction_transfer

end
end UnifiedTheory.Audit.KFCausalNeutralReferenceForm
