/- The physical clock defect acts on the entire actual charge-averaged
energy form domain. Its output is the pointwise eight-factor action,
and the signed square pairing survives the charge integral. -/
import UnifiedTheory.Audit.KFCausalAveragedFormAction
import UnifiedTheory.Audit.KFCausalClockFloorChargeDefect
import UnifiedTheory.Audit.KFCausalClockFloorFormDefect
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => KFCausalClockFloorClosedEnergyDefect.energy_bound ε hε hbar hh
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t
local notation "𝒱" => AveragedSpace ε hε hbar hb hne mass2 quartic vacuum t
local notation "J" => KFCausalClosedGraphForm.embedding 𝒟
local notation "A" => KFCausalClosedGraphForm.energyOutput 𝒟
local notation "F" => KFCausalClockFloorFormDefect.formAction ε hε hbar hh mass2 quartic vacuum t
local notation "R" => outputAction ε hε hbar hh

def formAction : 𝒱 →L[ℂ] 𝒱 := by
  let G : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] KFCausalClosedGraphForm.FormSpace 𝒟 := F
  let emb : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] Hilbert := J
  have hG : ∀ v, emb (G v) = defectOperator ε hε (emb v) :=
    (KFCausalClockFloorFormDefect.formAction_embedding ε hε hbar hh mass2 quartic vacuum t)
  have hC : ∀ (θ : ℝ) (f : Hilbert), defectOperator ε hε ((group hbar hne).action θ f) =
      (group hbar hne).action θ (defectOperator ε hε f) :=
    (KFCausalClockFloorChargeDefect.defect_action ε hε hbar hne)
  let L := KFCausalAveragedFormAction.formAction (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace 𝒟) (group hbar hne) (2*Real.pi) J
    (defectOperator ε hε) F hG hC
  exact L

theorem formAction_embedding (u : 𝒱) :
    embedding ε hε hbar hb hne mass2 quartic vacuum t (formAction ε hε hbar hne hh mass2 quartic vacuum t u) =
      defectOperator ε hε (embedding ε hε hbar hb hne mass2 quartic vacuum t u) := rfl

theorem formAction_section (u : 𝒱) :
    sectionMap ε hε hbar hb hne mass2 quartic vacuum t (formAction ε hε hbar hne hh mass2 quartic vacuum t u) =
      (F).compLp (sectionMap ε hε hbar hb hne mass2 quartic vacuum t u) := rfl

theorem formAction_output (u : 𝒱) :
    energyOutput ε hε hbar hb hne mass2 quartic vacuum t (formAction ε hε hbar hne hh mass2 quartic vacuum t u) =
      (R).compLp (energyOutput ε hε hbar hb hne mass2 quartic vacuum t u) := by
  let v := sectionMap ε hε hbar hb hne mass2 quartic vacuum t u
  change (A).compLp ((F).compLp v) = (R).compLp ((A).compLp v)
  apply Lp.ext
  filter_upwards [(A).coeFn_compLp ((F).compLp v),(F).coeFn_compLp v,
    (R).coeFn_compLp ((A).compLp v),(A).coeFn_compLp v] with θ ha hf hr hv
  rw [ha,hf,hr,hv]
  exact KFCausalClockFloorFormDefect.formAction_output ε hε hbar hh mass2 quartic vacuum t _

theorem outputLp_norm (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    ‖(R).compLp g‖ ≤ 2*‖g‖ := by
  apply ((R).norm_compLp_le g).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (outputAction_norm ε hε hbar hh)

theorem outputLp_square_sign (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    0 ≤ hbar*(inner ℂ g ((R).compLp ((R).compLp g))).im := by
  have hi := L2.integrable_inner (𝕜 := ℂ) g ((R).compLp ((R).compLp g))
  have he := integral_im hi
  change (∫ θ, (inner ℂ (g θ) ((R).compLp ((R).compLp g) θ)).im ∂angleMeasure) =
    (∫ θ, inner ℂ (g θ) ((R).compLp ((R).compLp g) θ) ∂angleMeasure).im at he
  rw [L2.inner_def,← he,← integral_const_mul]
  apply integral_nonneg_of_ae
  filter_upwards [(R).coeFn_compLp ((R).compLp g),(R).coeFn_compLp g] with θ h1 h2
  rw [h1,h2]
  exact outputAction_square_sign ε hε hbar hh (g θ)

theorem formAction_square_sign (u : 𝒱) :
    0 ≤ hbar*(inner ℂ (energyOutput ε hε hbar hb hne mass2 quartic vacuum t u)
      (energyOutput ε hε hbar hb hne mass2 quartic vacuum t
        (formAction ε hε hbar hne hh mass2 quartic vacuum t
          (formAction ε hε hbar hne hh mass2 quartic vacuum t u)))).im := by
  simp only [formAction_output]
  exact outputLp_square_sign ε hε hbar hh _

theorem defect_energy_domain (f : Hilbert)
    (hf : f ∈ (energyOperator ε hε hbar hb hne mass2 quartic vacuum t).domain) :
    defectOperator ε hε f ∈ (energyOperator ε hε hbar hb hne mass2 quartic vacuum t).domain := by
  obtain ⟨u,rfl⟩ := (energy_domain ε hε hbar hb hne mass2 quartic vacuum t f).mp hf
  apply (energy_domain ε hε hbar hb hne mass2 quartic vacuum t _).mpr
  exact ⟨formAction ε hε hbar hne hh mass2 quartic vacuum t u,rfl⟩

#print axioms formAction_embedding
#print axioms formAction_section
#print axioms formAction_output
#print axioms outputLp_norm
#print axioms outputLp_square_sign
#print axioms formAction_square_sign
#print axioms defect_energy_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
