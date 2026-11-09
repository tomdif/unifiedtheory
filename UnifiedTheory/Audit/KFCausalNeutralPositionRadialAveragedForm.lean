/- The original charge-compatible radial observable acts on the actual
full charge-averaged energy form. The output identity and quantitative
bound include all eight rows and apply to every averaged-form vector. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialFormAction
import UnifiedTheory.Audit.KFCausalLpOutputCorrection
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action action_charge)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy (energy_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k t : ℝ)

local notation "hb" => energy_bound ε hε h hh
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g k t
local notation "J₀" => KFCausalClosedGraphForm.embedding 𝒟
local notation "A₀" => KFCausalClosedGraphForm.energyOutput 𝒟
local notation "F₀" => KFCausalNeutralPositionRadialFormAction.formAction ε hε h δ v hδ hh hne m g k t
local notation "J" => embedding ε hε h hb hne m g k t
local notation "A" => energyOutput ε hε h hb hne m g k t
local notation "S" => sectionMap ε hε h hb hne m g k t
local notation "V" => AveragedSpace ε hε h hb hne m g k t
local notation "R" => outputAction ε hε h δ v hδ hh
local notation "C" => extra ε hε h δ v hδ
local notation "U" => group h hne
local notation "T" => (2*Real.pi)

abbrev OutputSpace := Lp (Output (Fin 8) Hilbert) 2 angleMeasure

def correction (f : Hilbert) : OutputSpace := (C).compLp (orbit U T f)

def transformed (f : Hilbert) (y : OutputSpace) : OutputSpace :=
  (R).compLp y+correction ε hε h δ v hδ hne f

def formAction : V →L[ℂ] V := by
  let G : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] KFCausalClosedGraphForm.FormSpace 𝒟 := F₀
  let emb : KFCausalClosedGraphForm.FormSpace 𝒟 →L[ℂ] Hilbert := J₀
  have hG : ∀ u, emb (G u) = action h δ v hδ (emb u) :=
    KFCausalNeutralPositionRadialFormAction.formAction_embedding ε hε h δ v hδ hh hne m g k t
  have hC : ∀ (θ : ℝ) (f : Hilbert), action h δ v hδ ((group h hne).action θ f) =
      (group h hne).action θ (action h δ v hδ f) := action_charge h hne δ v hδ
  let L := KFCausalAveragedFormAction.formAction (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace 𝒟) U T J₀ (action h δ v hδ) G hG hC
  exact L

theorem formAction_embedding (u : V) :
    J (formAction ε hε h δ v hδ hh hne m g k t u) = action h δ v hδ (J u) := rfl

theorem formAction_output (u : V) :
    A (formAction ε hε h δ v hδ hh hne m g k t u) =
      transformed ε hε h δ v hδ hh hne (J u) (A u) := by
  change (A₀).compLp ((F₀).compLp (S u)) =
    (R).compLp ((A₀).compLp (S u))+(C).compLp (orbit U T (J u))
  have hu := u.property
  change (J₀).compLp (S u)-orbit U T (J u)=0 at hu
  have hJ := sub_eq_zero.mp hu
  have he := KFCausalLpOutputCorrection.output_relation (H := Hilbert)
    (E := KFCausalClosedGraphForm.FormSpace 𝒟) (K := Output (Fin 8) Hilbert) J₀ A₀ F₀ R C
    (KFCausalNeutralPositionRadialFormAction.formAction_output ε hε h δ v hδ hh hne m g k t) (S u)
  exact he.trans (congrArg (fun z => (R).compLp ((A₀).compLp (S u))+(C).compLp z) hJ)

theorem outputLp_bound (y : OutputSpace) : ‖(R).compLp y‖ ≤ amplification ε h δ v*‖y‖ := by
  have hop : ‖R‖ ≤ amplification ε h δ v :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
      (outputAction_norm ε hε h δ v hδ hh)
  exact ((R).norm_compLp_le y).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))

theorem correction_bound (f : Hilbert) :
    ‖correction ε hε h δ v hδ hne f‖ ≤ |h| *responseConstant ε δ v*‖f‖ := by
  have hop : ‖C‖ ≤ |h| *responseConstant ε δ v :=
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) (responseConstant_nonneg _ _ _))
      (extra_bound ε hε h δ v hδ)
  exact ((C).norm_compLp_le _).trans
    ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (by rw [(orbit _ _).norm_map]))

theorem transformed_bound (f : Hilbert) (y : OutputSpace) :
    ‖transformed ε hε h δ v hδ hh hne f y‖ ≤
      amplification ε h δ v*‖y‖+|h| *responseConstant ε δ v*‖f‖ :=
  (norm_add_le _ _).trans (add_le_add
    (outputLp_bound ε hε h δ v hδ hh y) (correction_bound ε hε h δ v hδ hne f))

theorem formAction_output_bound (u : V) :
    ‖A (formAction ε hε h δ v hδ hh hne m g k t u)‖ ≤
      amplification ε h δ v*‖A u‖+|h| *responseConstant ε δ v*‖J u‖ := by
  exact (congrArg norm (formAction_output ε hε h δ v hδ hh hne m g k t u)).le.trans
    (transformed_bound ε hε h δ v hδ hh hne _ _)

include hh in
theorem energy_domain_action (f : Hilbert)
    (hf : f ∈ (energyOperator ε hε h hb hne m g k t).domain) :
    action h δ v hδ f ∈ (energyOperator ε hε h hb hne m g k t).domain := by
  obtain ⟨u,rfl⟩ := (energy_domain ε hε h hb hne m g k t f).mp hf
  exact (energy_domain ε hε h hb hne m g k t _).mpr
    ⟨formAction ε hε h δ v hδ hh hne m g k t u,rfl⟩

theorem energy_graph_action (f : Hilbert) (y : OutputSpace)
    (hfy : (f,y) ∈ (energyOperator ε hε h hb hne m g k t).graph) :
    (action h δ v hδ f,transformed ε hε h δ v hδ hh hne f y) ∈
      (energyOperator ε hε h hb hne m g k t).graph := by
  let L : V →L[ℂ] V := formAction ε hε h δ v hδ hh hne m g k t
  have hL : ∀ u, J (L u) = action h δ v hδ (J u) :=
    formAction_embedding ε hε h δ v hδ hh hne m g k t
  have hA : ∀ u, A (L u) = transformed ε hε h δ v hδ hh hne (J u) (A u) :=
    formAction_output ε hε h δ v hδ hh hne m g k t
  have hg := @KFCausalLpOutputCorrection.graph_action Hilbert
    (KFCausalClosedGraphForm.FormSpace 𝒟) (Output (Fin 8) Hilbert)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    U T J₀ A₀ (KFCausalClosedGraphForm.embedding_injective 𝒟)
    (action h δ v hδ) (fun u => L u) (transformed ε hε h δ v hδ hh hne) hL hA f y hfy
  exact hg

#print axioms formAction_embedding
#print axioms formAction_output
#print axioms outputLp_bound
#print axioms correction_bound
#print axioms transformed_bound
#print axioms formAction_output_bound
#print axioms energy_domain_action
#print axioms energy_graph_action

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm
