/- Multi-channel synthesis for the radial resolvent regularizer across the
completed full-energy, growing, residual, static, and potential forms at all
real couplings and times: all channel projections intertwine with the lifted
radial resolvent form actions, the growing and residual potential projections
coincide, the regularized energy norms satisfy exact two-channel and
three-channel decompositions, and every regularized full-form vector lies
simultaneously in all seven operator and form-closure domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRoot
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventAveragedForm
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventPotentialForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventMultiChannelSynthesis
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain)
open KFCausalClockFloorRadialResolventRoot (action_root_domain)
open KFCausalClockFloorResidualFormSplit (staticLift potentialLift
  staticLift_embedding potentialLift_embedding residual_norm_split)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput)

private theorem three_channel_arith (s b g r p c : ℝ)
    (hres : s=b+c*p) (hgrow : g=r+p) : s+c*r=b+c*g := by
  rw [hres,hgrow]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k t
local notation "JT" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k t
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "GL" => KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "SR" => KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "Tstat" => KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k

def growingProject (u : VT) : GV :=
  GL (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 u)

def residualProject (u : VT) : SV :=
  SR (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 u)

theorem growingProject_embedding (u : VT) :
    GJ (growingProject ε hε h hb hh m g k t u)=JT u :=
  (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k
    (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 u)).trans
    (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k t 0 u)

theorem residualProject_embedding (u : VT) :
    SJ (residualProject ε hε h hb hh m g k t u)=JT u :=
  (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t
    (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k t 0 u)).trans
    (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k t 0 u)

theorem growingLift_growingProject_eq_potentialLift_residualProject (u : VT) :
    growingLift ε hε h hh hw m g k (growingProject ε hε h hb hh m g k t u)=
      potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u) :=
  KFCausalClosedGraphForm.embedding_injective PD
    ((growingLift_embedding ε hε h hh hw m g k
      (growingProject ε hε h hb hh m g k t u)).trans
      ((growingProject_embedding ε hε h hb hh m g k t u).trans
        ((residualProject_embedding ε hε h hb hh m g k t u).symm.trans
          (potentialLift_embedding ε hε h hh hw m g k t
            (residualProject ε hε h hb hh m g k t u)).symm)))

theorem potentialLift_formAction (w : SV) :
    potentialLift ε hε h hh hw m g k t
      (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w)=
    KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k
      (potentialLift ε hε h hh hw m g k t w) :=
  KFCausalClosedGraphForm.embedding_injective PD
    ((potentialLift_embedding ε hε h hh hw m g k t
      (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t w)).trans
      ((KFCausalClockFloorRadialResolventResidual.formAction_embedding
        ε hε h N hN hb hh m g k t w).trans
        ((congrArg (action ε hε h N hN)
          (potentialLift_embedding ε hε h hh hw m g k t w).symm).trans
          (KFCausalClockFloorRadialResolventPotential.formAction_embedding
            ε hε h N hN hb hh m g k
            (potentialLift ε hε h hh hw m g k t w)).symm)))

theorem growingLift_potential_formAction (v : GV) :
    growingLift ε hε h hh hw m g k
      (KFCausalClockFloorRadialResolventGrowing.formAction ε hε h N hN hb hh m g k v)=
    KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k
      (growingLift ε hε h hh hw m g k v) :=
  KFCausalClockFloorRadialResolventGrowing.growingLift_formAction ε hε h N hN hb hh m g k v

theorem growingProject_formAction (u : VT) :
    growingProject ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)=
    KFCausalClockFloorRadialResolventGrowing.formAction ε hε h N hN hb hh m g k
      (growingProject ε hε h hb hh m g k t u) :=
  KFCausalClosedGraphForm.embedding_injective GD
    ((growingProject_embedding ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)).trans
      ((KFCausalClockFloorRadialResolventAveragedForm.formAction_embedding
        ε hε h N hN hb hh m g k t u).trans
        ((congrArg (action ε hε h N hN)
          (growingProject_embedding ε hε h hb hh m g k t u).symm).trans
          (KFCausalClockFloorRadialResolventGrowing.formAction_embedding
            ε hε h N hN hb hh m g k
            (growingProject ε hε h hb hh m g k t u)).symm)))

theorem residualProject_formAction (u : VT) :
    residualProject ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)=
    KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m g k t
      (residualProject ε hε h hb hh m g k t u) :=
  KFCausalClosedGraphForm.embedding_injective SD
    ((residualProject_embedding ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)).trans
      ((KFCausalClockFloorRadialResolventAveragedForm.formAction_embedding
        ε hε h N hN hb hh m g k t u).trans
        ((congrArg (action ε hε h N hN)
          (residualProject_embedding ε hε h hb hh m g k t u).symm).trans
          (KFCausalClockFloorRadialResolventResidual.formAction_embedding
            ε hε h N hN hb hh m g k t
            (residualProject ε hε h hb hh m g k t u)).symm)))

theorem staticProject_formAction (u : VT) :
    staticLift ε hε h hh hw m g k t
      (residualProject ε hε h hb hh m g k t
        (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u))=
    KFCausalClockFloorRadialResolventStaticForm.formAction ε hε h N hN hb hh m g k
      (staticLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)) :=
  (congrArg (staticLift ε hε h hh hw m g k t)
    (residualProject_formAction ε hε h N hN hb hh m g k t u)).trans
    (KFCausalClockFloorRadialResolventStaticForm.staticLift_formAction
      ε hε h N hN hb hh m g k t (residualProject ε hε h hb hh m g k t u))

theorem potentialProject_formAction (u : VT) :
    potentialLift ε hε h hh hw m g k t
      (residualProject ε hε h hb hh m g k t
        (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u))=
    KFCausalClockFloorRadialResolventPotential.formAction ε hε h N hN hb hh m g k
      (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)) :=
  (congrArg (potentialLift ε hε h hh hw m g k t)
    (residualProject_formAction ε hε h N hN hb hh m g k t u)).trans
    (potentialLift_formAction ε hε h N hN hb hh m g k t
      (residualProject ε hε h hb hh m g k t u))

theorem regularized_two_channel_norm_split (u : VT) :
    ‖SB (residualProject ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u))‖^2=
      ‖TB (KFCausalClockFloorRadialResolventStaticForm.formAction ε hε h N hN hb hh m g k
        (staticLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2+
      Real.exp (2*t)*‖PB (KFCausalClockFloorRadialResolventPotential.formAction
        ε hε h N hN hb hh m g k
        (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2 := by
  let ur := residualProject ε hε h hb hh m g k t
    (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)
  have hsplit := residual_norm_split ε hε h hh hw m g k t ur
  have hstat : ‖TB (staticLift ε hε h hh hw m g k t ur)‖^2=
      ‖TB (KFCausalClockFloorRadialResolventStaticForm.formAction ε hε h N hN hb hh m g k
        (staticLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2 :=
    congrArg (fun v => ‖TB v‖^2) (staticProject_formAction ε hε h N hN hb hh m g k t u)
  have hpot : ‖PB (potentialLift ε hε h hh hw m g k t ur)‖^2=
      ‖PB (KFCausalClockFloorRadialResolventPotential.formAction
        ε hε h N hN hb hh m g k
        (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2 :=
    congrArg (fun v => ‖PB v‖^2) (potentialProject_formAction ε hε h N hN hb hh m g k t u)
  exact hsplit.trans (congrArg₂ (·+·) hstat (congrArg (Real.exp (2*t)*·) hpot))

theorem regularized_three_channel_norm_split (u : VT) :
    ‖SB (residualProject ε hε h hb hh m g k t
      (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u))‖^2+
      Real.exp (2*t)*‖action ε hε h N hN (R (growingProject ε hε h hb hh m g k t u))‖^2=
      ‖TB (KFCausalClockFloorRadialResolventStaticForm.formAction ε hε h N hN hb hh m g k
        (staticLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2+
      Real.exp (2*t)*‖GB (growingProject ε hε h hb hh m g k t
        (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u))‖^2 := by
  let g0 := growingProject ε hε h hb hh m g k t u
  let gr := growingProject ε hε h hb hh m g k t
    (KFCausalClockFloorRadialResolventAveragedForm.formAction ε hε h N hN hb hh m g k t u)
  have hgrow0 := KFCausalClockFloorRadialResolventGrowing.growing_output_norm_sq
    ε hε h hb hh m g k gr
  have hR : ‖R gr‖^2=‖action ε hε h N hN (R g0)‖^2 :=
    congrArg (fun z : Hilbert => ‖z‖^2)
      ((congrArg R (growingProject_formAction ε hε h N hN hb hh m g k t u)).trans
        (KFCausalClockFloorRadialResolventGrowing.rootOutput_formAction
          ε hε h N hN hb hh m g k g0))
  have hP : ‖PB (growingLift ε hε h hh hw m g k gr)‖^2=
      ‖PB (KFCausalClockFloorRadialResolventPotential.formAction
        ε hε h N hN hb hh m g k
        (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2 :=
    congrArg (fun v : PV => ‖PB v‖^2)
      ((congrArg (growingLift ε hε h hh hw m g k)
        (growingProject_formAction ε hε h N hN hb hh m g k t u)).trans
        ((growingLift_potential_formAction ε hε h N hN hb hh m g k g0).trans
          (congrArg (KFCausalClockFloorRadialResolventPotential.formAction
            ε hε h N hN hb hh m g k)
            (growingLift_growingProject_eq_potentialLift_residualProject
              ε hε h hb hh m g k t u))))
  have hgrow : ‖GB gr‖^2=
      ‖action ε hε h N hN (R g0)‖^2+
        ‖PB (KFCausalClockFloorRadialResolventPotential.formAction
          ε hε h N hN hb hh m g k
          (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hb hh m g k t u)))‖^2 :=
    hgrow0.trans (congrArg₂ (·+·) hR hP)
  have hres := regularized_two_channel_norm_split ε hε h N hN hb hh m g k t u
  exact three_channel_arith _ _ _ _ _ (Real.exp (2*t)) hres hgrow

theorem regularized_multi_channel_domain (u : VT) :
    let f := action ε hε h N hN (JT u)
    f ∈ (Kr).domain ∧
      f ∈ (Eavg).domain ∧
      f ∈ (Tgrow).domain ∧
      f ∈ (Tres).domain ∧
      f ∈ (Tstat).domain ∧
      f ∈ (Tpot).domain ∧
      f ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain ∧
      f ∈ (KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h).domain := by
  let f := action ε hε h N hN (JT u)
  have hf0 : JT u ∈ (Eavg).domain := LinearPMap.mem_domain_of_mem_graph u.property
  have heavg : f ∈ (Eavg).domain :=
    KFCausalClockFloorRadialResolventAveragedForm.domain_action ε hε h N hN hb hh m g k t (JT u) hf0
  have hgr : f ∈ (Tgrow).domain ∧ f ∈ (Tres).domain :=
    (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
      ε hε h hh hb m g k t f).mp heavg
  have hpot : f ∈ (Tpot).domain :=
    ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
      ε hε h hh hb m g k f).mp hgr.1).2
  have hstat : f ∈ (Tstat).domain :=
    LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorResidualFormSplit.static_graph ε hε h hh hw m g k t f _
        ((Tres).mem_graph ⟨f,hgr.2⟩))
  have hroot_stat : f ∈ (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain :=
    (KFCausalClockFloorStaticOutputClosure.operator_domain ε hε h hh hw m g k 0 f).mp hstat
  exact ⟨radial_domain ε hε h N hN (JT u),heavg,hgr.1,hgr.2,hstat,hpot,
    hroot_stat,action_root_domain ε hε h N hN (JT u)⟩

#print axioms growingProject_embedding
#print axioms residualProject_embedding
#print axioms growingLift_growingProject_eq_potentialLift_residualProject
#print axioms potentialLift_formAction
#print axioms growingLift_potential_formAction
#print axioms growingProject_formAction
#print axioms residualProject_formAction
#print axioms staticProject_formAction
#print axioms potentialProject_formAction
#print axioms regularized_two_channel_norm_split
#print axioms regularized_three_channel_norm_split
#print axioms regularized_multi_channel_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventMultiChannelSynthesis
