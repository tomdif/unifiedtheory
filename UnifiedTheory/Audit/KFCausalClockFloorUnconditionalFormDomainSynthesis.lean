/- Unconditional Form-Domain Synthesis for all real couplings and times:
time-invariance of the completed residual-output and full-energy domains,
joint embedding into the maximal static, radial-root, and potential form
domains, and the exact three-part output and form norm decompositions on
the reference space. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorResidualFormSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutput selectedOutputLp sourceMap)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorResidualFormReconstruction (referenceRoot reference_output_norm_sq
  averaged_domain_eq_root_inter_residual averaged_domain_eq_growing_inter_residual)
open KFCausalClockFloorResidualFormSplit (staticLift potentialLift residual_norm_split)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem projection_closure {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (S : Submodule ℂ (X × Y)) (T : Submodule ℂ (X × Z))
    (L : Y →L[ℂ] Z) (hT : IsClosed (T : Set (X × Z)))
    (hS : ∀ z ∈ S, (z.1,L z.2) ∈ T) (z : X × Y) (hz : z ∈ S.topologicalClosure) :
    (z.1,L z.2) ∈ T := by
  let F : X × Y →L[ℂ] X × Z := (ContinuousLinearMap.id ℂ X).prodMap L
  have hs : S ≤ T.comap F.toLinearMap := hS
  exact S.topologicalClosure_minimal hs (hT.preimage F.continuous) hz

private theorem point_selected_time (s t : ℝ) (z : Output (Fin 8) Hilbert) :
    selectedOutput (timeOutput s t z)=timeOutput s t (selectedOutput z) := by
  apply PiLp.ext
  intro i
  by_cases hr : retained i <;>
    simp [selectedOutput,selected_apply,timeOutput_apply,hr]

private theorem lp_selected_time (s t : ℝ) (z : EnergyOutputSpace) :
    selectedOutputLp (timeOutputLp s t z)=timeOutputLp s t (selectedOutputLp z) := by
  let w1 := timeOutputLp s t z
  let w2 := selectedOutputLp z
  apply Lp.ext
  filter_upwards [selectedOutput.coeFn_compLp w1,(timeOutput s t).coeFn_compLp z,
    (timeOutput s t).coeFn_compLp w2,selectedOutput.coeFn_compLp z] with θ h1 h2 h3 h4
  change selectedOutput.compLp w1 θ=(timeOutput s t).compLp w2 θ
  rw [h1,h3]
  change selectedOutput ((timeOutput s t).compLp z θ)=
    timeOutput s t (selectedOutput.compLp z θ)
  rw [h2,h4,point_selected_time]

private theorem point_time_trans (r t s : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput t s (timeOutput r t z)=timeOutput r s z := by
  have he : Complex.exp ((s:ℂ)-(t:ℂ))*Complex.exp ((t:ℂ)-(r:ℂ))=
      Complex.exp ((s:ℂ)-(r:ℂ)) := by
    rw [← Complex.exp_add,show (s:ℂ)-(t:ℂ)+((t:ℂ)-(r:ℂ))=(s:ℂ)-(r:ℂ) by ring]
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3
  · simp [timeOutput_apply,h3]
  · simp [timeOutput_apply,h3,smul_smul,he]

private theorem lp_time_trans (r t s : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t s (timeOutputLp r t z)=timeOutputLp r s z := by
  let w := timeOutputLp r t z
  apply Lp.ext
  filter_upwards [(timeOutput t s).coeFn_compLp w,
    (timeOutput r t).coeFn_compLp z,
    (timeOutput r s).coeFn_compLp z] with θ h1 h2 h3
  change (timeOutput t s).compLp w θ=(timeOutput r s).compLp z θ
  rw [h1,h3]
  change timeOutput t s ((timeOutput r t).compLp z θ)=timeOutput r s (z θ)
  rw [h2,point_time_trans]

private theorem point_time_self (t : ℝ) (z : Output (Fin 8) Hilbert) :
    timeOutput t t z=z := by
  apply PiLp.ext
  intro i
  by_cases h3 : i.val < 3 <;>
    simp [timeOutput_apply,h3,sub_self,one_smul]

private theorem lp_time_self (t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t t z=z := by
  apply Lp.ext
  filter_upwards [(timeOutput t t).coeFn_compLp z] with θ h1
  change (timeOutput t t).compLp z θ=z θ
  rw [h1,point_time_self]

private theorem lp_time_inv (s t : ℝ) (z : EnergyOutputSpace) :
    timeOutputLp t s (timeOutputLp s t z)=z :=
  (lp_time_trans s t s z).trans (lp_time_self s z)

private theorem exp_two_zero_mul (x : ℝ) : Real.exp (2*(0:ℝ))*x=x := by
  rw [mul_zero,Real.exp_zero,one_mul]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SR" => KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

private theorem sourceMap_eq_time_selected (t : ℝ) (u : RV) :
    sourceMap ε hε h hh hw m g k t u=timeOutputLp 0 t (selectedOutputLp (RA u)) :=
  ((ContinuousLinearMap.comp_apply selectedOutputLp ((timeOutputLp 0 t).comp RA) u).trans
    (congrArg selectedOutputLp (ContinuousLinearMap.comp_apply (timeOutputLp 0 t) RA u))).trans
    (lp_selected_time 0 t (RA u))

private theorem sourceMap_time_transfer (t s : ℝ) (u : RV) :
    timeOutputLp t s (sourceMap ε hε h hh hw m g k t u)=
      sourceMap ε hε h hh hw m g k s u :=
  (congrArg (timeOutputLp t s) (sourceMap_eq_time_selected ε hε h hh hb m g k t u)).trans
    ((lp_time_trans 0 t s (selectedOutputLp (RA u))).trans
      (sourceMap_eq_time_selected ε hε h hh hb m g k s u).symm)

private theorem residual_graph_time_forward (t s : ℝ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f,z) ∈ (Tres t).graph) :
    (f,timeOutputLp t s z) ∈ (Tres s).graph := by
  have hs : ∀ p ∈ KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hw m g k t,
      (p.1,timeOutputLp t s p.2) ∈ (Tres s).graph := by
    rintro p ⟨u,rfl⟩
    exact (congrArg (fun y : EnergyOutputSpace => (RJ u,y) ∈ (Tres s).graph)
      (sourceMap_time_transfer ε hε h hh hb m g k t s u).symm).mp
        (KFCausalClockFloorStaticPotentialOutputClosure.reference_graph ε hε h hh hw m g k s u)
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph] at hz
  exact projection_closure
    (KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hw m g k t)
    (Tres s).graph (timeOutputLp t s)
    (KFCausalClockFloorStaticPotentialOutputClosure.operator_closed ε hε h hh hw m g k s)
    hs (f,z) hz

theorem residual_graph_time_transfer (t s : ℝ) (f : Hilbert) (z : EnergyOutputSpace) :
    (f,z) ∈ (Tres t).graph ↔ (f,timeOutputLp t s z) ∈ (Tres s).graph := by
  constructor
  · exact residual_graph_time_forward ε hε h hh hb m g k t s f z
  · intro hts
    have hst := residual_graph_time_forward ε hε h hh hb m g k s t f (timeOutputLp t s z) hts
    exact (congrArg (fun y : EnergyOutputSpace => (f,y) ∈ (Tres t).graph)
      (lp_time_inv t s z)).mp hst

theorem residual_domain_time_eq (t s : ℝ) (f : Hilbert) :
    f ∈ (Tres t).domain ↔ f ∈ (Tres s).domain := by
  constructor
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((residual_graph_time_transfer ε hε h hh hb m g k t s f _).mp
        ((Tres t).mem_graph ⟨f,hf⟩))
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      ((residual_graph_time_transfer ε hε h hh hb m g k s t f _).mp
        ((Tres s).mem_graph ⟨f,hf⟩))

theorem averaged_domain_time_eq (t s : ℝ) (f : Hilbert) :
    f ∈ (Eavg t).domain ↔ f ∈ (Eavg s).domain := by
  rw [averaged_domain_eq_root_inter_residual ε hε h hh hb m g k t f,
    averaged_domain_eq_root_inter_residual ε hε h hh hb m g k s f,
    residual_domain_time_eq ε hε h hh hb m g k t s f]

theorem residual_domain_subset_static_inter_potential (t : ℝ) (f : Hilbert)
    (hf : f ∈ (Tres t).domain) :
    f ∈ (Tstat).domain ∧ f ∈ (Tpot).domain := by
  have hg := (Tres t).mem_graph ⟨f,hf⟩
  have hs0 : f ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).domain :=
    LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorResidualFormSplit.static_graph ε hε h hh hw m g k t f _ hg)
  rw [KFCausalClockFloorStaticOutputClosure.operator_domain ε hε h hh hw m g k 0] at hs0
  have hp0 : f ∈ (Tpot).domain :=
    LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorResidualFormSplit.potential_graph ε hε h hh hw m g k t f _ hg)
  exact ⟨hs0,hp0⟩

theorem averaged_domain_subset_three_forms (t : ℝ) (f : Hilbert)
    (hf : f ∈ (Eavg t).domain) :
    f ∈ (Tstat).domain ∧ f ∈ (Kroot).domain ∧ f ∈ (Tpot).domain := by
  obtain ⟨hr,hs⟩ := (averaged_domain_eq_root_inter_residual ε hε h hh hb m g k t f).mp hf
  obtain ⟨hst,hp⟩ := residual_domain_subset_static_inter_potential ε hε h hh hb m g k t f hs
  exact ⟨hst,hr,hp⟩

theorem averaged_domain_iff_root_potential_residual (t : ℝ) (f : Hilbert) :
    f ∈ (Eavg t).domain ↔
      (f ∈ (Kroot).domain ∧ f ∈ (Tpot).domain) ∧ f ∈ (Tres 0).domain := by
  rw [averaged_domain_eq_growing_inter_residual ε hε h hh hb m g k t f,
    KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff ε hε h hh hb m g k f,
    residual_domain_time_eq ε hε h hh hb m g k t 0 f]

theorem reference_three_part_output_norm_sq (u : RV) :
    ‖RA u‖^2=‖referenceRoot ε hε h hh hb m g k u‖^2+
      (‖TB (staticLift ε hε h hh hw m g k 0 (SR 0 u))‖^2+
        ‖PB (potentialLift ε hε h hh hw m g k 0 (SR 0 u))‖^2) :=
  have hsb : KFCausalClosedGraphForm.energyOutput (SD 0) (SR 0 u)=selectedOutputLp (RA u) :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_output ε hε h hh hw m g k 0 u).trans
      ((sourceMap_eq_time_selected ε hε h hh hb m g k 0 u).trans
        (lp_time_self 0 (selectedOutputLp (RA u))))
  have hsb_norm : ‖selectedOutputLp (RA u)‖^2=
      ‖KFCausalClosedGraphForm.energyOutput (SD 0) (SR 0 u)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hsb.symm
  have h2 : ‖selectedOutputLp (RA u)‖^2=
      ‖TB (staticLift ε hε h hh hw m g k 0 (SR 0 u))‖^2+
        ‖PB (potentialLift ε hε h hh hw m g k 0 (SR 0 u))‖^2 :=
    (hsb_norm.trans (residual_norm_split ε hε h hh hw m g k 0 (SR 0 u))).trans
      (congrArg (fun s : ℝ => ‖TB (staticLift ε hε h hh hw m g k 0 (SR 0 u))‖^2+s)
        (exp_two_zero_mul (‖PB (potentialLift ε hε h hh hw m g k 0 (SR 0 u))‖^2)))
  (reference_output_norm_sq ε hε h hh hb m g k u).trans
    (congrArg (fun s : ℝ => ‖referenceRoot ε hε h hh hb m g k u‖^2+s) h2)

theorem reference_three_part_form_norm_sq (u : RV) :
    ‖u‖^2=‖RJ u‖^2+
      (‖referenceRoot ε hε h hh hb m g k u‖^2+
        (‖TB (staticLift ε hε h hh hw m g k 0 (SR 0 u))‖^2+
          ‖PB (potentialLift ε hε h hh hw m g k 0 (SR 0 u))‖^2)) :=
  (KFCausalClockFloorAveragedFormTransport.form_norm_identity ε hε h hh hw m g k 0 u).trans
    (congrArg (fun s : ℝ => ‖RJ u‖^2+s)
      (reference_three_part_output_norm_sq ε hε h hh hb m g k u))

#print axioms residual_graph_time_transfer
#print axioms residual_domain_time_eq
#print axioms averaged_domain_time_eq
#print axioms residual_domain_subset_static_inter_potential
#print axioms averaged_domain_subset_three_forms
#print axioms averaged_domain_iff_root_potential_residual
#print axioms reference_three_part_output_norm_sq
#print axioms reference_three_part_form_norm_sq
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis
