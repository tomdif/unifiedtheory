/- The radial resolvent regularizer preserves the domain of the maximal static
square-root operator and maps both the static square-root domain and the
maximal static operator domain into the intersection of the radial operator
domain and the static square-root domain. On the static square-root graph form,
the regularized static square-root output norm equals the regularized completed
static-form energy norm and converges to the static square-root output norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRoot
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorStaticMultiplierForm (rootOperator)
open KFCausalClockFloorStaticRootSource (rootData RootForm)
open KFCausalClockFloorStaticOutputClosure (extension_norm operator_domain)
open KFCausalClockFloorStaticHamiltonian (formData StaticForm rootLift
  rootLift_embedding rootLift_output)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain)
open KFCausalClockFloorRadialResolventStaticForm (formAction formAction_embedding
  domain_action form_sequence_tendsto)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0)

local notation "hw" => wide_bound ε hε h hb
local notation "RD" => rootData ε hε h
local notation "RJ" => KFCausalClosedGraphForm.embedding RD
local notation "RB" => KFCausalClosedGraphForm.energyOutput RD
local notation "TD" => formData ε hε h hh hw 0 0 0 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h

theorem rootForm_embedding_domain (w : RootForm ε hε h) :
    RJ w ∈ (rootOperator ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph w.property

theorem rootForm_output_eq (w : RootForm ε hε h) :
    RB w=rootOperator ε hε h ⟨RJ w,rootForm_embedding_domain ε hε h w⟩ :=
  (rootOperator ε hε h).mem_graph_snd_inj' w.property
    ((rootOperator ε hε h).mem_graph ⟨RJ w,rootForm_embedding_domain ε hε h w⟩) rfl

include hb hh in
theorem static_root_domain_action (f : Hilbert)
    (hf : f ∈ (rootOperator ε hε h).domain) :
    action ε hε h N hN f ∈ (rootOperator ε hε h).domain :=
  (operator_domain ε hε h hh hw 0 0 0 0 (action ε hε h N hN f)).mp
    (domain_action ε hε h N hN hb hh 0 0 0 f
      ((operator_domain ε hε h hh hw 0 0 0 0 f).mpr hf))

include hb hh in
theorem static_root_radial_domain_action (f : Hilbert)
    (hf : f ∈ (rootOperator ε hε h).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧
      action ε hε h N hN f ∈ (rootOperator ε hε h).domain :=
  ⟨radial_domain ε hε h N hN f,
    static_root_domain_action ε hε h N hN hb hh f hf⟩

include hb hh in
theorem static_operator_domain_to_root_radial (f : Hilbert)
    (hf : f ∈ (KFCausalClockFloorStaticOperator.operator ε hε h).domain) :
    action ε hε h N hN f ∈ (Kr).domain ∧
      action ε hε h N hN f ∈ (rootOperator ε hε h).domain :=
  static_root_radial_domain_action ε hε h N hN hb hh f
    (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨f,hf⟩)

def rootFormAction (w : RootForm ε hε h) : RootForm ε hε h :=
  KFCausalClosedGraphForm.graphVector RD
    ⟨action ε hε h N hN (RJ w),
      static_root_domain_action ε hε h N hN hb hh (RJ w)
        (rootForm_embedding_domain ε hε h w)⟩

def rootFormOutput (w : RootForm ε hε h) : Hilbert :=
  rootOperator ε hε h
    ⟨action ε hε h N hN (RJ w),
      static_root_domain_action ε hε h N hN hb hh (RJ w)
        (rootForm_embedding_domain ε hε h w)⟩

theorem rootLift_rootFormAction (w : RootForm ε hε h) :
    rootLift ε hε h hh hw 0 0 0 0 (rootFormAction ε hε h N hN hb hh w)=
      formAction ε hε h N hN hb hh 0 0 0 (rootLift ε hε h hh hw 0 0 0 0 w) :=
  KFCausalClosedGraphForm.embedding_injective TD
    ((rootLift_embedding ε hε h hh hw 0 0 0 0
      (rootFormAction ε hε h N hN hb hh w)).trans
      ((congrArg (action ε hε h N hN)
        (rootLift_embedding ε hε h hh hw 0 0 0 0 w).symm).trans
        (formAction_embedding ε hε h N hN hb hh 0 0 0
          (rootLift ε hε h hh hw 0 0 0 0 w)).symm))

theorem rootFormOutput_norm (w : RootForm ε hε h) :
    ‖rootFormOutput ε hε h N hN hb hh w‖=
      ‖TB (formAction ε hε h N hN hb hh 0 0 0 (rootLift ε hε h hh hw 0 0 0 0 w))‖ :=
  (extension_norm ε hε h hh hw 0 0 0 0
    (rootFormAction ε hε h N hN hb hh w)).symm.trans
    ((congrArg norm (rootLift_output ε hε h hh hw 0 0 0 0
      (rootFormAction ε hε h N hN hb hh w))).symm.trans
      (congrArg (fun u => ‖TB u‖)
        (rootLift_rootFormAction ε hε h N hN hb hh w)))

theorem rootFormOutput_norm_tendsto (w : RootForm ε hε h) :
    Tendsto (fun n : ℕ =>
      ‖rootFormOutput ε hε h ((n:ℝ)+1) (by positivity) hb hh w‖)
      atTop (𝓝 ‖rootOperator ε hε h ⟨RJ w,rootForm_embedding_domain ε hε h w⟩‖) := by
  let v := rootLift ε hε h hh hw 0 0 0 0 w
  have ht : Tendsto (fun n : ℕ =>
      ‖TB (formAction ε hε h ((n:ℝ)+1) (by positivity) hb hh 0 0 0 v)‖)
      atTop (𝓝 ‖TB v‖) :=
    (((TB).continuous.tendsto v).comp
      (form_sequence_tendsto ε hε h hb hh 0 0 0 v)).norm
  have hlim : ‖TB v‖=‖rootOperator ε hε h ⟨RJ w,rootForm_embedding_domain ε hε h w⟩‖ :=
    (congrArg norm (rootLift_output ε hε h hh hw 0 0 0 0 w)).trans
      ((extension_norm ε hε h hh hw 0 0 0 0 w).trans
        (congrArg norm (rootForm_output_eq ε hε h w)))
  rw [← hlim]
  exact ht.congr' (Eventually.of_forall (fun n =>
    (rootFormOutput_norm ε hε h ((n:ℝ)+1) (by positivity) hb hh w).symm))

#print axioms rootForm_embedding_domain
#print axioms rootForm_output_eq
#print axioms static_root_domain_action
#print axioms static_root_radial_domain_action
#print axioms static_operator_domain_to_root_radial
#print axioms rootLift_rootFormAction
#print axioms rootFormOutput_norm
#print axioms rootFormOutput_norm_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRoot
