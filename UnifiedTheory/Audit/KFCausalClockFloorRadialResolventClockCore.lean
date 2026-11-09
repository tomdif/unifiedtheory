/- Combining the radial resolvent operator commutation, multi-channel form
synthesis, and clock-domain commutation: the radial resolvent regularizer
preserves the intersection of the maximal radial operator domain with the
half-clock domain and converges simultaneously in Hilbert norm, radial output,
and half-clock output. On the completed interacting form space, every
half-clock-regular form vector has radial resolvent approximants lying
simultaneously in the half-clock domain and all eight radial, static-root, and
multi-channel form domains, converging strongly in norm, half-clock output,
static square-root output, and all five completed form outputs. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventMultiChannelSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCommutation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCore
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventOperator (operator_commute operator_sequence_tendsto)
open KFCausalClockFloorRadialResolventClockCommutation
  (resolvent_clockHalf_domain resolvent_clockHalf_commute resolvent_clockHalf_tendsto)
open KFCausalClockFloorStaticMultiplierForm (rootOperator)
open KFCausalClockFloorStaticRootSource (rootData RootForm)
open KFCausalClockFloorStaticOutputClosure (extension extension_norm operator_domain)
open KFCausalClockFloorStaticHamiltonian (rootLift rootLift_embedding rootLift_output)
open KFCausalClockFloorRadialResolventStaticRoot
  (rootForm_embedding_domain rootForm_output_eq static_root_domain_action
    rootFormAction rootFormOutput rootLift_rootFormAction)
open KFCausalClockFloorResidualFormSplit (staticLift potentialLift
  staticLift_embedding potentialLift_embedding)
open KFCausalClockFloorRadialResolventMultiChannelSynthesis
  (growingProject residualProject growingProject_embedding residualProject_embedding
    regularized_multi_channel_domain)

private theorem form_operator_apply
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : KFCausalClosedGraphForm.Data H K)
    (w : KFCausalClosedGraphForm.FormSpace D)
    (f : H) (hf : f ∈ D.operator.domain)
    (he : KFCausalClosedGraphForm.embedding D w = f) :
    D.operator ⟨f, hf⟩ = KFCausalClosedGraphForm.energyOutput D w :=
  D.operator.mem_graph_snd_inj' (D.operator.mem_graph ⟨f, hf⟩) w.property he.symm

private theorem form_operator_sequence_tendsto
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : KFCausalClosedGraphForm.Data H K)
    (w : KFCausalClosedGraphForm.FormSpace D)
    (wSeq : ℕ → KFCausalClosedGraphForm.FormSpace D)
    (f : H) (hf : f ∈ D.operator.domain)
    (fSeq : ℕ → H) (hfSeq : ∀ n, fSeq n ∈ D.operator.domain)
    (he : KFCausalClosedGraphForm.embedding D w = f)
    (heSeq : ∀ n, KFCausalClosedGraphForm.embedding D (wSeq n) = fSeq n)
    (ht : Tendsto wSeq atTop (𝓝 w)) :
    Tendsto (fun n : ℕ => D.operator ⟨fSeq n, hfSeq n⟩)
      atTop (𝓝 (D.operator ⟨f, hf⟩)) := by
  have hlim : Tendsto (fun n : ℕ => KFCausalClosedGraphForm.energyOutput D (wSeq n))
      atTop (𝓝 (KFCausalClosedGraphForm.energyOutput D w)) :=
    ((KFCausalClosedGraphForm.energyOutput D).continuous.tendsto w).comp ht
  rw [form_operator_apply D w f hf he]
  exact hlim.congr' (Eventually.of_forall (fun n =>
    (form_operator_apply D (wSeq n) (fSeq n) (hfSeq n) (heSeq n)).symm))

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

local notation "Kr" => operator ε hε h
local notation "J" => action ε hε h N hN
local notation "Troot" => rootOperator ε hε h

theorem radial_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    J f ∈ (Kr).domain ∧ J f ∈ (clockHalf ε).domain :=
  ⟨radial_domain ε hε h N hN f, resolvent_clockHalf_domain ε hε h N hN f hf⟩

theorem radial_clockHalf_sequence_tendsto (f : Hilbert)
    (hkr : f ∈ (Kr).domain) (hch : f ∈ (clockHalf ε).domain) :
    (∀ n : ℕ,
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (Kr).domain ∧
        action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (clockHalf ε).domain) ∧
    Tendsto (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) ∧
    Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩)
      atTop (𝓝 (Kr ⟨f, hkr⟩)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hch⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hch⟩)) :=
  ⟨fun n => radial_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hch,
    sequence_tendsto ε hε h f,
    operator_sequence_tendsto ε hε h ⟨f, hkr⟩,
    resolvent_clockHalf_tendsto ε hε h f hch⟩

variable (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "RD" => rootData ε hε h
local notation "RJ" => KFCausalClosedGraphForm.embedding RD
local notation "RB" => KFCausalClosedGraphForm.energyOutput RD
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw 0 0 0 0
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k t
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k t
local notation "JT" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k t
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k t
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "SD0" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "Tstat" => KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k

theorem rootFormOutput_sub_norm (w : RootForm ε hε h) :
    ‖rootFormOutput ε hε h N hN hb hh w - RB w‖ =
      ‖TB (KFCausalClockFloorRadialResolventStaticForm.formAction
        ε hε h N hN hb hh 0 0 0 (rootLift ε hε h hh hw 0 0 0 0 w)) -
        TB (rootLift ε hε h hh hw 0 0 0 0 w)‖ := by
  let wN := rootFormAction ε hε h N hN hb hh w
  have h1 : ‖rootFormOutput ε hε h N hN hb hh w - RB w‖ = ‖RB (wN - w)‖ :=
    congrArg norm ((RB).map_sub wN w).symm
  have h2 : ‖RB (wN - w)‖ = ‖extension ε hε h hh hw 0 0 0 0 (wN - w)‖ :=
    (extension_norm ε hε h hh hw 0 0 0 0 (wN - w)).symm
  have h3 : extension ε hε h hh hw 0 0 0 0 (wN - w) =
      TB (KFCausalClockFloorRadialResolventStaticForm.formAction
        ε hε h N hN hb hh 0 0 0 (rootLift ε hε h hh hw 0 0 0 0 w)) -
        TB (rootLift ε hε h hh hw 0 0 0 0 w) :=
    ((extension ε hε h hh hw 0 0 0 0).map_sub wN w).trans
      (congrArg (fun v => TB v - TB (rootLift ε hε h hh hw 0 0 0 0 w))
        (rootLift_rootFormAction ε hε h N hN hb hh w))
  exact h1.trans (h2.trans (congrArg norm h3))

theorem rootFormOutput_sequence_tendsto (w : RootForm ε hε h) :
    Tendsto (fun n : ℕ =>
      rootFormOutput ε hε h ((n : ℝ) + 1) (by positivity) hb hh w)
      atTop (𝓝 (RB w)) := by
  let v := rootLift ε hε h hh hw 0 0 0 0 w
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp
    (((TB).continuous.tendsto v).comp
      (KFCausalClockFloorRadialResolventStaticForm.form_sequence_tendsto
        ε hε h hb hh 0 0 0 v))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact ht.congr' (Eventually.of_forall (fun n =>
    (rootFormOutput_sub_norm ε hε h ((n : ℝ) + 1) (by positivity) hb hh w).symm))

theorem static_root_sequence_tendsto (f : Hilbert) (hf : f ∈ (Troot).domain) :
    Tendsto (fun n : ℕ =>
      Troot ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_root_domain_action ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hf⟩)
      atTop (𝓝 (Troot ⟨f, hf⟩)) := by
  let w : RootForm ε hε h := KFCausalClosedGraphForm.graphVector RD ⟨f, hf⟩
  exact rootFormOutput_sequence_tendsto ε hε h hb hh w

theorem multi_channel_domain_of_form (u : VT) :
    JT u ∈ (Eavg).domain ∧
      JT u ∈ (Tgrow).domain ∧
      JT u ∈ (Tres).domain ∧
      JT u ∈ (Tstat).domain ∧
      JT u ∈ (Tpot).domain ∧
      JT u ∈ (Troot).domain := by
  let f := JT u
  have heavg : f ∈ (Eavg).domain := LinearPMap.mem_domain_of_mem_graph u.property
  have hgr : f ∈ (Tgrow).domain ∧ f ∈ (Tres).domain :=
    (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
      ε hε h hh hb m g k t f).mp heavg
  have hpot : f ∈ (Tpot).domain :=
    ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
      ε hε h hh hb m g k f).mp hgr.1).2
  have hstat : f ∈ (Tstat).domain :=
    LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorResidualFormSplit.static_graph ε hε h hh hw m g k t f _
        ((Tres).mem_graph ⟨f, hgr.2⟩))
  have hroot : f ∈ (Troot).domain :=
    (operator_domain ε hε h hh hw m g k 0 f).mp hstat
  exact ⟨heavg, hgr.1, hgr.2, hstat, hpot, hroot⟩

theorem regularized_clock_multi_channel_domain (u : VT)
    (hch : JT u ∈ (clockHalf ε).domain) :
    let f := action ε hε h N hN (JT u)
    f ∈ (clockHalf ε).domain ∧
      f ∈ (Kr).domain ∧
      f ∈ (Eavg).domain ∧
      f ∈ (Tgrow).domain ∧
      f ∈ (Tres).domain ∧
      f ∈ (Tstat).domain ∧
      f ∈ (Tpot).domain ∧
      f ∈ (Troot).domain ∧
      f ∈ (KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h).domain :=
  ⟨resolvent_clockHalf_domain ε hε h N hN (JT u) hch,
    regularized_multi_channel_domain ε hε h N hN hb hh m g k t u⟩

theorem regularized_clock_multi_channel_tendsto (u : VT)
    (hch : JT u ∈ (clockHalf ε).domain) :
    let hd := multi_channel_domain_of_form ε hε h hb hh m g k t u
    let hdSeq := fun n : ℕ =>
      regularized_clock_multi_channel_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t u hch
    Tendsto (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      atTop (𝓝 (JT u)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).1⟩)
      atTop (𝓝 (clockHalf ε ⟨JT u, hch⟩)) ∧
    Tendsto (fun n : ℕ =>
      Eavg ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.1⟩)
      atTop (𝓝 (Eavg ⟨JT u, hd.1⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tgrow ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.2.1⟩)
      atTop (𝓝 (Tgrow ⟨JT u, hd.2.1⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tres ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.2.2.1⟩)
      atTop (𝓝 (Tres ⟨JT u, hd.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tstat ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.2.2.2.1⟩)
      atTop (𝓝 (Tstat ⟨JT u, hd.2.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ =>
      Tpot ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.2.2.2.2.1⟩)
      atTop (𝓝 (Tpot ⟨JT u, hd.2.2.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ =>
      Troot ⟨action ε hε h ((n : ℝ) + 1) (by positivity) (JT u), (hdSeq n).2.2.2.2.2.2.2.1⟩)
      atTop (𝓝 (Troot ⟨JT u, hd.2.2.2.2.2⟩)) := by
  let hd := multi_channel_domain_of_form ε hε h hb hh m g k t u
  let hdSeq := fun n : ℕ =>
    regularized_clock_multi_channel_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t u hch
  let gu := growingProject ε hε h hb hh m g k t u
  let ru := residualProject ε hε h hb hh m g k t u
  let su := staticLift ε hε h hh hw m g k t ru
  let pu := potentialLift ε hε h hh hw m g k t ru
  have hgu : KFCausalClosedGraphForm.embedding GD gu = JT u :=
    growingProject_embedding ε hε h hb hh m g k t u
  have hru : KFCausalClosedGraphForm.embedding SD ru = JT u :=
    residualProject_embedding ε hε h hb hh m g k t u
  have hsu : KFCausalClosedGraphForm.embedding SD0 su = JT u :=
    (staticLift_embedding ε hε h hh hw m g k t ru).trans hru
  have hpu : KFCausalClosedGraphForm.embedding PD pu = JT u :=
    (potentialLift_embedding ε hε h hh hw m g k t ru).trans hru
  refine ⟨sequence_tendsto ε hε h (JT u),
    resolvent_clockHalf_tendsto ε hε h (JT u) hch,
    form_operator_sequence_tendsto AD u
      (fun n => KFCausalClockFloorRadialResolventAveragedForm.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t u)
      (JT u) hd.1
      (fun n => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      (fun n => (hdSeq n).2.2.1) rfl
      (fun n => KFCausalClockFloorRadialResolventAveragedForm.formAction_embedding
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t u)
      (KFCausalClockFloorRadialResolventAveragedForm.form_sequence_tendsto
        ε hε h hb hh m g k t u),
    form_operator_sequence_tendsto GD gu
      (fun n => KFCausalClockFloorRadialResolventGrowing.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k gu)
      (JT u) hd.2.1
      (fun n => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      (fun n => (hdSeq n).2.2.2.1) hgu
      (fun n => (KFCausalClockFloorRadialResolventGrowing.formAction_embedding
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k gu).trans
        (congrArg (action ε hε h ((n : ℝ) + 1) (by positivity)) hgu))
      (KFCausalClockFloorRadialResolventGrowing.form_sequence_tendsto
        ε hε h hb hh m g k gu),
    form_operator_sequence_tendsto SD ru
      (fun n => KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t ru)
      (JT u) hd.2.2.1
      (fun n => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      (fun n => (hdSeq n).2.2.2.2.1) hru
      (fun n => (KFCausalClockFloorRadialResolventResidual.formAction_embedding
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t ru).trans
        (congrArg (action ε hε h ((n : ℝ) + 1) (by positivity)) hru))
      (KFCausalClockFloorRadialResolventResidual.form_sequence_tendsto
        ε hε h hb hh m g k t ru),
    form_operator_sequence_tendsto SD0 su
      (fun n => KFCausalClockFloorRadialResolventStaticForm.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k su)
      (JT u) hd.2.2.2.1
      (fun n => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      (fun n => (hdSeq n).2.2.2.2.2.1) hsu
      (fun n => (KFCausalClockFloorRadialResolventStaticForm.formAction_embedding
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k su).trans
        (congrArg (action ε hε h ((n : ℝ) + 1) (by positivity)) hsu))
      (KFCausalClockFloorRadialResolventStaticForm.form_sequence_tendsto
        ε hε h hb hh m g k su),
    form_operator_sequence_tendsto PD pu
      (fun n => KFCausalClockFloorRadialResolventPotential.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k pu)
      (JT u) hd.2.2.2.2.1
      (fun n => action ε hε h ((n : ℝ) + 1) (by positivity) (JT u))
      (fun n => (hdSeq n).2.2.2.2.2.2.1) hpu
      (fun n => (KFCausalClockFloorRadialResolventPotential.formAction_embedding
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k pu).trans
        (congrArg (action ε hε h ((n : ℝ) + 1) (by positivity)) hpu))
      (KFCausalClockFloorRadialResolventPotentialForm.form_sequence_tendsto
        ε hε h hb hh m g k pu),
    static_root_sequence_tendsto ε hε h hb hh (JT u) hd.2.2.2.2.2⟩

#print axioms radial_clockHalf_domain
#print axioms radial_clockHalf_sequence_tendsto
#print axioms rootFormOutput_sub_norm
#print axioms rootFormOutput_sequence_tendsto
#print axioms static_root_sequence_tendsto
#print axioms multi_channel_domain_of_form
#print axioms regularized_clock_multi_channel_domain
#print axioms regularized_clock_multi_channel_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCore
