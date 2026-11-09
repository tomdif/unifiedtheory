/- Trajectory-wide form-domain regularity, two-time form-norm comparisons, and
five-operator component form-energy bounds along the nonautonomous quantum
evolution for all real couplings and times. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormNormBounds
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalOperatorFormEnergy
import UnifiedTheory.Audit.KFCausalClockFloorRescaledEnergy
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormEnergyRegularity
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorStaticRootSource (rootData)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput rootOutput_graph)
open KFCausalClockFloorResidualFormSplit
  (staticLift staticLift_embedding potentialLift potentialLift_embedding
   residual_norm_split source_static)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding)
open KFCausalClockFloorRadialResolventGrowing (growing_output_norm_sq)
open KFCausalClockFloorTwoTimeFormTransfer
  (residualFormTransfer growingProject residualProject)
open KFCausalClockFloorTwoTimeFormNormBounds
  (residualFormTransfer_energy_le_max residualFormTransfer_energy_ge_min
   residualFormTransfer_energy_le_add formTransfer_energy_le_max
   formTransfer_energy_ge_min formTransfer_energy_le_add
   formTransfer_growingOutput_energy_le formTransfer_growing_energy_le)
open KFCausalClockFloorAveragedTimeControl
  (staticPart growingPart timeEnergy timeEnergy_actual timeEnergy_nonneg
   transported_form_norm reference_norm_identity)
open KFCausalClockFloorAveragedFormFlow
  (formFlow formFlow_initial formFlow_compose formFlow_reverse formFlow_physical_norm)
open KFCausalClockFloorStrongFormEvolution
  (formFlow_energy_bound timeEnergy_distance_comparison formFlow_local_norm_bound
   formFlow_continuous)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding evolution_norm)

private theorem prop_of_eq {X : Type*} (P : X → Prop) {x y : X} (hxy : x = y) (hx : P x) :
    P y :=
  (congrArg P hxy).mp hx

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem add_mul_add_eq (a e b c : ℝ) : a + e * (b + c) = a + e * b + e * c := by
  ring

private theorem three_channel_to_radial_residual (hE s r p res : ℝ)
    (h1 : hE = s + r + p) (h2 : res = s + p) : hE = r + res := by
  linarith

private theorem left_le_of_eq_add {a b c : ℝ} (h : c = a + b) (hb : 0 ≤ b) : a ≤ c := by
  linarith

private theorem right_le_of_eq_add {a b c : ℝ} (h : c = a + b) (ha : 0 ≤ a) : b ≤ c := by
  linarith

private theorem unscale_exp_le {t a b : ℝ} (h : Real.exp (2 * t) * a ≤ b) :
    a ≤ Real.exp (-2 * t) * b := by
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * t)).le
  have he : Real.exp (-2 * t) * (Real.exp (2 * t) * a) = a := by
    rw [← mul_assoc, ← Real.exp_add, show -2 * t + 2 * t = 0 by ring, Real.exp_zero, one_mul]
  rwa [he] at hm

private theorem exp_neg_mul_exp_abs_eq (t s : ℝ) :
    Real.exp (-2 * t) * Real.exp (2 * |t - s|) = Real.exp (2 * (|t - s| - t)) := by
  rw [← Real.exp_add, show -2 * t + 2 * |t - s| = 2 * (|t - s| - t) by ring]

private theorem unscale_exp_abs_le {s t a b : ℝ}
    (h : Real.exp (2 * t) * a ≤ Real.exp (2 * |t - s|) * b) :
    a ≤ Real.exp (2 * (|t - s| - t)) * b := by
  have h1 := unscale_exp_le h
  have heq : Real.exp (-2 * t) * (Real.exp (2 * |t - s|) * b) =
      Real.exp (2 * (|t - s| - t)) * b := by
    rw [← mul_assoc, exp_neg_mul_exp_abs_eq]
  exact h1.trans_eq heq

private theorem unscale_exp_forward_le {s t a b : ℝ} (hst : s ≤ t)
    (h : a ≤ Real.exp (2 * (|t - s| - t)) * b) :
    a ≤ Real.exp (-2 * s) * b := by
  have habs : |t - s| = t - s := abs_of_nonneg (sub_nonneg.mpr hst)
  have heq : Real.exp (2 * (|t - s| - t)) * b = Real.exp (-2 * s) * b := by
    rw [habs, show 2 * (t - s - t) = -2 * s by ring]
  exact h.trans_eq heq

private theorem mul_assoc_trans_le {a b c d e : ℝ} (hc : 0 ≤ c)
    (h1 : a ≤ c * b) (h2 : b ≤ d * e) :
    a ≤ c * d * e := by
  have hm := h1.trans (mul_le_mul_of_nonneg_left h2 hc)
  rwa [← mul_assoc] at hm

private theorem exp_dist_mul_le {s t r a b c : ℝ}
    (h1 : a ≤ Real.exp (2 * |t - r|) * b)
    (h2 : b ≤ Real.exp (2 * |t - s|) * c) :
    a ≤ Real.exp (2 * (|t - r| + |t - s|)) * c := by
  have hm := h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos (2 * |t - r|)).le)
  have hexp : Real.exp (2 * |t - r|) * (Real.exp (2 * |t - s|) * c) =
      Real.exp (2 * (|t - r| + |t - s|)) * c := by
    rw [← mul_assoc, ← Real.exp_add, show 2 * |t - r| + 2 * |t - s| = 2 * (|t - r| + |t - s|) by ring]
  exact hm.trans_eq hexp

private theorem zero_sub_max_eq (s t c : ℝ) :
    max 1 (Real.exp (2 * (0 - t))) * Real.exp (2 * |t - s|) * c =
      max 1 (Real.exp (-2 * t)) * Real.exp (2 * |t - s|) * c := by
  rw [show 2 * (0 - t) = -2 * t by ring]

private theorem zero_sub_dist_eq (s t c : ℝ) :
    Real.exp (2 * (|t - 0| + |t - s|)) * c =
      Real.exp (2 * (|t| + |t - s|)) * c := by
  rw [sub_zero]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "AJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k
local notation "RA" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "FT" => KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k
local notation "F" => formFlow ε hε h hh hw m g k
local notation "U" => evolution ε hε h hh hw m g k
local notation "E" => timeEnergy ε hε h hh hw m g k
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "GL" => KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "PL" => KFCausalClockFloorPotentialHamiltonian.referenceLift ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SJ" => fun r => KFCausalClosedGraphForm.embedding (SD r)
local notation "SB" => fun r => KFCausalClosedGraphForm.energyOutput (SD r)
local notation "SR" => KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k
local notation "R" => rootOutput ε hε h hh hw m g k

private theorem static_form_norm_sq_eq (v : TV) (f : Hilbert)
    (hJ : TJ v = f) (hf : f ∈ (Tstat).domain) :
    ‖TB v‖^2 = ‖Tstat ⟨f, hf⟩‖^2 := by
  have hfv : TJ v ∈ (Tstat).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Tstat).domain) hJ.symm hf
  let ru := KFCausalClosedGraphForm.graphVector (rootData ε hε h) ⟨TJ v, hfv⟩
  have h1 : (TJ v, TB v) ∈
      (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).graph :=
    v.property
  have h2 : (TJ v, KFCausalClockFloorStaticOutputClosure.extension ε hε h hh hw m g k 0 ru) ∈
      (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).graph :=
    KFCausalClockFloorStaticOutputClosure.root_form_graph ε hε h hh hw m g k 0 ru
  have heq : TB v = KFCausalClockFloorStaticOutputClosure.extension ε hε h hh hw m g k 0 ru :=
    (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).mem_graph_snd_inj'
      h1 h2 rfl
  have hn : ‖TB v‖ = ‖Tstat ⟨TJ v, hfv⟩‖ :=
    (congrArg norm heq).trans
      (KFCausalClockFloorStaticOutputClosure.extension_norm ε hε h hh hw m g k 0 ru)
  have hsub : (⟨TJ v, hfv⟩ : (Tstat).domain) = ⟨f, hf⟩ := Subtype.ext hJ
  exact congrArg (fun s : ℝ => s^2)
    (hn.trans (congrArg (fun z : (Tstat).domain => ‖Tstat z‖) hsub))

private theorem radial_root_output_eq (u : GV) (f : Hilbert)
    (hJ : GJ u = f) (hf : f ∈ (Kroot).domain) :
    R u = Kroot ⟨f, hf⟩ :=
  (Kroot).mem_graph_snd_inj' (rootOutput_graph ε hε h hh hw m g k u)
    ((Kroot).mem_graph ⟨f, hf⟩) hJ

/-! ### Reference Form Five-Operator Domain Membership and Exact Energy Decompositions -/

theorem reference_mem_averaged_domain (r : ℝ) (w : RV) :
    RJ w ∈ (Eavg r).domain := by
  let wr := FT 0 r w
  have hdom : AJ r wr ∈ (Eavg r).domain := LinearPMap.mem_domain_of_mem_graph wr.property
  exact prop_of_eq (fun x : Hilbert => x ∈ (Eavg r).domain)
    (KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k 0 r w) hdom

theorem reference_mem_staticRoot_domain (w : RV) :
    RJ w ∈ (Tstat).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k 0 (RJ w) (reference_mem_averaged_domain ε hε h hh hb m g k 0 w)).1

theorem reference_mem_radialRoot_domain (w : RV) :
    RJ w ∈ (Kroot).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k 0 (RJ w) (reference_mem_averaged_domain ε hε h hh hb m g k 0 w)).2.1

theorem reference_mem_potentialForm_domain (w : RV) :
    RJ w ∈ (Tpot).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k 0 (RJ w) (reference_mem_averaged_domain ε hε h hh hb m g k 0 w)).2.2

theorem reference_mem_growingForm_domain (w : RV) :
    RJ w ∈ (Tgrow).domain :=
  ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k 0 (RJ w)).mp
    (reference_mem_averaged_domain ε hε h hh hb m g k 0 w)).1

theorem reference_mem_residualForm_domain (r : ℝ) (w : RV) :
    RJ w ∈ (Tres r).domain :=
  ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k r (RJ w)).mp
    (reference_mem_averaged_domain ε hε h hh hb m g k r w)).2

theorem reference_mem_five_operator_domains (r : ℝ) (w : RV) :
    RJ w ∈ ((Tstat).domain : Set Hilbert) ∩ (Kroot).domain ∩ (Tpot).domain ∩
      (Tgrow).domain ∩ (Tres r).domain :=
  ⟨⟨⟨⟨reference_mem_staticRoot_domain ε hε h hh hb m g k w,
      reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩,
     reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩,
    reference_mem_growingForm_domain ε hε h hh hb m g k w⟩,
   reference_mem_residualForm_domain ε hε h hh hb m g k r w⟩

theorem reference_staticRoot_norm_sq_eq (w : RV) :
    ‖staticPart ε hε h hh hw m g k w‖^2 =
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 := by
  let v := staticLift ε hε h hh hw m g k 0 (SR 0 w)
  have hTB : TB v = staticPart ε hε h hh hw m g k w :=
    source_static ε hε h hh hw m g k 0 w
  have hTJ : TJ v = RJ w :=
    (staticLift_embedding ε hε h hh hw m g k 0 (SR 0 w)).trans
      (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k 0 w)
  exact (congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hTB.symm).trans
    (static_form_norm_sq_eq ε hε h hh hb m g k v (RJ w) hTJ
      (reference_mem_staticRoot_domain ε hε h hh hb m g k w))

theorem reference_growingForm_output_eq (w : RV) :
    GB (GL w) =
      Tgrow ⟨RJ w, reference_mem_growingForm_domain ε hε h hh hb m g k w⟩ :=
  form_output_eq_operator GD (GL w) (RJ w)
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k w)
    (reference_mem_growingForm_domain ε hε h hh hb m g k w)

theorem reference_growingForm_norm_sq_eq (w : RV) :
    ‖growingPart ε hε h hh hw m g k w‖^2 =
      ‖Tgrow ⟨RJ w, reference_mem_growingForm_domain ε hε h hh hb m g k w⟩‖^2 :=
  congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
    ((KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k w).symm.trans
      (reference_growingForm_output_eq ε hε h hh hb m g k w))

theorem reference_radialRoot_output_eq (w : RV) :
    R (GL w) =
      Kroot ⟨RJ w, reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩ :=
  radial_root_output_eq ε hε h hh hb m g k (GL w) (RJ w)
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k w)
    (reference_mem_radialRoot_domain ε hε h hh hb m g k w)

theorem reference_potentialForm_output_eq (r : ℝ) (w : RV) :
    PB (potentialLift ε hε h hh hw m g k r (SR r w)) =
      Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩ :=
  form_output_eq_operator PD (potentialLift ε hε h hh hw m g k r (SR r w)) (RJ w)
    ((potentialLift_embedding ε hε h hh hw m g k r (SR r w)).trans
      (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k r w))
    (reference_mem_potentialForm_domain ε hε h hh hb m g k w)

theorem reference_residualForm_output_eq (r : ℝ) (w : RV) :
    SB r (SR r w) =
      Tres r ⟨RJ w, reference_mem_residualForm_domain ε hε h hh hb m g k r w⟩ :=
  form_output_eq_operator (SD r) (SR r w) (RJ w)
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
      ε hε h hh hw m g k r w)
    (reference_mem_residualForm_domain ε hε h hh hb m g k r w)

theorem reference_growing_norm_sq_split (w : RV) :
    ‖Tgrow ⟨RJ w, reference_mem_growingForm_domain ε hε h hh hb m g k w⟩‖^2 =
      ‖Kroot ⟨RJ w, reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        ‖Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩‖^2 := by
  have hg := growing_output_norm_sq ε hε h hb hh m g k (GL w)
  have h1 : ‖GB (GL w)‖^2 =
      ‖Tgrow ⟨RJ w, reference_mem_growingForm_domain ε hε h hh hb m g k w⟩‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (reference_growingForm_output_eq ε hε h hh hb m g k w)
  have h2 : ‖R (GL w)‖^2 =
      ‖Kroot ⟨RJ w, reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩‖^2 :=
    congrArg (fun z : Hilbert => ‖z‖^2)
      (reference_radialRoot_output_eq ε hε h hh hb m g k w)
  have hp_eq : growingLift ε hε h hh hw m g k (GL w) =
      potentialLift ε hε h hh hw m g k 0 (SR 0 w) := by
    apply KFCausalClosedGraphForm.embedding_injective PD
    exact ((growingLift_embedding ε hε h hh hw m g k (GL w)).trans
      (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k w)).trans
      ((potentialLift_embedding ε hε h hh hw m g k 0 (SR 0 w)).trans
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
          ε hε h hh hw m g k 0 w)).symm
  have h3 : ‖PB (growingLift ε hε h hh hw m g k (GL w))‖^2 =
      ‖Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩‖^2 :=
    (congrArg (fun v => ‖PB v‖^2) hp_eq).trans
      (congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
        (reference_potentialForm_output_eq ε hε h hh hb m g k 0 w))
  exact h1.symm.trans (hg.trans (congrArg₂ (· + ·) h2 h3))

theorem reference_residual_norm_sq_split (r : ℝ) (w : RV) :
    ‖Tres r ⟨RJ w, reference_mem_residualForm_domain ε hε h hh hb m g k r w⟩‖^2 =
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩‖^2 := by
  have hres := residual_norm_split ε hε h hh hw m g k r (SR r w)
  have h1 : ‖SB r (SR r w)‖^2 =
      ‖Tres r ⟨RJ w, reference_mem_residualForm_domain ε hε h hh hb m g k r w⟩‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (reference_residualForm_output_eq ε hε h hh hb m g k r w)
  have h2 : ‖TB (staticLift ε hε h hh hw m g k r (SR r w))‖^2 =
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 :=
    static_form_norm_sq_eq ε hε h hh hb m g k
      (staticLift ε hε h hh hw m g k r (SR r w)) (RJ w)
      ((staticLift_embedding ε hε h hh hw m g k r (SR r w)).trans
        (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
          ε hε h hh hw m g k r w))
      (reference_mem_staticRoot_domain ε hε h hh hb m g k w)
  have h3 : ‖PB (potentialLift ε hε h hh hw m g k r (SR r w))‖^2 =
      ‖Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (reference_potentialForm_output_eq ε hε h hh hb m g k r w)
  exact h1.symm.trans
    (hres.trans (congrArg₂ (· + ·) h2 (congrArg (Real.exp (2 * r) * ·) h3)))

theorem reference_timeEnergy_eq_static_add_growing (r : ℝ) (w : RV) :
    E r w =
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tgrow ⟨RJ w, reference_mem_growingForm_domain ε hε h hh hb m g k w⟩‖^2 := by
  unfold timeEnergy
  exact congrArg₂ (· + ·)
    (reference_staticRoot_norm_sq_eq ε hε h hh hb m g k w)
    (congrArg (Real.exp (2 * r) * ·)
      (reference_growingForm_norm_sq_eq ε hε h hh hb m g k w))

theorem reference_timeEnergy_eq_three_channel (r : ℝ) (w : RV) :
    E r w =
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        Real.exp (2 * r) *
          ‖Kroot ⟨RJ w, reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tpot ⟨RJ w, reference_mem_potentialForm_domain ε hε h hh hb m g k w⟩‖^2 :=
  (reference_timeEnergy_eq_static_add_growing ε hε h hh hb m g k r w).trans
    ((congrArg (fun s : ℝ =>
      ‖Tstat ⟨RJ w, reference_mem_staticRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        Real.exp (2 * r) * s)
      (reference_growing_norm_sq_split ε hε h hh hb m g k w)).trans
      (add_mul_add_eq _ _ _ _))

theorem reference_timeEnergy_eq_radial_add_residual (r : ℝ) (w : RV) :
    E r w =
      Real.exp (2 * r) *
          ‖Kroot ⟨RJ w, reference_mem_radialRoot_domain ε hε h hh hb m g k w⟩‖^2 +
        ‖Tres r ⟨RJ w, reference_mem_residualForm_domain ε hε h hh hb m g k r w⟩‖^2 :=
  three_channel_to_radial_residual _ _ _ _ _
    (reference_timeEnergy_eq_three_channel ε hε h hh hb m g k r w)
    (reference_residual_norm_sq_split ε hε h hh hb m g k r w)

/-! ### Evolved Form Trajectory Regularity and Five-Operator Domain Membership -/

def evolvedForm (s t r : ℝ) (u : RV) : VT r :=
  FT 0 r (F s t u)

def evolvedState (s t : ℝ) (u : RV) : Hilbert :=
  U s t (RJ u)

def referenceFormEnergy (s t : ℝ) (u : RV) : ℝ :=
  E 0 (F s t u)

def instantFormEnergy (s t r : ℝ) (u : RV) : ℝ :=
  E r (F s t u)

theorem evolvedForm_embedding (s t r : ℝ) (u : RV) :
    AJ r (evolvedForm ε hε h hh hb m g k s t r u) = U s t (RJ u) :=
  (KFCausalClockFloorAveragedFormTransport.transfer_embedding
    ε hε h hh hw m g k 0 r (F s t u)).trans
    (evolution_embedding ε hε h hh hw m g k s t u).symm

theorem evolvedForm_zero_eq_formFlow (s t : ℝ) (u : RV) :
    evolvedForm ε hε h hh hb m g k s t 0 u = F s t u :=
  KFCausalClockFloorAveragedFormTransport.transfer_self ε hε h hh hw m g k 0 (F s t u)

theorem evolvedForm_transfer (s t r₁ r₂ : ℝ) (u : RV) :
    FT r₁ r₂ (evolvedForm ε hε h hh hb m g k s t r₁ u) =
      evolvedForm ε hε h hh hb m g k s t r₂ u :=
  KFCausalClockFloorAveragedFormTransport.transfer_comp ε hε h hh hw m g k 0 r₁ r₂ (F s t u)

theorem instantFormEnergy_eq_output_norm_sq (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u =
      ‖AT r (evolvedForm ε hε h hh hb m g k s t r u)‖^2 :=
  (timeEnergy_actual ε hε h hh hw m g k r (F s t u)).symm

theorem referenceFormEnergy_eq_instant_zero (s t : ℝ) (u : RV) :
    referenceFormEnergy ε hε h hh hb m g k s t u =
      instantFormEnergy ε hε h hh hb m g k s t 0 u := rfl

theorem evolved_mem_reference_range (s t : ℝ) (u : RV) :
    U s t (RJ u) ∈ Set.range RJ :=
  ⟨F s t u, (evolution_embedding ε hε h hh hw m g k s t u).symm⟩

theorem evolved_mem_time_range (s t r : ℝ) (u : RV) :
    U s t (RJ u) ∈ Set.range (AJ r) :=
  ⟨evolvedForm ε hε h hh hb m g k s t r u,
    evolvedForm_embedding ε hε h hh hb m g k s t r u⟩

theorem evolved_mem_averaged_domain (s t r : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Eavg r).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Eavg r).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_averaged_domain ε hε h hh hb m g k r (F s t u))

theorem evolved_mem_staticRoot_domain (s t : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Tstat).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Tstat).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_staticRoot_domain ε hε h hh hb m g k (F s t u))

theorem evolved_mem_radialRoot_domain (s t : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Kroot).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Kroot).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_radialRoot_domain ε hε h hh hb m g k (F s t u))

theorem evolved_mem_potentialForm_domain (s t : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Tpot).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Tpot).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_potentialForm_domain ε hε h hh hb m g k (F s t u))

theorem evolved_mem_growingForm_domain (s t : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Tgrow).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Tgrow).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_growingForm_domain ε hε h hh hb m g k (F s t u))

theorem evolved_mem_residualForm_domain (s t r : ℝ) (u : RV) :
    U s t (RJ u) ∈ (Tres r).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Tres r).domain)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_residualForm_domain ε hε h hh hb m g k r (F s t u))

theorem evolved_mem_five_operator_domains (s t r : ℝ) (u : RV) :
    U s t (RJ u) ∈ ((Tstat).domain : Set Hilbert) ∩ (Kroot).domain ∩ (Tpot).domain ∩
      (Tgrow).domain ∩ (Tres r).domain :=
  ⟨⟨⟨⟨evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u,
      evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩,
     evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩,
    evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩,
   evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩

/-! ### Evolved Trajectory Decompositions and Two-Time Form-Energy Bounds -/

private theorem operator_norm_sq_congr
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : Hilbert →ₗ.[ℂ] Y) {x y : Hilbert} (hxy : x = y)
    (hx : x ∈ T.domain) (hy : y ∈ T.domain) :
    ‖T ⟨x, hx⟩‖^2 = ‖T ⟨y, hy⟩‖^2 := by
  have hsub : (⟨x, hx⟩ : T.domain) = ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg (fun z : T.domain => ‖T z‖^2) hsub

private theorem evolvedForm_transfer_output_norm_sq (s t r₁ r₂ : ℝ) (u : RV) :
    ‖AT r₂ (FT r₁ r₂ (evolvedForm ε hε h hh hb m g k s t r₁ u))‖^2 =
      instantFormEnergy ε hε h hh hb m g k s t r₂ u :=
  (congrArg (fun v : VT r₂ => ‖AT r₂ v‖^2)
    (evolvedForm_transfer ε hε h hh hb m g k s t r₁ r₂ u)).trans
    (instantFormEnergy_eq_output_norm_sq ε hε h hh hb m g k s t r₂ u).symm

theorem evolved_instantFormEnergy_eq_static_add_growing (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u =
      ‖Tstat ⟨U s t (RJ u), evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tgrow ⟨U s t (RJ u), evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩‖^2 := by
  have h0 := reference_timeEnergy_eq_static_add_growing ε hε h hh hb m g k r (F s t u)
  have h1 := operator_norm_sq_congr Tstat
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_staticRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u)
  have h2 := operator_norm_sq_congr Tgrow
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_growingForm_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_growingForm_domain ε hε h hh hb m g k s t u)
  exact h0.trans (congrArg₂ (· + ·) h1 (congrArg (Real.exp (2 * r) * ·) h2))

theorem evolved_instantFormEnergy_eq_three_channel (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u =
      ‖Tstat ⟨U s t (RJ u), evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        Real.exp (2 * r) *
          ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 := by
  have h0 := reference_timeEnergy_eq_three_channel ε hε h hh hb m g k r (F s t u)
  have h1 := operator_norm_sq_congr Tstat
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_staticRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u)
  have h2 := operator_norm_sq_congr Kroot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_radialRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u)
  have h3 := operator_norm_sq_congr Tpot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_potentialForm_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u)
  exact h0.trans
    (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) h1 (congrArg (Real.exp (2 * r) * ·) h2))
      (congrArg (Real.exp (2 * r) * ·) h3))

theorem evolved_instantFormEnergy_eq_radial_add_residual (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u =
      Real.exp (2 * r) *
          ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        ‖Tres r ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩‖^2 := by
  have h0 := reference_timeEnergy_eq_radial_add_residual ε hε h hh hb m g k r (F s t u)
  have h1 := operator_norm_sq_congr Kroot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_radialRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u)
  have h2 := operator_norm_sq_congr (Tres r)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_residualForm_domain ε hε h hh hb m g k r (F s t u))
    (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u)
  exact h0.trans (congrArg₂ (· + ·) (congrArg (Real.exp (2 * r) * ·) h1) h2)

theorem evolved_growing_norm_sq_split (s t : ℝ) (u : RV) :
    ‖Tgrow ⟨U s t (RJ u), evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩‖^2 =
      ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 := by
  have h0 := reference_growing_norm_sq_split ε hε h hh hb m g k (F s t u)
  have h1 := operator_norm_sq_congr Tgrow
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_growingForm_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_growingForm_domain ε hε h hh hb m g k s t u)
  have h2 := operator_norm_sq_congr Kroot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_radialRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u)
  have h3 := operator_norm_sq_congr Tpot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_potentialForm_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u)
  exact h1.symm.trans (h0.trans (congrArg₂ (· + ·) h2 h3))

theorem evolved_residual_norm_sq_split (s t r : ℝ) (u : RV) :
    ‖Tres r ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩‖^2 =
      ‖Tstat ⟨U s t (RJ u), evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u⟩‖^2 +
        Real.exp (2 * r) *
          ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 := by
  have h0 := reference_residual_norm_sq_split ε hε h hh hb m g k r (F s t u)
  have h1 := operator_norm_sq_congr (Tres r)
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_residualForm_domain ε hε h hh hb m g k r (F s t u))
    (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u)
  have h2 := operator_norm_sq_congr Tstat
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_staticRoot_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u)
  have h3 := operator_norm_sq_congr Tpot
    (evolution_embedding ε hε h hh hw m g k s t u).symm
    (reference_mem_potentialForm_domain ε hε h hh hb m g k (F s t u))
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u)
  exact h1.symm.trans (h0.trans (congrArg₂ (· + ·) h2 (congrArg (Real.exp (2 * r) * ·) h3)))

theorem evolved_dynamical_energy_le (s t : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t t u ≤
      Real.exp (2 * |t - s|) * E s u :=
  formFlow_energy_bound ε hε h hh hw m g k s t u

theorem evolved_instantFormEnergy_le_max_dynamical (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u ≤
      max 1 (Real.exp (2 * (r - t))) *
        instantFormEnergy ε hε h hh hb m g k s t t u :=
  (evolvedForm_transfer_output_norm_sq ε hε h hh hb m g k s t t r u).symm.trans_le
    ((formTransfer_energy_le_max ε hε h hh hb m g k r t
      (evolvedForm ε hε h hh hb m g k s t t u)).trans_eq
      (congrArg (max 1 (Real.exp (2 * (r - t))) * ·)
        (instantFormEnergy_eq_output_norm_sq ε hε h hh hb m g k s t t u).symm))

theorem evolved_instantFormEnergy_ge_min_dynamical (s t r : ℝ) (u : RV) :
    min 1 (Real.exp (2 * (r - t))) *
        instantFormEnergy ε hε h hh hb m g k s t t u ≤
      instantFormEnergy ε hε h hh hb m g k s t r u :=
  (congrArg (min 1 (Real.exp (2 * (r - t))) * ·)
    (instantFormEnergy_eq_output_norm_sq ε hε h hh hb m g k s t t u)).trans_le
    ((formTransfer_energy_ge_min ε hε h hh hb m g k r t
      (evolvedForm ε hε h hh hb m g k s t t u)).trans_eq
      (evolvedForm_transfer_output_norm_sq ε hε h hh hb m g k s t t r u))

theorem evolved_instantFormEnergy_le_max_initial (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * E s u :=
  mul_assoc_trans_le
    (le_trans zero_le_one (le_max_left 1 (Real.exp (2 * (r - t)))))
    (evolved_instantFormEnergy_le_max_dynamical ε hε h hh hb m g k s t r u)
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_instantFormEnergy_le_add_initial (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u ≤
      (1 + Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * E s u :=
  mul_assoc_trans_le
    (add_nonneg zero_le_one (Real.exp_pos (2 * (r - t))).le)
    ((evolvedForm_transfer_output_norm_sq ε hε h hh hb m g k s t t r u).symm.trans_le
      ((formTransfer_energy_le_add ε hε h hh hb m g k r t
        (evolvedForm ε hε h hh hb m g k s t t u)).trans_eq
        (congrArg ((1 + Real.exp (2 * (r - t))) * ·)
          (instantFormEnergy_eq_output_norm_sq ε hε h hh hb m g k s t t u).symm)))
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_instantFormEnergy_le_exp_distance (s t r : ℝ) (u : RV) :
    instantFormEnergy ε hε h hh hb m g k s t r u ≤
      Real.exp (2 * (|t - r| + |t - s|)) * E s u :=
  exp_dist_mul_le
    (timeEnergy_distance_comparison ε hε h hh hw m g k r t (F s t u))
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_referenceFormEnergy_le_max_initial (s t : ℝ) (u : RV) :
    referenceFormEnergy ε hε h hh hb m g k s t u ≤
      max 1 (Real.exp (-2 * t)) * Real.exp (2 * |t - s|) * E s u :=
  (evolved_instantFormEnergy_le_max_initial ε hε h hh hb m g k s t 0 u).trans_eq
    (zero_sub_max_eq s t (E s u))

theorem evolved_referenceFormEnergy_le_exp_distance (s t : ℝ) (u : RV) :
    referenceFormEnergy ε hε h hh hb m g k s t u ≤
      Real.exp (2 * (|t| + |t - s|)) * E s u :=
  (evolved_instantFormEnergy_le_exp_distance ε hε h hh hb m g k s t 0 u).trans_eq
    (zero_sub_dist_eq s t (E s u))

theorem evolvedForm_norm_sq_eq (s t r : ℝ) (u : RV) :
    ‖evolvedForm ε hε h hh hb m g k s t r u‖^2 =
      ‖RJ u‖^2 + instantFormEnergy ε hε h hh hb m g k s t r u :=
  (transported_form_norm ε hε h hh hw m g k r (F s t u)).trans
    (congrArg (fun a : ℝ => a^2 + instantFormEnergy ε hε h hh hb m g k s t r u)
      (formFlow_physical_norm ε hε h hh hw m g k s t u))

theorem evolvedForm_norm_sq_le_max_initial (s t r : ℝ) (u : RV) :
    ‖evolvedForm ε hε h hh hb m g k s t r u‖^2 ≤
      ‖RJ u‖^2 + max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * E s u :=
  (evolvedForm_norm_sq_eq ε hε h hh hb m g k s t r u).trans_le
    (add_le_add le_rfl (evolved_instantFormEnergy_le_max_initial ε hε h hh hb m g k s t r u))

theorem formFlow_reference_norm_sq_le_max_initial (s t : ℝ) (u : RV) :
    ‖F s t u‖^2 ≤
      ‖RJ u‖^2 + max 1 (Real.exp (-2 * t)) * Real.exp (2 * |t - s|) * E s u :=
  (congrArg (fun v : RV => ‖v‖^2)
    (evolvedForm_zero_eq_formFlow ε hε h hh hb m g k s t u).symm).trans_le
    ((evolvedForm_norm_sq_le_max_initial ε hε h hh hb m g k s t 0 u).trans_eq
      (congrArg (‖RJ u‖^2 + ·) (zero_sub_max_eq s t (E s u))))

/-! ### Five-Operator Component Form-Energy Bounds Along the Evolved Trajectory -/

theorem evolved_staticRoot_norm_sq_le (s t : ℝ) (u : RV) :
    ‖Tstat ⟨U s t (RJ u), evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * E s u :=
  (left_le_of_eq_add
    (evolved_instantFormEnergy_eq_static_add_growing ε hε h hh hb m g k s t t u)
    (mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _))).trans
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_staticRoot_norm_sq_le_total (s t : ℝ) (u : RV) :
    ‖Tstat ⟨U s t (RJ u), evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * (E s u + ‖RJ u‖^2) :=
  (evolved_staticRoot_norm_sq_le ε hε h hh hb m g k s t u).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _))
      (Real.exp_pos (2 * |t - s|)).le)

theorem evolved_weighted_growingForm_norm_sq_le (s t : ℝ) (u : RV) :
    Real.exp (2 * t) *
        ‖Tgrow ⟨U s t (RJ u), evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * E s u :=
  (right_le_of_eq_add
    (evolved_instantFormEnergy_eq_static_add_growing ε hε h hh hb m g k s t t u)
    (sq_nonneg _)).trans
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_growingForm_norm_sq_le (s t : ℝ) (u : RV) :
    ‖Tgrow ⟨U s t (RJ u), evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * (|t - s| - t)) * E s u :=
  unscale_exp_abs_le (evolved_weighted_growingForm_norm_sq_le ε hε h hh hb m g k s t u)

theorem evolved_growingForm_norm_sq_le_forward (s t : ℝ) (hst : s ≤ t) (u : RV) :
    ‖Tgrow ⟨U s t (RJ u), evolved_mem_growingForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (-2 * s) * E s u :=
  unscale_exp_forward_le hst (evolved_growingForm_norm_sq_le ε hε h hh hb m g k s t u)

theorem evolved_weighted_radialRoot_norm_sq_le (s t : ℝ) (u : RV) :
    Real.exp (2 * t) *
        ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * E s u :=
  (left_le_of_eq_add
    (evolved_instantFormEnergy_eq_radial_add_residual ε hε h hh hb m g k s t t u)
    (sq_nonneg _)).trans
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_radialRoot_norm_sq_le (s t : ℝ) (u : RV) :
    ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * (|t - s| - t)) * E s u :=
  unscale_exp_abs_le (evolved_weighted_radialRoot_norm_sq_le ε hε h hh hb m g k s t u)

theorem evolved_radialRoot_norm_sq_le_forward (s t : ℝ) (hst : s ≤ t) (u : RV) :
    ‖Kroot ⟨U s t (RJ u), evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (-2 * s) * E s u :=
  (left_le_of_eq_add (evolved_growing_norm_sq_split ε hε h hh hb m g k s t u)
    (sq_nonneg _)).trans
    (evolved_growingForm_norm_sq_le_forward ε hε h hh hb m g k s t hst u)

theorem evolved_weighted_potentialForm_norm_sq_le (s t : ℝ) (u : RV) :
    Real.exp (2 * t) *
        ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * E s u :=
  (right_le_of_eq_add
    (evolved_instantFormEnergy_eq_three_channel ε hε h hh hb m g k s t t u)
    (add_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _)))).trans
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_potentialForm_norm_sq_le (s t : ℝ) (u : RV) :
    ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (2 * (|t - s| - t)) * E s u :=
  unscale_exp_abs_le (evolved_weighted_potentialForm_norm_sq_le ε hε h hh hb m g k s t u)

theorem evolved_potentialForm_norm_sq_le_forward (s t : ℝ) (hst : s ≤ t) (u : RV) :
    ‖Tpot ⟨U s t (RJ u), evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u⟩‖^2 ≤
      Real.exp (-2 * s) * E s u :=
  (right_le_of_eq_add (evolved_growing_norm_sq_split ε hε h hh hb m g k s t u)
    (sq_nonneg _)).trans
    (evolved_growingForm_norm_sq_le_forward ε hε h hh hb m g k s t hst u)

theorem evolved_dynamical_residualForm_norm_sq_le (s t : ℝ) (u : RV) :
    ‖Tres t ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t t u⟩‖^2 ≤
      Real.exp (2 * |t - s|) * E s u :=
  (right_le_of_eq_add
    (evolved_instantFormEnergy_eq_radial_add_residual ε hε h hh hb m g k s t t u)
    (mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _))).trans
    (evolved_dynamical_energy_le ε hε h hh hb m g k s t u)

theorem evolved_residualForm_norm_sq_le_instantFormEnergy (s t r : ℝ) (u : RV) :
    ‖Tres r ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩‖^2 ≤
      instantFormEnergy ε hε h hh hb m g k s t r u :=
  right_le_of_eq_add
    (evolved_instantFormEnergy_eq_radial_add_residual ε hε h hh hb m g k s t r u)
    (mul_nonneg (Real.exp_pos (2 * r)).le (sq_nonneg _))

theorem evolved_residualForm_norm_sq_le_max_initial (s t r : ℝ) (u : RV) :
    ‖Tres r ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩‖^2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * E s u :=
  (evolved_residualForm_norm_sq_le_instantFormEnergy ε hε h hh hb m g k s t r u).trans
    (evolved_instantFormEnergy_le_max_initial ε hε h hh hb m g k s t r u)

theorem evolved_residualForm_norm_sq_le_max_total (s t r : ℝ) (u : RV) :
    ‖Tres r ⟨U s t (RJ u), evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u⟩‖^2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * (E s u + ‖RJ u‖^2) :=
  (evolved_residualForm_norm_sq_le_max_initial ε hε h hh hb m g k s t r u).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _))
      (mul_nonneg (le_trans zero_le_one (le_max_left 1 (Real.exp (2 * (r - t)))))
        (Real.exp_pos (2 * |t - s|)).le))

#print axioms reference_mem_averaged_domain
#print axioms reference_mem_staticRoot_domain
#print axioms reference_mem_radialRoot_domain
#print axioms reference_mem_potentialForm_domain
#print axioms reference_mem_growingForm_domain
#print axioms reference_mem_residualForm_domain
#print axioms reference_mem_five_operator_domains
#print axioms reference_staticRoot_norm_sq_eq
#print axioms reference_growingForm_output_eq
#print axioms reference_growingForm_norm_sq_eq
#print axioms reference_radialRoot_output_eq
#print axioms reference_potentialForm_output_eq
#print axioms reference_residualForm_output_eq
#print axioms reference_growing_norm_sq_split
#print axioms reference_residual_norm_sq_split
#print axioms reference_timeEnergy_eq_static_add_growing
#print axioms reference_timeEnergy_eq_three_channel
#print axioms reference_timeEnergy_eq_radial_add_residual
#print axioms evolvedForm_embedding
#print axioms evolvedForm_zero_eq_formFlow
#print axioms evolvedForm_transfer
#print axioms instantFormEnergy_eq_output_norm_sq
#print axioms referenceFormEnergy_eq_instant_zero
#print axioms evolved_mem_reference_range
#print axioms evolved_mem_time_range
#print axioms evolved_mem_averaged_domain
#print axioms evolved_mem_staticRoot_domain
#print axioms evolved_mem_radialRoot_domain
#print axioms evolved_mem_potentialForm_domain
#print axioms evolved_mem_growingForm_domain
#print axioms evolved_mem_residualForm_domain
#print axioms evolved_mem_five_operator_domains
#print axioms evolved_instantFormEnergy_eq_static_add_growing
#print axioms evolved_instantFormEnergy_eq_three_channel
#print axioms evolved_instantFormEnergy_eq_radial_add_residual
#print axioms evolved_growing_norm_sq_split
#print axioms evolved_residual_norm_sq_split
#print axioms evolved_dynamical_energy_le
#print axioms evolved_instantFormEnergy_le_max_dynamical
#print axioms evolved_instantFormEnergy_ge_min_dynamical
#print axioms evolved_instantFormEnergy_le_max_initial
#print axioms evolved_instantFormEnergy_le_add_initial
#print axioms evolved_instantFormEnergy_le_exp_distance
#print axioms evolved_referenceFormEnergy_le_max_initial
#print axioms evolved_referenceFormEnergy_le_exp_distance
#print axioms evolvedForm_norm_sq_eq
#print axioms evolvedForm_norm_sq_le_max_initial
#print axioms formFlow_reference_norm_sq_le_max_initial
#print axioms evolved_staticRoot_norm_sq_le
#print axioms evolved_staticRoot_norm_sq_le_total
#print axioms evolved_weighted_growingForm_norm_sq_le
#print axioms evolved_growingForm_norm_sq_le
#print axioms evolved_growingForm_norm_sq_le_forward
#print axioms evolved_weighted_radialRoot_norm_sq_le
#print axioms evolved_radialRoot_norm_sq_le
#print axioms evolved_radialRoot_norm_sq_le_forward
#print axioms evolved_weighted_potentialForm_norm_sq_le
#print axioms evolved_potentialForm_norm_sq_le
#print axioms evolved_potentialForm_norm_sq_le_forward
#print axioms evolved_dynamical_residualForm_norm_sq_le
#print axioms evolved_residualForm_norm_sq_le_instantFormEnergy
#print axioms evolved_residualForm_norm_sq_le_max_initial
#print axioms evolved_residualForm_norm_sq_le_max_total
end
end UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormEnergyRegularity
