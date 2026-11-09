/- Unconditional operator-to-form energy decompositions for all real couplings
and physical times: every vector in Dom H(t) lies in the static square-root,
radial square-root, potential, growing, and residual form domains, and the
quadratic form Re <H(t)x, x> decomposes into its two-channel (static + growing,
radial + residual) and three-channel (static + radial + potential) form energies,
along with the corresponding decompositions for S(t) and G. -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalOperatorFormEnergy
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorStaticRootSource (rootData)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput rootOutput_graph)
open KFCausalClockFloorResidualFormSplit (staticLift staticLift_embedding
  potentialLift potentialLift_embedding residual_norm_split source_static)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding growingLift_output)
open KFCausalClockFloorRadialResolventGrowing (growing_output_norm_sq)

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f,hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f,hf⟩) hJ

private theorem norm_sq_of_inner_split {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (y z : K) (q : ℂ) (c : ℝ)
    (h : q = inner ℂ y y + (c:ℂ)*inner ℂ z z) :
    q.re = ‖y‖^2 + c*‖z‖^2 := by
  have hi := congrArg Complex.re h
  rw [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hi
  exact hi.trans (congrArg₂ (·+·) (inner_self_eq_norm_sq (𝕜 := ℂ) y)
    (congrArg (c*·) (inner_self_eq_norm_sq (𝕜 := ℂ) z)))

private theorem add_mul_add_eq (a e b c : ℝ) : a+e*(b+c) = a+e*b+e*c := by ring

private theorem three_channel_to_radial_residual (hE s r p res : ℝ)
    (h1 : hE = s+r+p) (h2 : res = s+p) : hE = r+res := by linarith

private theorem growing_add_residual_from_parts (g r p res hE e : ℝ)
    (h1 : hE = e*r+res) (hg : g = r+p) : e*g+res = hE+e*p := by
  rw [hg,h1]
  ring

private theorem left_le_of_eq_add {a b c : ℝ} (h : c = a+b) (hb : 0 ≤ b) : a ≤ c := by linarith
private theorem right_le_of_eq_add {a b c : ℝ} (h : c = a+b) (ha : 0 ≤ a) : b ≤ c := by linarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SJ" => fun t => KFCausalClosedGraphForm.embedding (SD t)
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "HD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
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
    ‖TB v‖^2 = ‖Tstat ⟨f,hf⟩‖^2 := by
  have hfv : TJ v ∈ (Tstat).domain := hJ.symm ▸ hf
  let ru := KFCausalClosedGraphForm.graphVector (rootData ε hε h) ⟨TJ v,hfv⟩
  have h1 : (TJ v,TB v) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).graph :=
    v.property
  have h2 : (TJ v,KFCausalClockFloorStaticOutputClosure.extension ε hε h hh hw m g k 0 ru) ∈
      (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).graph :=
    KFCausalClockFloorStaticOutputClosure.root_form_graph ε hε h hh hw m g k 0 ru
  have heq : TB v = KFCausalClockFloorStaticOutputClosure.extension ε hε h hh hw m g k 0 ru :=
    (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hw m g k 0).mem_graph_snd_inj' h1 h2 rfl
  have hn : ‖TB v‖ = ‖Tstat ⟨TJ v,hfv⟩‖ :=
    (congrArg norm heq).trans (KFCausalClockFloorStaticOutputClosure.extension_norm ε hε h hh hw m g k 0 ru)
  have hsub : (⟨TJ v,hfv⟩ : (Tstat).domain) = ⟨f,hf⟩ := Subtype.ext hJ
  exact congrArg (fun s : ℝ => s^2) (hn.trans (congrArg (fun z : (Tstat).domain => ‖Tstat z‖) hsub))

private theorem radial_root_output_eq (u : GV) (f : Hilbert)
    (hJ : GJ u = f) (hf : f ∈ (Kroot).domain) :
    R u = Kroot ⟨f,hf⟩ :=
  (Kroot).mem_graph_snd_inj' (rootOutput_graph ε hε h hh hw m g k u)
    ((Kroot).mem_graph ⟨f,hf⟩) hJ

/-! ### Growing Hamiltonian Form Energy -/

theorem growing_mem_growingForm_domain (x : (G).domain) :
    (x:Hilbert) ∈ (Tgrow).domain := by
  let u := KFCausalClosedGraphForm.formLift GD x
  have hJ : GJ u = (x:Hilbert) := KFCausalClosedGraphForm.embedding_formLift GD x
  exact hJ ▸ LinearPMap.mem_domain_of_mem_graph u.property

theorem growing_mem_radialRoot_domain (x : (G).domain) :
    (x:Hilbert) ∈ (Kroot).domain :=
  ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff ε hε h hh hb m g k (x:Hilbert)).mp
    (growing_mem_growingForm_domain ε hε h hh hb m g k x)).1

theorem growing_mem_potentialForm_domain (x : (G).domain) :
    (x:Hilbert) ∈ (Tpot).domain :=
  ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff ε hε h hh hb m g k (x:Hilbert)).mp
    (growing_mem_growingForm_domain ε hε h hh hb m g k x)).2

theorem growing_form_energy_eq_growingOutput (x : (G).domain) :
    (inner ℂ (G x) (x:Hilbert)).re =
      ‖Tgrow ⟨(x:Hilbert),growing_mem_growingForm_domain ε hε h hh hb m g k x⟩‖^2 := by
  let u := KFCausalClosedGraphForm.formLift GD x
  have hout := form_output_eq_operator GD u (x:Hilbert)
    (KFCausalClosedGraphForm.embedding_formLift GD x)
    (growing_mem_growingForm_domain ε hε h hh hb m g k x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy GD x).trans
    (congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hout)

theorem growing_form_energy_eq_lifts (x : (G).domain) :
    (inner ℂ (G x) (x:Hilbert)).re =
      ‖Kroot ⟨(x:Hilbert),growing_mem_radialRoot_domain ε hε h hh hb m g k x⟩‖^2+
        ‖PB (growingLift ε hε h hh hw m g k (KFCausalClosedGraphForm.formLift GD x))‖^2 := by
  let u := KFCausalClosedGraphForm.formLift GD x
  have hr := radial_root_output_eq ε hε h hh hb m g k u (x:Hilbert)
    (KFCausalClosedGraphForm.embedding_formLift GD x)
    (growing_mem_radialRoot_domain ε hε h hh hb m g k x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy GD x).trans
    ((growing_output_norm_sq ε hε h hb hh m g k u).trans
      (congrArg (fun z : Hilbert => ‖z‖^2+‖PB (growingLift ε hε h hh hw m g k u)‖^2) hr))

theorem growing_form_energy_eq_split (x : (G).domain) :
    (inner ℂ (G x) (x:Hilbert)).re =
      ‖Kroot ⟨(x:Hilbert),growing_mem_radialRoot_domain ε hε h hh hb m g k x⟩‖^2+
        ‖Tpot ⟨(x:Hilbert),growing_mem_potentialForm_domain ε hε h hh hb m g k x⟩‖^2 := by
  let u := KFCausalClosedGraphForm.formLift GD x
  have hPJ : PJ (growingLift ε hε h hh hw m g k u) = (x:Hilbert) :=
    (growingLift_embedding ε hε h hh hw m g k u).trans
      (KFCausalClosedGraphForm.embedding_formLift GD x)
  have hp := form_output_eq_operator PD (growingLift ε hε h hh hw m g k u) (x:Hilbert) hPJ
    (growing_mem_potentialForm_domain ε hε h hh hb m g k x)
  exact (growing_form_energy_eq_lifts ε hε h hh hb m g k x).trans
    (congrArg (fun y : EnergyOutputSpace =>
      ‖Kroot ⟨(x:Hilbert),growing_mem_radialRoot_domain ε hε h hh hb m g k x⟩‖^2+‖y‖^2) hp)

theorem radialRoot_norm_sq_le_growing_re (x : (G).domain) :
    ‖Kroot ⟨(x:Hilbert),growing_mem_radialRoot_domain ε hε h hh hb m g k x⟩‖^2 ≤
      (inner ℂ (G x) (x:Hilbert)).re :=
  left_le_of_eq_add (growing_form_energy_eq_split ε hε h hh hb m g k x) (sq_nonneg _)

theorem potentialForm_norm_sq_le_growing_re (x : (G).domain) :
    ‖Tpot ⟨(x:Hilbert),growing_mem_potentialForm_domain ε hε h hh hb m g k x⟩‖^2 ≤
      (inner ℂ (G x) (x:Hilbert)).re :=
  right_le_of_eq_add (growing_form_energy_eq_split ε hε h hh hb m g k x) (sq_nonneg _)

/-! ### Residual Hamiltonian Form Energy -/

theorem residual_mem_residualForm_domain (t : ℝ) (x : (S t).domain) :
    (x:Hilbert) ∈ (Tres t).domain := by
  let w := KFCausalClosedGraphForm.formLift (SD t) x
  have hJ : SJ t w = (x:Hilbert) := KFCausalClosedGraphForm.embedding_formLift (SD t) x
  exact hJ ▸ LinearPMap.mem_domain_of_mem_graph w.property

theorem residual_mem_staticRoot_domain (t : ℝ) (x : (S t).domain) :
    (x:Hilbert) ∈ (Tstat).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
    ε hε h hh hb m g k t (x:Hilbert) (residual_mem_residualForm_domain ε hε h hh hb m g k t x)).1

theorem residual_mem_potentialForm_domain (t : ℝ) (x : (S t).domain) :
    (x:Hilbert) ∈ (Tpot).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
    ε hε h hh hb m g k t (x:Hilbert) (residual_mem_residualForm_domain ε hε h hh hb m g k t x)).2

theorem residual_form_energy_eq_residualOutput (t : ℝ) (x : (S t).domain) :
    (inner ℂ (S t x) (x:Hilbert)).re =
      ‖Tres t ⟨(x:Hilbert),residual_mem_residualForm_domain ε hε h hh hb m g k t x⟩‖^2 := by
  let w := KFCausalClosedGraphForm.formLift (SD t) x
  have hout := form_output_eq_operator (SD t) w (x:Hilbert)
    (KFCausalClosedGraphForm.embedding_formLift (SD t) x)
    (residual_mem_residualForm_domain ε hε h hh hb m g k t x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy (SD t) x).trans
    (congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hout)

theorem residual_form_energy_eq_lifts (t : ℝ) (x : (S t).domain) :
    (inner ℂ (S t x) (x:Hilbert)).re =
      ‖Tstat ⟨(x:Hilbert),residual_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t
          (KFCausalClosedGraphForm.formLift (SD t) x))‖^2 := by
  let w := KFCausalClosedGraphForm.formLift (SD t) x
  have hTJ : TJ (staticLift ε hε h hh hw m g k t w) = (x:Hilbert) :=
    (staticLift_embedding ε hε h hh hw m g k t w).trans
      (KFCausalClosedGraphForm.embedding_formLift (SD t) x)
  have hst := static_form_norm_sq_eq ε hε h hh hb m g k
    (staticLift ε hε h hh hw m g k t w) (x:Hilbert) hTJ
    (residual_mem_staticRoot_domain ε hε h hh hb m g k t x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy (SD t) x).trans
    ((residual_norm_split ε hε h hh hw m g k t w).trans
      (congrArg (fun s : ℝ => s+Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t w)‖^2) hst))

theorem residual_form_energy_eq_split (t : ℝ) (x : (S t).domain) :
    (inner ℂ (S t x) (x:Hilbert)).re =
      ‖Tstat ⟨(x:Hilbert),residual_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖Tpot ⟨(x:Hilbert),residual_mem_potentialForm_domain ε hε h hh hb m g k t x⟩‖^2 := by
  let w := KFCausalClosedGraphForm.formLift (SD t) x
  have hPJ : PJ (potentialLift ε hε h hh hw m g k t w) = (x:Hilbert) :=
    (potentialLift_embedding ε hε h hh hw m g k t w).trans
      (KFCausalClosedGraphForm.embedding_formLift (SD t) x)
  have hp := form_output_eq_operator PD (potentialLift ε hε h hh hw m g k t w) (x:Hilbert) hPJ
    (residual_mem_potentialForm_domain ε hε h hh hb m g k t x)
  exact (residual_form_energy_eq_lifts ε hε h hh hb m g k t x).trans
    (congrArg (fun y : EnergyOutputSpace =>
      ‖Tstat ⟨(x:Hilbert),residual_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖y‖^2) hp)

theorem staticRoot_norm_sq_le_residual_re (t : ℝ) (x : (S t).domain) :
    ‖Tstat ⟨(x:Hilbert),residual_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2 ≤
      (inner ℂ (S t x) (x:Hilbert)).re :=
  left_le_of_eq_add (residual_form_energy_eq_split ε hε h hh hb m g k t x)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

theorem potentialForm_norm_sq_le_residual_re (t : ℝ) (x : (S t).domain) :
    Real.exp (2*t)*‖Tpot ⟨(x:Hilbert),residual_mem_potentialForm_domain ε hε h hh hb m g k t x⟩‖^2 ≤
      (inner ℂ (S t x) (x:Hilbert)).re :=
  right_le_of_eq_add (residual_form_energy_eq_split ε hε h hh hb m g k t x) (sq_nonneg _)

/-! ### Full Time-Dependent Hamiltonian Form Energy -/

def referenceProject (t : ℝ) (x : (H t).domain) : RV :=
  KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t x

def growingProject (t : ℝ) (x : (H t).domain) : GV :=
  KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
    (referenceProject ε hε h hh hb m g k t x)

def residualProject (t : ℝ) (x : (H t).domain) : SV t :=
  KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t
    (referenceProject ε hε h hh hb m g k t x)

theorem referenceProject_embedding (t : ℝ) (x : (H t).domain) :
    RJ (referenceProject ε hε h hh hb m g k t x) = (x:Hilbert) :=
  KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hw m g k t x

theorem growingProject_embedding (t : ℝ) (x : (H t).domain) :
    GJ (growingProject ε hε h hh hb m g k t x) = (x:Hilbert) :=
  (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k
    (referenceProject ε hε h hh hb m g k t x)).trans
    (referenceProject_embedding ε hε h hh hb m g k t x)

theorem residualProject_embedding (t : ℝ) (x : (H t).domain) :
    SJ t (residualProject ε hε h hh hb m g k t x) = (x:Hilbert) :=
  (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t
    (referenceProject ε hε h hh hb m g k t x)).trans
    (referenceProject_embedding ε hε h hh hb m g k t x)

theorem hamiltonian_mem_averaged_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Eavg t).domain := by
  let u := KFCausalClosedGraphForm.formLift (HD t) x
  have hJ : KFCausalClosedGraphForm.embedding (HD t) u = (x:Hilbert) :=
    KFCausalClosedGraphForm.embedding_formLift (HD t) x
  exact hJ ▸ LinearPMap.mem_domain_of_mem_graph u.property

theorem hamiltonian_mem_staticRoot_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Tstat).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k t (x:Hilbert)
    (hamiltonian_mem_averaged_domain ε hε h hh hb m g k t x)).1

theorem hamiltonian_mem_radialRoot_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Kroot).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k t (x:Hilbert)
    (hamiltonian_mem_averaged_domain ε hε h hh hb m g k t x)).2.1

theorem hamiltonian_mem_potentialForm_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Tpot).domain :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k t (x:Hilbert)
    (hamiltonian_mem_averaged_domain ε hε h hh hb m g k t x)).2.2

theorem hamiltonian_mem_growingForm_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Tgrow).domain :=
  ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k t (x:Hilbert)).mp
    (hamiltonian_mem_averaged_domain ε hε h hh hb m g k t x)).1

theorem hamiltonian_mem_residualForm_domain (t : ℝ) (x : (H t).domain) :
    (x:Hilbert) ∈ (Tres t).domain :=
  ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k t (x:Hilbert)).mp
    (hamiltonian_mem_averaged_domain ε hε h hh hb m g k t x)).2

theorem growingProject_output_eq (t : ℝ) (x : (H t).domain) :
    GB (growingProject ε hε h hh hb m g k t x) =
      Tgrow ⟨(x:Hilbert),hamiltonian_mem_growingForm_domain ε hε h hh hb m g k t x⟩ :=
  form_output_eq_operator GD (growingProject ε hε h hh hb m g k t x) (x:Hilbert)
    (growingProject_embedding ε hε h hh hb m g k t x)
    (hamiltonian_mem_growingForm_domain ε hε h hh hb m g k t x)

theorem residualProject_output_eq (t : ℝ) (x : (H t).domain) :
    SB t (residualProject ε hε h hh hb m g k t x) =
      Tres t ⟨(x:Hilbert),hamiltonian_mem_residualForm_domain ε hε h hh hb m g k t x⟩ :=
  form_output_eq_operator (SD t) (residualProject ε hε h hh hb m g k t x) (x:Hilbert)
    (residualProject_embedding ε hε h hh hb m g k t x)
    (hamiltonian_mem_residualForm_domain ε hε h hh hb m g k t x)

theorem potentialLift_residualProject_output_eq (t : ℝ) (x : (H t).domain) :
    PB (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)) =
      Tpot ⟨(x:Hilbert),hamiltonian_mem_potentialForm_domain ε hε h hh hb m g k t x⟩ :=
  form_output_eq_operator PD
    (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)) (x:Hilbert)
    ((potentialLift_embedding ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)).trans
      (residualProject_embedding ε hε h hh hb m g k t x))
    (hamiltonian_mem_potentialForm_domain ε hε h hh hb m g k t x)

theorem growingLift_growingProject_eq_potentialLift (t : ℝ) (x : (H t).domain) :
    growingLift ε hε h hh hw m g k (growingProject ε hε h hh hb m g k t x) =
      potentialLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x) := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (growingLift_embedding ε hε h hh hw m g k (growingProject ε hε h hh hb m g k t x)).trans
    ((growingProject_embedding ε hε h hh hb m g k t x).trans
      ((residualProject_embedding ε hε h hh hb m g k t x).symm.trans
        (potentialLift_embedding ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)).symm))

theorem growingProject_output_norm_sq (t : ℝ) (x : (H t).domain) :
    ‖GB (growingProject ε hε h hh hb m g k t x)‖^2 =
      ‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        ‖PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t x))‖^2 := by
  have hg := growing_output_norm_sq ε hε h hb hh m g k (growingProject ε hε h hh hb m g k t x)
  have hr : ‖R (growingProject ε hε h hh hb m g k t x)‖^2 =
      ‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2 :=
    congrArg (fun z : Hilbert => ‖z‖^2)
      (radial_root_output_eq ε hε h hh hb m g k
        (growingProject ε hε h hh hb m g k t x) (x:Hilbert)
        (growingProject_embedding ε hε h hh hb m g k t x)
        (hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x))
  have hp : ‖PB (growingLift ε hε h hh hw m g k (growingProject ε hε h hh hb m g k t x))‖^2 =
      ‖PB (potentialLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x))‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (congrArg PB (growingLift_growingProject_eq_potentialLift ε hε h hh hb m g k t x))
  exact hg.trans (congrArg₂ (·+·) hr hp)

theorem hamiltonian_form_energy_eq_static_add_growing (t : ℝ) (x : (H t).domain) :
    (inner ℂ (H t x) (x:Hilbert)).re =
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k t x)‖^2 := by
  let u0 := referenceProject ε hε h hh hb m g k t x
  have hp1 : inner ℂ (H t x) (x:Hilbert) =
      inner ℂ u0 (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hw m g k t u0) :=
    (congrArg (inner ℂ (H t x)) (referenceProject_embedding ε hε h hh hb m g k t x).symm).trans
      (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_pairing
        ε hε h hh hw m g k t x u0).symm
  have hp2 := KFCausalBoundedFormCurve.formOperator_pairing
    (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k)
    (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k) t u0 u0
  have hsplit := norm_sq_of_inner_split
    (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k u0)
    (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k u0)
    (inner ℂ (H t x) (x:Hilbert)) (Real.exp (2*t)) (hp1.trans hp2)
  have hTB : TB (staticLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)) =
      KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k u0 :=
    source_static ε hε h hh hw m g k t u0
  have hTJ : TJ (staticLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)) =
      (x:Hilbert) :=
    (staticLift_embedding ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)).trans
      (residualProject_embedding ε hε h hh hb m g k t x)
  have hst : ‖KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k u0‖^2 =
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2 :=
    (congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hTB.symm).trans
      (static_form_norm_sq_eq ε hε h hh hb m g k
        (staticLift ε hε h hh hw m g k t (residualProject ε hε h hh hb m g k t x)) (x:Hilbert) hTJ
        (hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x))
  exact hsplit.trans
    (congrArg (fun s : ℝ => s+Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k t x)‖^2) hst)

theorem hamiltonian_form_energy_eq_three_channel_lifts (t : ℝ) (x : (H t).domain) :
    (inner ℂ (H t x) (x:Hilbert)).re =
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t
          (residualProject ε hε h hh hb m g k t x))‖^2 :=
  (hamiltonian_form_energy_eq_static_add_growing ε hε h hh hb m g k t x).trans
    ((congrArg (fun s : ℝ =>
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*s)
      (growingProject_output_norm_sq ε hε h hh hb m g k t x)).trans
      (add_mul_add_eq _ _ _ _))

theorem hamiltonian_form_energy_eq_three_channel (t : ℝ) (x : (H t).domain) :
    (inner ℂ (H t x) (x:Hilbert)).re =
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖Tpot ⟨(x:Hilbert),hamiltonian_mem_potentialForm_domain ε hε h hh hb m g k t x⟩‖^2 :=
  (hamiltonian_form_energy_eq_three_channel_lifts ε hε h hh hb m g k t x).trans
    (congrArg (fun y : EnergyOutputSpace =>
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖y‖^2)
      (potentialLift_residualProject_output_eq ε hε h hh hb m g k t x))

theorem hamiltonian_form_energy_eq_radial_add_residual (t : ℝ) (x : (H t).domain) :
    (inner ℂ (H t x) (x:Hilbert)).re =
      Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        ‖SB t (residualProject ε hε h hh hb m g k t x)‖^2 := by
  let w := residualProject ε hε h hh hb m g k t x
  have hTJ : TJ (staticLift ε hε h hh hw m g k t w) = (x:Hilbert) :=
    (staticLift_embedding ε hε h hh hw m g k t w).trans
      (residualProject_embedding ε hε h hh hb m g k t x)
  have hst := static_form_norm_sq_eq ε hε h hh hb m g k
    (staticLift ε hε h hh hw m g k t w) (x:Hilbert) hTJ
    (hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x)
  have hres : ‖SB t w‖^2 =
      ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
        Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t w)‖^2 :=
    (residual_norm_split ε hε h hh hw m g k t w).trans
      (congrArg (fun s : ℝ => s+Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t w)‖^2) hst)
  exact three_channel_to_radial_residual _ _ _ _ _
    (hamiltonian_form_energy_eq_three_channel_lifts ε hε h hh hb m g k t x) hres

theorem hamiltonian_growing_add_residual_energy_eq (t : ℝ) (x : (H t).domain) :
    Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k t x)‖^2+
      ‖SB t (residualProject ε hε h hh hb m g k t x)‖^2 =
        (inner ℂ (H t x) (x:Hilbert)).re+
          Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k t
            (residualProject ε hε h hh hb m g k t x))‖^2 :=
  growing_add_residual_from_parts _ _ _ _ _ _
    (hamiltonian_form_energy_eq_radial_add_residual ε hε h hh hb m g k t x)
    (growingProject_output_norm_sq ε hε h hh hb m g k t x)

theorem static_add_radial_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2+
      Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2 ≤
        (inner ℂ (H t x) (x:Hilbert)).re :=
  left_le_of_eq_add (hamiltonian_form_energy_eq_three_channel ε hε h hh hb m g k t x)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

theorem staticRoot_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    ‖Tstat ⟨(x:Hilbert),hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t x⟩‖^2 ≤
      (inner ℂ (H t x) (x:Hilbert)).re :=
  left_le_of_eq_add (hamiltonian_form_energy_eq_static_add_growing ε hε h hh hb m g k t x)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

theorem radialRoot_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    Real.exp (2*t)*‖Kroot ⟨(x:Hilbert),hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t x⟩‖^2 ≤
      (inner ℂ (H t x) (x:Hilbert)).re :=
  left_le_of_eq_add (hamiltonian_form_energy_eq_radial_add_residual ε hε h hh hb m g k t x)
    (sq_nonneg _)

theorem potentialForm_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    Real.exp (2*t)*‖Tpot ⟨(x:Hilbert),hamiltonian_mem_potentialForm_domain ε hε h hh hb m g k t x⟩‖^2 ≤
      (inner ℂ (H t x) (x:Hilbert)).re :=
  right_le_of_eq_add (hamiltonian_form_energy_eq_three_channel ε hε h hh hb m g k t x)
    (add_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _)))

theorem growingForm_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k t x)‖^2 ≤
      (inner ℂ (H t x) (x:Hilbert)).re :=
  right_le_of_eq_add (hamiltonian_form_energy_eq_static_add_growing ε hε h hh hb m g k t x)
    (sq_nonneg _)

theorem residualForm_norm_sq_le_hamiltonian_re (t : ℝ) (x : (H t).domain) :
    ‖SB t (residualProject ε hε h hh hb m g k t x)‖^2 ≤
      (inner ℂ (H t x) (x:Hilbert)).re :=
  right_le_of_eq_add (hamiltonian_form_energy_eq_radial_add_residual ε hε h hh hb m g k t x)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

#print axioms growing_mem_growingForm_domain
#print axioms growing_mem_radialRoot_domain
#print axioms growing_mem_potentialForm_domain
#print axioms growing_form_energy_eq_growingOutput
#print axioms growing_form_energy_eq_lifts
#print axioms growing_form_energy_eq_split
#print axioms radialRoot_norm_sq_le_growing_re
#print axioms potentialForm_norm_sq_le_growing_re
#print axioms residual_mem_residualForm_domain
#print axioms residual_mem_staticRoot_domain
#print axioms residual_mem_potentialForm_domain
#print axioms residual_form_energy_eq_residualOutput
#print axioms residual_form_energy_eq_lifts
#print axioms residual_form_energy_eq_split
#print axioms staticRoot_norm_sq_le_residual_re
#print axioms potentialForm_norm_sq_le_residual_re
#print axioms referenceProject_embedding
#print axioms growingProject_embedding
#print axioms residualProject_embedding
#print axioms hamiltonian_mem_averaged_domain
#print axioms hamiltonian_mem_staticRoot_domain
#print axioms hamiltonian_mem_radialRoot_domain
#print axioms hamiltonian_mem_potentialForm_domain
#print axioms hamiltonian_mem_growingForm_domain
#print axioms hamiltonian_mem_residualForm_domain
#print axioms growingProject_output_eq
#print axioms residualProject_output_eq
#print axioms potentialLift_residualProject_output_eq
#print axioms growingLift_growingProject_eq_potentialLift
#print axioms growingProject_output_norm_sq
#print axioms hamiltonian_form_energy_eq_static_add_growing
#print axioms hamiltonian_form_energy_eq_three_channel_lifts
#print axioms hamiltonian_form_energy_eq_three_channel
#print axioms hamiltonian_form_energy_eq_radial_add_residual
#print axioms hamiltonian_growing_add_residual_energy_eq
#print axioms static_add_radial_norm_sq_le_hamiltonian_re
#print axioms staticRoot_norm_sq_le_hamiltonian_re
#print axioms radialRoot_norm_sq_le_hamiltonian_re
#print axioms potentialForm_norm_sq_le_hamiltonian_re
#print axioms growingForm_norm_sq_le_hamiltonian_re
#print axioms residualForm_norm_sq_le_hamiltonian_re
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalOperatorFormEnergy
