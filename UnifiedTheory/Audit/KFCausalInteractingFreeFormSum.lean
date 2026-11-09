/- The actual interacting Hamiltonian is the form sum of the actual free
Hamiltonian and the time-weighted closed potential, on its entire graph.
No separate potential-operator domain assumption is used. -/
import UnifiedTheory.Audit.KFCausalCircularInteractingBridge
import UnifiedTheory.Audit.KFCausalClockFloorFreeHamiltonianFormSum
import UnifiedTheory.Audit.KFCausalThreeChannelPolarization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInteractingFreeFormSum
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

private def graphLift {X Y V : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [AddCommGroup V] [Module ℂ V]
    (D : KFCausalClosedGraphForm.Data X Y) (J : V →ₗ[ℂ] X)
    (hd : ∀ u, J u ∈ D.operator.domain) : V →ₗ[ℂ] KFCausalClosedGraphForm.FormSpace D where
  toFun u := KFCausalClosedGraphForm.graphVector D ⟨J u,hd u⟩
  map_add' u v := KFCausalClosedGraphForm.embedding_injective D (J.map_add u v)
  map_smul' c u := KFCausalClosedGraphForm.embedding_injective D (J.map_smul c u)

private theorem form_output_eq {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (D : KFCausalClosedGraphForm.Data X Y) (u : KFCausalClosedGraphForm.FormSpace D)
    (f : X) (y : Y) (hu : KFCausalClosedGraphForm.embedding D u = f)
    (hy : (f,y) ∈ D.operator.graph) : KFCausalClosedGraphForm.energyOutput D u = y :=
  D.operator.mem_graph_snd_inj' u.property hy hu

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ) (hk : 0 < k)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hpos.ne' hw m g k
local notation "V" => FormSpace ε hε h hpos.ne' hw m g k 0
local notation "J" => embedding ε hε h hpos.ne' hw m g k 0
local notation "A" => energyOutput ε hε h hpos.ne' hw m g k 0
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hpos.ne' hw m g k
local notation "S" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "R" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "P" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hpos.ne' hw m g k

def FormDomain : Submodule ℂ Hilbert := KFCausalClockFloorFreeHamiltonianFormSum.FormDomain ε hε h ⊓ (P).domain

def freeView : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] KFCausalClockFloorFreeHamiltonianFormSum.FormDomain ε hε h :=
  (FormDomain ε hε h hpos hb m g k).subtype.codRestrict _ (fun u => u.property.1)

include hk in
theorem form_domain_iff (f : Hilbert) :
    f ∈ (D 0).operator.domain ↔ f ∈ FormDomain ε hε h hpos hb m g k := by
  change f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
    (hamiltonian_bound ε h hw) hpos.ne' m g k 0).domain ↔ _
  rw [KFCausalCircularInteractingBridge.form_domain_iff ε hε h hpos hb m g k hk 0 f,
    KFCausalClockFloorFreeFormSum.free_form_domain ε hε h hpos.ne' 0 hb f]
  rfl

def toReference : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] V :=
  graphLift (D 0) (FormDomain ε hε h hpos hb m g k).subtype
    (fun u => (form_domain_iff ε hε h hpos hb m g k hk u.val).mpr u.property)

theorem toReference_embedding (u : FormDomain ε hε h hpos hb m g k) :
    J (toReference ε hε h hpos hb m g k hk u) = u.val := rfl

theorem toReference_surjective : Function.Surjective (toReference ε hε h hpos hb m g k hk) := by
  intro u
  refine ⟨⟨J u,(form_domain_iff ε hε h hpos hb m g k hk (J u)).mp
    (LinearPMap.mem_domain_of_mem_graph u.property)⟩,?_⟩
  exact embedding_injective ε hε h hpos.ne' hw m g k 0 rfl

def staticRoot : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] Hilbert :=
  (S).toFun.comp ((FormDomain ε hε h hpos hb m g k).subtype.codRestrict _
    (fun u => u.property.1.2))

def radialRoot : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] Hilbert :=
  (R).toFun.comp ((FormDomain ε hε h hpos hb m g k).subtype.codRestrict _
    (fun u => u.property.1.1))

def potentialRoot : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] EnergyOutputSpace :=
  (P).toFun.comp ((FormDomain ε hε h hpos hb m g k).subtype.codRestrict _
    (fun u => u.property.2))

private theorem static_norm (u : V) (z : Hilbert) (hz : (J u,z) ∈ (S).graph) :
    ‖staticOutputLp (A u)‖ = ‖z‖ := by
  obtain ⟨v,hv⟩ := KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective
    ε hε h hpos.ne' hw m g k 0 u
  let w := KFCausalClockFloorStaticRootSource.source ε hε h hpos.ne' hw m g k 0 v
  have he : KFCausalClosedGraphForm.energyOutput
      (KFCausalClockFloorStaticRootSource.rootData ε hε h) w = z :=
    (S).mem_graph_snd_inj' w.property hz
      ((KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
        ε hε h hpos.ne' hw m g k 0 v).symm.trans (congrArg J hv))
  have hn := KFCausalClockFloorStaticRootSource.source_output_norm ε hε h hpos.ne' hw m g k 0 v
  have hA := (congrArg A hv).symm.trans
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output ε hε h hpos.ne' hw m g k 0 v)
  exact (congrArg (fun x => ‖staticOutputLp x‖) hA).trans (hn.symm.trans (congrArg norm he))

private theorem growing_norm_reference (v : V) (r : Hilbert) (p : EnergyOutputSpace)
    (hR : (J v,r) ∈ (R).graph) (hP : (J v,p) ∈ (P).graph) :
    ‖growingOutputLp (A v)‖^2 = ‖r‖^2+‖p‖^2 := by
  let w := KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hpos.ne' hw m g k v
  have hn := KFCausalClockFloorRadialResolventGrowing.growing_output_norm_sq
    ε hε h hb hpos.ne' m g k w
  have hr : KFCausalClockFloorResidualFormReconstruction.referenceRoot
      ε hε h hpos.ne' hb m g k v = r :=
    (R).mem_graph_snd_inj'
      (KFCausalClockFloorResidualFormReconstruction.referenceRoot_graph
        ε hε h hpos.ne' hb m g k v) hR rfl
  have hp : KFCausalClosedGraphForm.energyOutput PD
      (KFCausalClockFloorPotentialHamiltonian.growingLift ε hε h hpos.ne' hw m g k w) = p :=
    form_output_eq PD
      (KFCausalClockFloorPotentialHamiltonian.growingLift ε hε h hpos.ne' hw m g k w)
      (J v) p (KFCausalClockFloorPotentialHamiltonian.growingLift_embedding
        ε hε h hpos.ne' hw m g k w) hP
  have ho : KFCausalClosedGraphForm.energyOutput
      (KFCausalClockFloorGrowingHamiltonian.formData ε hε h hpos.ne' hw m g k) w =
      growingOutputLp (A v) :=
    KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hpos.ne' hw m g k v
  exact (congrArg (fun x => ‖x‖^2) ho).symm.trans
    (hn.trans (congrArg₂ (·+·) (congrArg (fun x => ‖x‖^2) hr)
      (congrArg (fun x => ‖x‖^2) hp)))

private theorem growing_norm (u : FormDomain ε hε h hpos hb m g k) :
    ‖growingOutputLp (A (toReference ε hε h hpos hb m g k hk u))‖^2 =
      ‖radialRoot ε hε h hpos hb m g k u‖^2+‖potentialRoot ε hε h hpos hb m g k u‖^2 :=
  growing_norm_reference ε hε h hpos hb m g k
    (toReference ε hε h hpos hb m g k hk u) _ _
    ((R).mem_graph ⟨u.val,u.property.1.1⟩) ((P).mem_graph ⟨u.val,u.property.2⟩)

def output (t : ℝ) : FormDomain ε hε h hpos hb m g k →ₗ[ℂ] EnergyOutputSpace :=
  (energyOutput ε hε h hpos.ne' hw m g k t).toLinearMap.comp
    ((formTransfer ε hε h hpos.ne' hw m g k 0 t).toLinearMap.comp
      (toReference ε hε h hpos hb m g k hk))

theorem output_norm (t : ℝ) (u : FormDomain ε hε h hpos hb m g k) :
    ‖output ε hε h hpos hb m g k hk t u‖^2 =
      ‖staticRoot ε hε h hpos hb m g k u‖^2+
      Real.exp (2*t)*(‖radialRoot ε hε h hpos hb m g k u‖^2+
        ‖potentialRoot ε hε h hpos hb m g k u‖^2) := by
  let v := toReference ε hε h hpos hb m g k hk u
  have ht : output ε hε h hpos hb m g k hk t u =
      KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t (A v) :=
    transfer_energyOutput ε hε h hpos.ne' hw m g k 0 t v
  have hs := static_norm ε hε h hpos hb m g k v
    (staticRoot ε hε h hpos hb m g k u) ((S).mem_graph ⟨u.val,u.property.1.2⟩)
  have hn : ‖KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t (A v)‖^2 =
      ‖staticOutputLp (A v)‖^2+Real.exp (2*t)*‖growingOutputLp (A v)‖^2 := by
    simpa only [sub_zero] using KFCausalAveragedOutputRescaling.norm_timeOutputLp_sq 0 t (A v)
  exact (congrArg (fun x => ‖x‖^2) ht).trans (hn.trans
    (congrArg₂ (fun x y : ℝ => x+Real.exp (2*t)*y) (congrArg (fun x : ℝ => x^2) hs)
      (growing_norm ε hε h hpos hb m g k hk u)))

/-- The free term is exactly the previously identified physical free form. -/
def pairing (t : ℝ) (u v : FormDomain ε hε h hpos hb m g k) : ℂ :=
  KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t
    (freeView ε hε h hpos hb m g k u) (freeView ε hε h hpos hb m g k v)+
    (Real.exp (2*t):ℂ)*inner ℂ (potentialRoot ε hε h hpos hb m g k u)
      (potentialRoot ε hε h hpos hb m g k v)

theorem output_inner (t : ℝ) (u v : FormDomain ε hε h hpos hb m g k) :
    inner ℂ (output ε hε h hpos hb m g k hk t u) (output ε hε h hpos hb m g k hk t v) =
      pairing ε hε h hpos hb m g k t u v := by
  have he : (Real.exp t)^2 = Real.exp (2*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
  have hp := KFCausalThreeChannelPolarization.inner_split
    (output ε hε h hpos hb m g k hk t) (staticRoot ε hε h hpos hb m g k)
    (radialRoot ε hε h hpos hb m g k) (potentialRoot ε hε h hpos hb m g k)
    (Real.exp t) (fun x => by rw [he]; exact output_norm ε hε h hpos hb m g k hk t x) u v
  have hec : ((Real.exp t:ℂ))^2 = (Real.exp (2*t):ℂ) := by
    rw [← Complex.ofReal_pow,he]
  rw [hec] at hp
  rw [hp]
  change _ = inner ℂ (staticRoot ε hε h hpos hb m g k u) (staticRoot ε hε h hpos hb m g k v)+
    (Real.exp (2*t):ℂ)*inner ℂ (radialRoot ε hε h hpos hb m g k u)
      (radialRoot ε hε h hpos hb m g k v)+
    (Real.exp (2*t):ℂ)*inner ℂ (potentialRoot ε hε h hpos hb m g k u)
      (potentialRoot ε hε h hpos hb m g k v)
  ring

include hk in
/-- Entire actual operator graph. Only form-domain conditions occur on the right. -/
theorem hamiltonian_graph_iff (t : ℝ) (f g' : Hilbert) :
    (f,g') ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian
      ε hε h hpos.ne' hw m g k t).graph ↔
      ∃ u : FormDomain ε hε h hpos hb m g k, u.val = f ∧
        ∀ v : FormDomain ε hε h hpos hb m g k,
          pairing ε hε h hpos hb m g k t u v = inner ℂ g' v.val := by
  let L : FormDomain ε hε h hpos hb m g k → FormSpace ε hε h hpos.ne' hw m g k t :=
    fun u => formTransfer ε hε h hpos.ne' hw m g k 0 t
      (toReference ε hε h hpos hb m g k hk u)
  have hsur : Function.Surjective L := by
    intro w
    obtain ⟨u,hu⟩ := toReference_surjective ε hε h hpos hb m g k hk
      (formTransfer ε hε h hpos.ne' hw m g k t 0 w)
    refine ⟨u,?_⟩
    change formTransfer ε hε h hpos.ne' hw m g k 0 t
      (toReference ε hε h hpos hb m g k hk u) = w
    exact (congrArg (formTransfer ε hε h hpos.ne' hw m g k 0 t) hu).trans
      (transfer_inverse ε hε h hpos.ne' hw m g k t 0 w)
  exact KFCausalClosedFormUnitaryGraph.graph_iff (D t) (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun u : FormDomain ε hε h hpos hb m g k => u.val) L hsur
    (fun u => transfer_embedding ε hε h hpos.ne' hw m g k 0 t
      (toReference ε hε h hpos hb m g k hk u))
    (pairing ε hε h hpos hb m g k t) (output_inner ε hε h hpos hb m g k hk t) f g'

include hk in
theorem hamiltonian_domain_iff (t : ℝ) (f : Hilbert) :
    f ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian
      ε hε h hpos.ne' hw m g k t).domain ↔
      ∃ u : FormDomain ε hε h hpos hb m g k, u.val = f ∧
        ∃ y : Hilbert, ∀ v : FormDomain ε hε h hpos hb m g k,
          pairing ε hε h hpos hb m g k t u v = inner ℂ y v.val := by
  constructor
  · intro hf
    obtain ⟨u,hu,hp⟩ := (hamiltonian_graph_iff ε hε h hpos hb m g k hk t f _).mp
      ((KFCausalClockFloorAveragedHamiltonian.hamiltonian
        ε hε h hpos.ne' hw m g k t).mem_graph ⟨f,hf⟩)
    exact ⟨u,hu,_,hp⟩
  · rintro ⟨u,hu,y,hp⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((hamiltonian_graph_iff ε hε h hpos hb m g k hk t f y).mpr ⟨u,hu,hp⟩)

theorem energy_split (t : ℝ) (u : FormDomain ε hε h hpos hb m g k) :
    (pairing ε hε h hpos hb m g k t u u).re =
      (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t
        (freeView ε hε h hpos hb m g k u) (freeView ε hε h hpos hb m g k u)).re+
      Real.exp (2*t)*‖potentialRoot ε hε h hpos hb m g k u‖^2 := by
  simp only [pairing,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  exact congrArg (fun r : ℝ =>
    (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t
      (freeView ε hε h hpos hb m g k u) (freeView ε hε h hpos hb m g k u)).re+
      Real.exp (2*t)*r) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

theorem free_energy_le (t : ℝ) (u : FormDomain ε hε h hpos hb m g k) :
    (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t
      (freeView ε hε h hpos hb m g k u) (freeView ε hε h hpos hb m g k u)).re ≤
      (pairing ε hε h hpos hb m g k t u u).re := by
  rw [energy_split]
  exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

include hk in
/-- Full interacting graph in the same circular Hilbert coordinates as the free spectrum.
The potential occurs through its completed energy form, not an assumed `P f` output. -/
theorem circular_graph_iff (t : ℝ)
    (F G : KFCausalJointHermiteFourierTransform.Coefficients) :
    ((KFCausalFreeCircularSpectral.transform h hpos t).symm F,
      (KFCausalFreeCircularSpectral.transform h hpos t).symm G) ∈
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t).graph ↔
      ∃ u : FormDomain ε hε h hpos hb m g k,
        KFCausalFreeCircularSpectral.transform h hpos t u.val = F ∧
        ∀ v : FormDomain ε hε h hpos hb m g k,
          pairing ε hε h hpos hb m g k t u v =
            inner ℂ G (KFCausalFreeCircularSpectral.transform h hpos t v.val) := by
  let W := KFCausalFreeCircularSpectral.transform h hpos t
  rw [hamiltonian_graph_iff ε hε h hpos hb m g k hk t]
  constructor
  · rintro ⟨u,hu,hp⟩
    refine ⟨u,(congrArg W hu).trans (W.apply_symm_apply F),?_⟩
    intro v
    exact (hp v).trans ((W.inner_map_map (W.symm G) v.val).symm.trans
      (congrArg (fun z => inner ℂ z (W v.val)) (W.apply_symm_apply G)))
  · rintro ⟨u,hu,hp⟩
    refine ⟨u,(W.symm_apply_apply u.val).symm.trans (congrArg W.symm hu),?_⟩
    intro v
    exact (hp v).trans
      ((congrArg (fun z => inner ℂ z (W v.val)) (W.apply_symm_apply G).symm).trans
        (W.inner_map_map (W.symm G) v.val))

include hk in
/-- Actual interacting energy equals free-form energy plus a nonnegative potential energy,
even without separate free/potential operator-domain membership. -/
theorem hamiltonian_energy_split (t : ℝ) (f y : Hilbert)
    (hy : (f,y) ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian
      ε hε h hpos.ne' hw m g k t).graph) :
    ∃ u : FormDomain ε hε h hpos hb m g k, u.val = f ∧
      (inner ℂ y f).re =
        (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t
          (freeView ε hε h hpos hb m g k u) (freeView ε hε h hpos hb m g k u)).re+
          Real.exp (2*t)*‖potentialRoot ε hε h hpos hb m g k u‖^2 := by
  obtain ⟨u,hu,hp⟩ := (hamiltonian_graph_iff ε hε h hpos hb m g k hk t f y).mp hy
  refine ⟨u,hu,?_⟩
  have he := congrArg Complex.re (hp u)
  rw [hu] at he
  exact he.symm.trans (energy_split ε hε h hpos hb m g k t u)

#print axioms form_domain_iff
#print axioms toReference_surjective
#print axioms output_norm
#print axioms output_inner
#print axioms hamiltonian_graph_iff
#print axioms hamiltonian_domain_iff
#print axioms energy_split
#print axioms free_energy_le
#print axioms circular_graph_iff
#print axioms hamiltonian_energy_split
end
end UnifiedTheory.Audit.KFCausalInteractingFreeFormSum
