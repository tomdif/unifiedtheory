/- Quantitative stability of the actual interacting energy floor under
the newly constructed component form couplings. This is a bound above the
chosen energy origin, not a vacuum-subtracted excitation gap. -/
import UnifiedTheory.Audit.KFCausalInteractingComponentPerturbation
import UnifiedTheory.Audit.KFCausalInteractingEnergyFloor

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingComponentEnergyFloor
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)

private theorem form_floor_of_operator_floor {X K : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : KFCausalClosedGraphForm.Data X K) (δ : ℝ)
    (hf : ∀ f : (KFCausalClosedGraphForm.hamiltonian D).domain,
      δ*‖(f:X)‖^2 ≤ (inner ℂ (KFCausalClosedGraphForm.hamiltonian D f) (f:X)).re)
    (u : KFCausalClosedGraphForm.FormSpace D) :
    δ*‖KFCausalClosedGraphForm.embedding D u‖^2 ≤
      ‖KFCausalClosedGraphForm.energyOutput D u‖^2 := by
  have hd : DenseRange (KFCausalClosedGraphForm.formLift D) :=
    KFCausalFormHamiltonian.operator_domain_form_dense _
      (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)
  refine hd.induction_on u ?_ ?_
  · exact isClosed_le
      (continuous_const.mul ((KFCausalClosedGraphForm.embedding D).continuous.norm.pow 2))
      ((KFCausalClosedGraphForm.energyOutput D).continuous.norm.pow 2)
  · intro f
    rw [KFCausalClosedGraphForm.embedding_formLift,
      ← KFCausalClosedGraphForm.hamiltonian_energy D f]
    exact hf f

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m q k : ℝ) (hk : 0 < k) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hpos.ne' hw m q k t
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "E" => KFCausalClosedGraphForm.energyOutput D
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m q k t
local notation "A" => KFCausalInteractingComponentPerturbation.component ε hε h hpos.ne' hw m q k t
local notation "Hg" => KFCausalInteractingComponentPerturbation.hamiltonian ε hε h hpos.ne' hw m q k t

include hk in
theorem original_form_lower (u : KFCausalClosedGraphForm.FormSpace D) :
    (ε/2)*‖J u‖^2 ≤ ‖E u‖^2 := by
  apply form_floor_of_operator_floor D (ε/2) _ u
  intro f
  exact KFCausalInteractingEnergyFloor.graph_energy_lower ε hε h hpos hb m q k hk t f (H f)
    ((H).mem_graph f)

include hk in
theorem perturbed_energy_lower (i : Fin 8) (g : ℝ)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert)
    (huy : (J u,y) ∈ (Hg i g).graph) :
    (ε/4-2*g^2)*‖J u‖^2 ≤ (inner ℂ y (J u)).re := by
  have hf : ∀ v : KFCausalClosedGraphForm.FormSpace D,
      (ε/2)*‖J v‖^2 ≤ ‖v‖^2-‖J v‖^2 := by
    intro v
    have he := KFCausalClosedGraphForm.form_norm_identity D v
    have hl := original_form_lower ε hε h hpos hb m q k hk t v
    linarith
  have he := KFCausalLinearFieldFormPerturbation.lower_bound_with_floor J (A i) g
    (KFCausalInteractingComponentPerturbation.component_bound ε hε h hpos.ne' hw m q k t i)
    (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)
    (ε/2) hf u y huy
  convert he using 1 <;> ring

theorem small_coupling_floor_positive (g : ℝ) (hg : g^2 < ε/8) : 0 < ε/4-2*g^2 := by
  linarith

include hk in
theorem full_domain_energy_lower (i : Fin 8) (g : ℝ) (f : (Hg i g).domain) :
    (ε/4-2*g^2)*‖(f : Hilbert)‖^2 ≤ (inner ℂ (Hg i g f) (f : Hilbert)).re := by
  obtain ⟨u,hu⟩ := KFCausalLinearFieldFormPerturbation.domain_in_form_range J (A i) g
    (KFCausalInteractingComponentPerturbation.component_bound ε hε h hpos.ne' hw m q k t i)
    (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D) f
  have hg : (J u,Hg i g f) ∈ (Hg i g).graph := by rw [hu]; exact (Hg i g).mem_graph f
  simpa only [hu] using perturbed_energy_lower ε hε h hpos hb m q k hk t i g u _ hg

end
end UnifiedTheory.Audit.KFCausalInteractingComponentEnergyFloor
