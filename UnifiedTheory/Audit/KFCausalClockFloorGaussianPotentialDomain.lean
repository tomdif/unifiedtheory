/- Clock Gaussian regularization on the entire completed potential
Hamiltonian domain. Because the potential form has no radial kinetic rows,
the half-shift Gaussian adjoint identity is exact with zero defect, and
regularized vectors converge in the graph of P as the Gaussian width tends
to zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialForm
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialDomain
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGaussianGrowingTransport (action action_pairing)
open KFCausalClockFloorGaussianPotentialForm (formAction formAction_embedding form_pairing)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)
open KFCausalClosedGraphForm
  (formLift embedding_formLift hamiltonian_represents_form hamiltonian_domain_characterization)

private theorem form_graph (D : KFCausalClosedGraphForm.Data Hilbert
    KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert)
    (hp : ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
      (KFCausalClosedGraphForm.energyOutput D v)=
        inner ℂ y (KFCausalClosedGraphForm.embedding D v)) :
    (KFCausalClosedGraphForm.embedding D u,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph := by
  obtain ⟨hu,he⟩ := (hamiltonian_domain_characterization D u y).mpr hp
  have hg := (KFCausalClosedGraphForm.hamiltonian D).mem_graph
    ⟨KFCausalClosedGraphForm.embedding D u,hu⟩
  rwa [he] at hg

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "D" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "V" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hb m g k
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "B" => KFCausalClosedGraphForm.energyOutput D
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k

theorem gaussian_graph (a : ℝ) (ha : 0 ≤ a) (x : (P).domain) :
    (action ε a ha 0 (x:Hilbert),action ε a ha (-h) (P x)) ∈ (P).graph := by
  let u := formLift D x
  let v := formAction ε hε a ha h hh hb 0 m g k u
  have hp (z : V) : inner ℂ (B v) (B z)=
      inner ℂ (action ε a ha (-h) (P x)) (J z) := by
    have he := form_pairing ε hε a ha h hh hb m g k u z
    have hr := hamiltonian_represents_form D x
      (formAction ε hε a ha h hh hb h m g k z)
    have hs : inner ℂ (P x) (action ε a ha h (J z))=
        inner ℂ (action ε a ha (-h) (P x)) (J z) := by
      simpa only [neg_neg] using (action_pairing ε a ha (-h) (P x) (J z)).symm
    exact he.trans (hr.trans ((congrArg (fun w : Hilbert => inner ℂ (P x) w)
      (formAction_embedding ε hε a ha h hh hb h m g k z)).trans hs))
  have hg := form_graph D v (action ε a ha (-h) (P x)) hp
  have hj : J v=action ε a ha 0 (x:Hilbert) :=
    (formAction_embedding ε hε a ha h hh hb 0 m g k u).trans
      (congrArg (action ε a ha 0) (embedding_formLift D x))
  exact (congrArg (fun w : Hilbert => (w,action ε a ha (-h) (P x)) ∈ (P).graph) hj).mp hg

theorem gaussian_graph_of_mem (a : ℝ) (ha : 0 ≤ a) (f z : Hilbert)
    (hfz : (f,z) ∈ (P).graph) :
    (action ε a ha 0 f,action ε a ha (-h) z) ∈ (P).graph := by
  let x : (P).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hfz⟩
  have hx : P x=z := (P).mem_graph_snd_inj' ((P).mem_graph x) hfz rfl
  exact (congrArg (fun w : Hilbert => (action ε a ha 0 f,action ε a ha (-h) w) ∈ (P).graph) hx).mp
    (gaussian_graph ε hε h hh hb m g k a ha x)

theorem gaussian_domain (a : ℝ) (ha : 0 ≤ a) (x : (P).domain) :
    action ε a ha 0 (x:Hilbert) ∈ (P).domain :=
  LinearPMap.mem_domain_of_mem_graph (gaussian_graph ε hε h hh hb m g k a ha x)

theorem output_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0)) (x : (P).domain) :
    Tendsto (fun i => action ε (a i) (ha i) (-h) (P x)) l (𝓝 (P x)) :=
  action_tendsto ε (-h) a ha hz (P x)

theorem graph_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0)) (x : (P).domain) :
    Tendsto (fun i => (action ε (a i) (ha i) 0 (x:Hilbert),
      action ε (a i) (ha i) (-h) (P x))) l (𝓝 ((x:Hilbert),P x)) :=
  (action_tendsto ε 0 a ha hz (x:Hilbert)).prodMk_nhds
    (output_tendsto ε hε h hh hb m g k a ha hz x)

theorem sequence_graph_tendsto (x : (P).domain) :
    (∀ n : ℕ,
      (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 (x:Hilbert),
        action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) (P x)) ∈ (P).graph) ∧
    Tendsto (fun n : ℕ => (action ε (((n:ℝ)+1)⁻¹) (by positivity) 0 (x:Hilbert),
      action ε (((n:ℝ)+1)⁻¹) (by positivity) (-h) (P x))) atTop
        (𝓝 ((x:Hilbert),P x)) := by
  refine ⟨fun n => gaussian_graph ε hε h hh hb m g k _ (by positivity) x,?_⟩
  apply graph_tendsto ε hε h hh hb m g k _ _ _ x
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

#print axioms gaussian_graph
#print axioms gaussian_graph_of_mem
#print axioms gaussian_domain
#print axioms output_tendsto
#print axioms graph_tendsto
#print axioms sequence_graph_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianPotentialDomain
