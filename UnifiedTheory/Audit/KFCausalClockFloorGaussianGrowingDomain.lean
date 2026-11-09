/- Clock Gaussian regularization on the ENTIRE actual growing Hamiltonian
domain. Original-form transport and the exact half-shift adjoint identity
give the operator value; proved radial domination supplies its correction.
The resulting graph approximation assumes no separate potential domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingOutputPairing
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingRadialPairing
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingDomain
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGaussianGrowingTransport (action action_pairing)
open KFCausalClockFloorGaussianGrowingForm (formAction formAction_embedding)
open KFCausalClockFloorGaussianGrowingOutputPairing (form_pairing)
open KFCausalClockFloorGaussianGrowingRadialPairing (radialOutput gaussian_form_pairing)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)
open KFCausalClosedGraphForm
  (formLift embedding_formLift hamiltonian_represents_form hamiltonian_domain_characterization)

private theorem pairing_cancel (A b c d B C E : ℂ)
    (he : A+b=c+d) (hb : b=B) (hc : c=C) (hd : d=E) : A=C+E-B := by
  rw [hb,hc,hd] at he
  exact eq_sub_of_add_eq he

private theorem inner_combination (p q r z : Hilbert) :
    inner ℂ (p+q-r) z=inner ℂ p z+inner ℂ q z-inner ℂ r z := by
  rw [inner_sub_left,inner_add_left]

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
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "V" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "B" => KFCausalClosedGraphForm.energyOutput D
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "K" => radialOutput ε hε h hh hb m g k

def output (a : ℝ) (ha : 0 ≤ a) (x : (G).domain) : Hilbert :=
  action ε a ha (-h) (G x)+action ε a ha 0 (K x)-action ε a ha (-h) (K x)

theorem gaussian_graph (a : ℝ) (ha : 0 ≤ a) (x : (G).domain) :
    (action ε a ha 0 (x:Hilbert),output ε hε h hh hb m g k a ha x) ∈ (G).graph := by
  let u := formLift D x
  let v := formAction ε hε a ha h hh hw 0 m g k u
  have hp (z : V) : inner ℂ (B v) (B z)=
      inner ℂ (output ε hε h hh hb m g k a ha x) (J z) := by
    have he := form_pairing ε a ha h hε hh hw m g k u z
    have hp := hamiltonian_represents_form D x
      (formAction ε hε a ha h hh hw h m g k z)
    have ph := gaussian_form_pairing ε hε h hh hb m g k a ha h x z
    have p0 := gaussian_form_pairing ε hε h hh hb m g k a ha 0 x z
    have hs : inner ℂ (G x) (action ε a ha h (J z))=
        inner ℂ (action ε a ha (-h) (G x)) (J z) := by
      simpa only [neg_neg] using (action_pairing ε a ha (-h) (G x) (J z)).symm
    have hc : inner ℂ (B u) (B (formAction ε hε a ha h hh hw h m g k z))=
        inner ℂ (action ε a ha (-h) (G x)) (J z) :=
      hp.trans ((congrArg (fun w : Hilbert => inner ℂ (G x) w)
        (formAction_embedding ε hε a ha h hh hw h m g k z)).trans hs)
    simp only [neg_zero] at p0
    have he' := pairing_cancel _ _ _ _ _ _ _ he ph hc p0
    exact he'.trans (inner_combination (action ε a ha (-h) (G x))
      (action ε a ha 0 (K x)) (action ε a ha (-h) (K x)) (J z)).symm
  have hg := form_graph D v (output ε hε h hh hb m g k a ha x) hp
  have hj : J v=action ε a ha 0 (x:Hilbert) :=
    (formAction_embedding ε hε a ha h hh hw 0 m g k u).trans
      (congrArg (action ε a ha 0) (embedding_formLift D x))
  exact (congrArg (fun w : Hilbert => (w,output ε hε h hh hb m g k a ha x) ∈ (G).graph) hj).mp hg

theorem gaussian_domain (a : ℝ) (ha : 0 ≤ a) (x : (G).domain) :
    action ε a ha 0 (x:Hilbert) ∈ (G).domain :=
  LinearPMap.mem_domain_of_mem_graph (gaussian_graph ε hε h hh hb m g k a ha x)

theorem output_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0)) (x : (G).domain) :
    Tendsto (fun i => output ε hε h hh hb m g k (a i) (ha i) x) l (𝓝 (G x)) := by
  have ht := ((action_tendsto ε (-h) a ha hz (G x)).add
    (action_tendsto ε 0 a ha hz (K x))).sub (action_tendsto ε (-h) a ha hz (K x))
  simpa only [output,add_sub_cancel_right] using ht

theorem graph_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0)) (x : (G).domain) :
    Tendsto (fun i => (action ε (a i) (ha i) 0 (x:Hilbert),
      output ε hε h hh hb m g k (a i) (ha i) x)) l (𝓝 ((x:Hilbert),G x)) :=
  (action_tendsto ε 0 a ha hz (x:Hilbert)).prodMk_nhds
    (output_tendsto ε hε h hh hb m g k a ha hz x)

#print axioms gaussian_graph
#print axioms gaussian_domain
#print axioms output_tendsto
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingDomain
