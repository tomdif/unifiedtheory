/- The existing averaged Hamiltonians agree affinely on their common
intersection with the growing operator domain. This neither proves graph-core
density of that intersection nor preservation by the nonautonomous flow. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingDerivativeDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingCommonDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalBoundedFormCurve (gram formOperator)

private theorem affine_pairing
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (A B : X →L[ℂ] Z) (s t : ℝ) (u : X) (y z : Y)
    (hs : ∀ v, inner ℂ u (formOperator A B s v)=inner ℂ y (J v))
    (hg : ∀ v, inner ℂ (B u) (B v)=inner ℂ z (J v)) (v : X) :
    inner ℂ u (formOperator A B t v)=
      inner ℂ (y+(Real.exp (2*t)-Real.exp (2*s)) • z) (J v) := by
  have he : formOperator A B t v=formOperator A B s v+
      (Real.exp (2*t)-Real.exp (2*s)) • gram B v := by
    simp only [formOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      sub_smul]
    abel
  rw [he,inner_add_right,inner_smul_right_eq_smul,hs v]
  change inner ℂ y (J v)+(Real.exp (2*t)-Real.exp (2*s)) •
    inner ℂ u (B.adjoint (B v))=_
  rw [B.adjoint_inner_right,hg v,inner_add_left,inner_smul_left_eq_smul]

private theorem domain_intersection_eq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : ℝ → X →ₗ.[ℂ] X) (G : X →ₗ.[ℂ] X) (d : ℝ → ℝ → ℝ)
    (hgraph : ∀ s t x y z, (x,y) ∈ (T s).graph → (x,z) ∈ G.graph →
      (x,y+d s t • z) ∈ (T t).graph) (s t : ℝ) :
    (T s).domain ⊓ G.domain=(T t).domain ⊓ G.domain := by
  ext x
  constructor
  · rintro ⟨hx,hg⟩
    exact ⟨LinearPMap.mem_domain_of_mem_graph
      (hgraph s t x (T s ⟨x,hx⟩) (G ⟨x,hg⟩)
        ((T s).mem_graph ⟨x,hx⟩) (G.mem_graph ⟨x,hg⟩)),hg⟩
  · rintro ⟨hx,hg⟩
    exact ⟨LinearPMap.mem_domain_of_mem_graph
      (hgraph t s x (T t ⟨x,hx⟩) (G ⟨x,hg⟩)
        ((T t).mem_graph ⟨x,hx⟩) (G.mem_graph ⟨x,hg⟩)),hg⟩

private theorem affine_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (s t : ℝ) (y z : X) :
    HasDerivAt (fun r => y+(Real.exp (2*r)-Real.exp (2*s)) • z)
      ((2*Real.exp (2*t)) • z) t := by
  have he := (Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hd : HasDerivAt (fun r => Real.exp (2*r)-Real.exp (2*s))
      (2*Real.exp (2*t)) t := by
    convert he.sub_const (Real.exp (2*s)) using 1
    ring
  exact (hd.smul_const z).const_add y

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum 0
local notation "A" => staticMap ε hε h hh hb mass2 quartic vacuum
local notation "B" => growingMap ε hε h hh hb mass2 quartic vacuum
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb mass2 quartic vacuum

theorem affine_graph (s t : ℝ) (x y z : Hilbert)
    (hs : (x,y) ∈ (H s).graph) (hg : (x,z) ∈ (G).graph) :
    (x,y+(Real.exp (2*t)-Real.exp (2*s)) • z) ∈ (H t).graph := by
  let u : V := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift
    ε hε h hh hb mass2 quartic vacuum s
    ⟨x,LinearPMap.mem_domain_of_mem_graph hs⟩
  have hj : J u=x :=
    KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift
      ε hε h hh hb mass2 quartic vacuum s _
  have hs' : (J u,y) ∈ (H s).graph := by simpa only [hj] using hs
  have hg' : (J u,z) ∈ (G).graph := by simpa only [hj] using hg
  have hp := (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain
    ε hε h hh hb mass2 quartic vacuum s u y).mp
      ((KFCausalMassFormOperator.graph_domain_iff (H s) (J u) y).mp hs')
  have hz := (KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization
    ε hε h hh hb mass2 quartic vacuum u z).mp
      ((KFCausalMassFormOperator.graph_domain_iff G (J u) z).mp hg')
  have ht := (KFCausalMassFormOperator.graph_domain_iff (H t) (J u)
    (y+(Real.exp (2*t)-Real.exp (2*s)) • z)).mpr
      ((KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain
        ε hε h hh hb mass2 quartic vacuum t u _).mpr
          (affine_pairing J A B s t u y z hp hz))
  simpa only [hj] using ht

theorem common_domain_eq (s t : ℝ) :
    (H s).domain ⊓ (G).domain=(H t).domain ⊓ (G).domain :=
  domain_intersection_eq H G (fun s t => Real.exp (2*t)-Real.exp (2*s))
    (affine_graph ε hε h hh hb mass2 quartic vacuum) s t

def output (s : ℝ) (x : Hilbert) (hx : x ∈ (H s).domain) (hg : x ∈ (G).domain)
    (t : ℝ) : Hilbert := H t ⟨x,by
      have hd : x ∈ (H s).domain ⊓ (G).domain := ⟨hx,hg⟩
      rw [common_domain_eq ε hε h hh hb mass2 quartic vacuum s t] at hd
      exact hd.1⟩

theorem output_formula (s : ℝ) (x : Hilbert)
    (hx : x ∈ (H s).domain) (hg : x ∈ (G).domain) (t : ℝ) :
    output ε hε h hh hb mass2 quartic vacuum s x hx hg t=
      H s ⟨x,hx⟩+(Real.exp (2*t)-Real.exp (2*s)) • G ⟨x,hg⟩ := by
  have he := (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨x,by
      have hd : x ∈ (H s).domain ⊓ (G).domain := ⟨hx,hg⟩
      rw [common_domain_eq ε hε h hh hb mass2 quartic vacuum s t] at hd
      exact hd.1⟩)
    (affine_graph ε hε h hh hb mass2 quartic vacuum s t x (H s ⟨x,hx⟩)
      (G ⟨x,hg⟩) ((H s).mem_graph ⟨x,hx⟩) ((G).mem_graph ⟨x,hg⟩))
  exact he rfl

theorem output_derivative (s : ℝ) (x : Hilbert)
    (hx : x ∈ (H s).domain) (hg : x ∈ (G).domain) (t : ℝ) :
    HasDerivAt (output ε hε h hh hb mass2 quartic vacuum s x hx hg)
      ((2*Real.exp (2*t)) • G ⟨x,hg⟩) t := by
  have he : output ε hε h hh hb mass2 quartic vacuum s x hx hg=
      fun r => H s ⟨x,hx⟩+(Real.exp (2*r)-Real.exp (2*s)) • G ⟨x,hg⟩ :=
    funext (output_formula ε hε h hh hb mass2 quartic vacuum s x hx hg)
  rw [he]
  exact affine_derivative s t (H s ⟨x,hx⟩) (G ⟨x,hg⟩)

#print axioms affine_graph
#print axioms common_domain_eq
#print axioms output_formula
#print axioms output_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingCommonDomain
