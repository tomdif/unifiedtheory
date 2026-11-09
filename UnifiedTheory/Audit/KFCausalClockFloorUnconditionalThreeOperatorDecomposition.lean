/- Unconditional Three-Operator Decomposition for all real couplings (without
positivity of the vacuum coupling): on the reference residual form domain
Dom Tres(0), the maximal static operator T, maximal radial operator Kr, and
closed potential Hamiltonian P reconstruct both the residual Hamiltonian S(t)
and the full Hamiltonian H(t), and all pairwise common domains of H(t) and S(t)
with P, T, and G equal (Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0). -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorUnconditionalFormDomainSynthesis (residual_domain_time_eq)

private theorem sum_graph {H : Type*} [AddCommGroup H] [Module ℂ H]
    (K P : H →ₗ.[ℂ] H) (f r p : H)
    (hr : (f,r) ∈ K.graph) (hp : (f,p) ∈ P.graph) : (f,r+p) ∈ (K+P).graph := by
  have hk := LinearPMap.mem_domain_of_mem_graph hr
  have hp' := LinearPMap.mem_domain_of_mem_graph hp
  have heK : K ⟨f,hk⟩=r := K.mem_graph_snd_inj' (K.mem_graph ⟨f,hk⟩) hr rfl
  have heP : P ⟨f,hp'⟩=p := P.mem_graph_snd_inj' (P.mem_graph ⟨f,hp'⟩) hp rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hk,hp'⟩⟩,rfl,by
    change K ⟨f,hk⟩+P ⟨f,hp'⟩=r+p
    rw [heK,heP]⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

theorem residual_hamiltonian_domain_subset_residual_form (x : Hilbert)
    (hx : x ∈ (S).domain) : x ∈ (Tres 0).domain := by
  let w := KFCausalClosedGraphForm.formLift SD ⟨x,hx⟩
  have hemb : KFCausalClosedGraphForm.embedding SD w=x :=
    KFCausalClosedGraphForm.embedding_formLift SD ⟨x,hx⟩
  have ht : x ∈ (Tres t).domain :=
    (congrArg (fun a : Hilbert => a ∈ (Tres t).domain) hemb).mp
      (LinearPMap.mem_domain_of_mem_graph w.property)
  exact (residual_domain_time_eq ε hε h hh hb m g k t 0 x).mp ht

theorem unconditional_three_operator_residual_graph (x y z : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hp : (x,z) ∈ (P).graph) (hres : x ∈ (Tres 0).domain) :
    (x,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph := by
  have hst : x ∈ (Tres t).domain :=
    (residual_domain_time_eq ε hε h hh hb m g k 0 t x).mp hres
  let w := KFCausalClosedGraphForm.graphVector SD ⟨x,hst⟩
  have hemb : KFCausalClosedGraphForm.embedding SD w=x :=
    KFCausalClosedGraphForm.graphVector_embedding SD ⟨x,hst⟩
  have ht' : (KFCausalClosedGraphForm.embedding SD w,y) ∈ (T).graph :=
    (congrArg (fun a : Hilbert => (a,y) ∈ (T).graph) hemb.symm).mp ht
  have hp' : (KFCausalClosedGraphForm.embedding SD w,z) ∈ (P).graph :=
    (congrArg (fun a : Hilbert => (a,z) ∈ (P).graph) hemb.symm).mp hp
  have hg := KFCausalClockFloorResidualStaticPotentialDecomposition.sum_graph
    ε hε h hh hw m g k t w y z ht' hp'
  exact (congrArg (fun a : Hilbert => (a,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph) hemb).mp hg

theorem unconditional_three_operator_hamiltonian_graph (x y r z : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hr : (x,r) ∈ (K).graph) (hp : (x,z) ∈ (P).graph)
    (hres : x ∈ (Tres 0).domain) :
    (x,y+(Real.exp (2*t):ℂ) • (r+z)) ∈ (H).graph := by
  have hs := unconditional_three_operator_residual_graph ε hε h hh hb m g k t x y z ht hp hres
  have hk := LinearPMap.mem_domain_of_mem_graph hr
  have heK : (K) ⟨x,hk⟩=r := (K).mem_graph_snd_inj' ((K).mem_graph ⟨x,hk⟩) hr rfl
  have hkr : (x,(Real.exp (2*t):ℂ) • r) ∈ ((Real.exp (2*t):ℂ) • (K)).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨x,hk⟩,rfl,by
      change (Real.exp (2*t):ℂ) • (K) ⟨x,hk⟩=_
      rw [heK]⟩
  have hsum := sum_graph ((Real.exp (2*t):ℂ) • (K)) (S) x
    ((Real.exp (2*t):ℂ) • r) (y+(Real.exp (2*t):ℂ) • z) hkr hs
  rw [← KFCausalClockFloorHamiltonianRadialSum.operator_sum ε hε h hh hb m g k t] at hsum
  have ha : (Real.exp (2*t):ℂ) • r+(y+(Real.exp (2*t):ℂ) • z)=
      y+(Real.exp (2*t):ℂ) • (r+z) := by
    rw [smul_add]
    abel
  exact (congrArg (fun v : Hilbert => (x,v) ∈ (H).graph) ha).mp hsum

theorem unconditional_static_growing_hamiltonian_graph (x y gVec : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hg : (x,gVec) ∈ (G).graph)
    (hres : x ∈ (Tres 0).domain) :
    (x,y+(Real.exp (2*t):ℂ) • gVec) ∈ (H).graph := by
  have hgdom : x ∈ (G).domain := LinearPMap.mem_domain_of_mem_graph hg
  obtain ⟨hk,hp⟩ := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hgdom
  have hkp : (x,(K) ⟨x,hk⟩+(P) ⟨x,hp⟩) ∈ (G).graph := by
    rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
    exact sum_graph (K) (P) x ((K) ⟨x,hk⟩) ((P) ⟨x,hp⟩)
      ((K).mem_graph ⟨x,hk⟩) ((P).mem_graph ⟨x,hp⟩)
  have heq : gVec=(K) ⟨x,hk⟩+(P) ⟨x,hp⟩ :=
    (G).mem_graph_snd_inj' hg hkp rfl
  rw [heq]
  exact unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
    x y ((K) ⟨x,hk⟩) ((P) ⟨x,hp⟩) ht ((K).mem_graph ⟨x,hk⟩) ((P).mem_graph ⟨x,hp⟩) hres

theorem residual_growing_common_domain_eq :
    (S).domain ⊓ (G).domain=((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
  ext x
  change (x ∈ (S).domain ∧ x ∈ (G).domain) ↔
    (((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain) ∧ x ∈ (Tres 0).domain)
  rw [KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x]
  have hc := Set.ext_iff.mp (congrArg SetLike.coe
    (KFCausalClockFloorResidualStaticPotentialDecomposition.common_domain_eq
      ε hε h hh hw m g k t)) x
  change (x ∈ (S).domain ∧ x ∈ (P).domain) ↔ (x ∈ (S).domain ∧ x ∈ (T).domain) at hc
  constructor
  · rintro ⟨hs,hk,hp⟩
    have ht : x ∈ (T).domain := (hc.mp ⟨hs,hp⟩).2
    have hres := residual_hamiltonian_domain_subset_residual_form ε hε h hh hb m g k t x hs
    exact ⟨⟨⟨ht,hk⟩,hp⟩,hres⟩
  · rintro ⟨⟨⟨ht,hk⟩,hp⟩,hres⟩
    have hs : x ∈ (S).domain := LinearPMap.mem_domain_of_mem_graph
      (unconditional_three_operator_residual_graph ε hε h hh hb m g k t x _ _
        ((T).mem_graph ⟨x,ht⟩) ((P).mem_graph ⟨x,hp⟩) hres)
    exact ⟨hs,hk,hp⟩

theorem hamiltonian_residual_common_domain_eq :
    (H).domain ⊓ (P).domain=((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
  ext x
  change (x ∈ (H).domain ∧ x ∈ (P).domain) ↔
    (((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain) ∧ x ∈ (Tres 0).domain)
  rw [KFCausalClockFloorHamiltonianRadialSum.domain_iff ε hε h hh hb m g k t x]
  have hc := Set.ext_iff.mp (congrArg SetLike.coe
    (KFCausalClockFloorResidualStaticPotentialDecomposition.common_domain_eq
      ε hε h hh hw m g k t)) x
  change (x ∈ (S).domain ∧ x ∈ (P).domain) ↔ (x ∈ (S).domain ∧ x ∈ (T).domain) at hc
  constructor
  · rintro ⟨⟨hk,hs⟩,hp⟩
    have ht : x ∈ (T).domain := (hc.mp ⟨hs,hp⟩).2
    have hres := residual_hamiltonian_domain_subset_residual_form ε hε h hh hb m g k t x hs
    exact ⟨⟨⟨ht,hk⟩,hp⟩,hres⟩
  · rintro ⟨⟨⟨ht,hk⟩,hp⟩,hres⟩
    have hs : x ∈ (S).domain := LinearPMap.mem_domain_of_mem_graph
      (unconditional_three_operator_residual_graph ε hε h hh hb m g k t x _ _
        ((T).mem_graph ⟨x,ht⟩) ((P).mem_graph ⟨x,hp⟩) hres)
    exact ⟨⟨hk,hs⟩,hp⟩

theorem hamiltonian_growing_common_domain_eq :
    (H).domain ⊓ (G).domain=((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
  have h1 := (KFCausalClockFloorResidualStaticPotentialDecomposition.hamiltonian_common_domain_eq
    ε hε h hh m g k t hb).1
  exact h1.symm.trans (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t)

theorem hamiltonian_static_common_domain_eq :
    (H).domain ⊓ (T).domain=((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
  have h1 := (KFCausalClockFloorResidualStaticPotentialDecomposition.hamiltonian_common_domain_eq
    ε hε h hh m g k t hb).2
  exact h1.symm.trans (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t)

#print axioms residual_hamiltonian_domain_subset_residual_form
#print axioms unconditional_three_operator_residual_graph
#print axioms unconditional_three_operator_hamiltonian_graph
#print axioms unconditional_static_growing_hamiltonian_graph
#print axioms residual_growing_common_domain_eq
#print axioms hamiltonian_residual_common_domain_eq
#print axioms hamiltonian_growing_common_domain_eq
#print axioms hamiltonian_static_common_domain_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition
