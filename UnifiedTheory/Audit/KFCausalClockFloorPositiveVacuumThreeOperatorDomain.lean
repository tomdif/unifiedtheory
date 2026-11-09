/- For strictly positive vacuum coupling, the three self-adjoint component
operators T (maximal static), Kr (maximal radial), and P (closed potential)
reconstruct both the full Hamiltonian H(t) and the residual Hamiltonian S(t)
on their intersection domain, without any separate form-range premise. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumCommonDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)

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

theorem three_operator_hamiltonian_graph (hk : 0 < k) (x y r z : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hr : (x,r) ∈ (K).graph) (hp : (x,z) ∈ (P).graph) :
    (x,y+(Real.exp (2*t):ℂ) • (r+z)) ∈ (H).graph := by
  have hg : (x,r+z) ∈ (G).graph := by
    rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
    exact sum_graph (K) (P) x r z hr hp
  have hs := KFCausalClockFloorPositiveVacuumCommonDomain.sum_graph
    ε hε h hh hw m g k hk t x y (r+z) ht hg
  exact (congrArg (fun v : Hilbert => (x,y+v) ∈ (H).graph)
    (Complex.coe_smul (Real.exp (2*t)) (r+z)).symm).mp hs

theorem three_operator_residual_graph (hk : 0 < k) (x y r z : Hilbert)
    (ht : (x,y) ∈ (T).graph) (hr : (x,r) ∈ (K).graph) (hp : (x,z) ∈ (P).graph) :
    (x,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph := by
  have hh' := three_operator_hamiltonian_graph ε hε h hh hb m g k t hk x y r z ht hr hp
  let xH : (H).domain := ⟨x,LinearPMap.mem_domain_of_mem_graph hh'⟩
  have hH : H xH=y+(Real.exp (2*t):ℂ) • (r+z) :=
    (H).mem_graph_snd_inj' ((H).mem_graph xH) hh' rfl
  have hK : KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb m g k t xH=r :=
    (K).mem_graph_snd_inj' ((K).mem_graph _) hr rfl
  have hs := KFCausalClockFloorHamiltonianRadialSum.residual_graph ε hε h hh hb m g k t xH
  have hout : KFCausalClockFloorHamiltonianRadialSum.residualOutput ε hε h hh hb m g k t xH=
      y+(Real.exp (2*t):ℂ) • z := by
    unfold KFCausalClockFloorHamiltonianRadialSum.residualOutput
    rw [hH,hK,smul_add]
    abel
  exact (congrArg (fun v : Hilbert => (x,v) ∈ (S).graph) hout).mp hs

theorem hamiltonian_potential_domain_eq (hk : 0 < k) :
    (H).domain ⊓ (P).domain=((T).domain ⊓ (K).domain) ⊓ (P).domain := by
  have h1 := (KFCausalClockFloorResidualStaticPotentialDecomposition.hamiltonian_common_domain_eq
    ε hε h hh m g k t hb).1
  have h2 := KFCausalClockFloorPositiveVacuumCommonDomain.common_domain_eq
    ε hε h hh hw m g k hk t
  ext x
  have e1 := Set.ext_iff.mp (congrArg SetLike.coe h1) x
  have e2 := Set.ext_iff.mp (congrArg SetLike.coe h2) x
  change (x ∈ (H).domain ∧ x ∈ (P).domain) ↔ (x ∈ (H).domain ∧ x ∈ (G).domain) at e1
  change (x ∈ (H).domain ∧ x ∈ (G).domain) ↔ (x ∈ (T).domain ∧ x ∈ (G).domain) at e2
  change (x ∈ (H).domain ∧ x ∈ (P).domain) ↔ ((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain)
  rw [e1,e2,KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x]
  tauto

theorem hamiltonian_static_domain_eq (hk : 0 < k) :
    (H).domain ⊓ (T).domain=((T).domain ⊓ (K).domain) ⊓ (P).domain := by
  have h1 := (KFCausalClockFloorResidualStaticPotentialDecomposition.hamiltonian_common_domain_eq
    ε hε h hh m g k t hb).2
  rw [← h1]
  exact hamiltonian_potential_domain_eq ε hε h hh hb m g k t hk

theorem residual_growing_domain_eq (hk : 0 < k) :
    (S).domain ⊓ (G).domain=((T).domain ⊓ (K).domain) ⊓ (P).domain := by
  ext x
  change (x ∈ (S).domain ∧ x ∈ (G).domain) ↔
    ((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain)
  rw [KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x]
  have hc := Set.ext_iff.mp (congrArg SetLike.coe
    (KFCausalClockFloorResidualStaticPotentialDecomposition.common_domain_eq
      ε hε h hh hw m g k t)) x
  change (x ∈ (S).domain ∧ x ∈ (P).domain) ↔ (x ∈ (S).domain ∧ x ∈ (T).domain) at hc
  constructor
  · rintro ⟨hs,hk',hp⟩
    have ht : x ∈ (T).domain := (hc.mp ⟨hs,hp⟩).2
    exact ⟨⟨ht,hk'⟩,hp⟩
  · rintro ⟨⟨ht,hk'⟩,hp⟩
    have hs : x ∈ (S).domain := LinearPMap.mem_domain_of_mem_graph
      (three_operator_residual_graph ε hε h hh hb m g k t hk x _ _ _
        ((T).mem_graph ⟨x,ht⟩) ((K).mem_graph ⟨x,hk'⟩) ((P).mem_graph ⟨x,hp⟩))
    exact ⟨hs,hk',hp⟩

#print axioms three_operator_hamiltonian_graph
#print axioms three_operator_residual_graph
#print axioms hamiltonian_potential_domain_eq
#print axioms hamiltonian_static_domain_eq
#print axioms residual_growing_domain_eq
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain
