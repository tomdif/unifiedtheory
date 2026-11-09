/- Unconditional Hamiltonian and three-operator cross-estimates for all real
couplings and times (without vacuum-coupling positivity). On the reference
residual form domain Dom Tres(0) and on every pairwise common domain of H(t) or
S(t) with G, T, or P, the three self-adjoint components T, Kr, and P satisfy
exact operator-sum identities together with simultaneous norm-square bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorThreeOperatorCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalHamiltonianCrossEstimate
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorThreeOperatorCrossEstimate (potential_radial_pairing)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph
   unconditional_three_operator_hamiltonian_graph
   residual_growing_common_domain_eq
   hamiltonian_residual_common_domain_eq
   hamiltonian_growing_common_domain_eq
   hamiltonian_static_common_domain_eq)

private theorem sum_graph {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B : X →ₗ.[ℂ] X) (f a b : X)
    (ha : (f,a) ∈ A.graph) (hb : (f,b) ∈ B.graph) : (f,a+b) ∈ (A+B).graph := by
  have hda := LinearPMap.mem_domain_of_mem_graph ha
  have hdb := LinearPMap.mem_domain_of_mem_graph hb
  have hea : A ⟨f,hda⟩=a := A.mem_graph_snd_inj' (A.mem_graph ⟨f,hda⟩) ha rfl
  have heb : B ⟨f,hdb⟩=b := B.mem_graph_snd_inj' (B.mem_graph ⟨f,hdb⟩) hb rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hda,hdb⟩⟩,rfl,by
    change A ⟨f,hda⟩+B ⟨f,hdb⟩=a+b
    rw [hea,heb]⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

theorem unconditional_three_operator_cross_estimate
    (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph)
    (hres : f ∈ (Tres 0).domain) :
    (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph ∧
      (f,y+(Real.exp (2*t):ℂ) • (r+z)) ∈ (H).graph ∧
      0 ≤ (inner ℂ z r).re ∧
      -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ (y+(Real.exp (2*t):ℂ) • z) r).re ∧
      Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
        ‖y+(Real.exp (2*t):ℂ) • (r+z)‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have hs := unconditional_three_operator_residual_graph
    ε hε h hh hb m g k t f y z ht hp hres
  have hh_g := unconditional_three_operator_hamiltonian_graph
    ε hε h hh hb m g k t f y r z ht hr hp hres
  have hpot := (potential_radial_pairing ε hε h hh hb m g k f r z hr hp).1
  have hH := KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k t f (y+(Real.exp (2*t):ℂ) • (r+z)) r (y+(Real.exp (2*t):ℂ) • z)
    hh_g hr hs
  exact ⟨hs,hh_g,hpot,hH.1,hH.2⟩

theorem unconditional_static_growing_cross_estimate
    (f y g_out : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hg : (f,g_out) ∈ (G).graph)
    (hres : f ∈ (Tres 0).domain) :
    let xG : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hg⟩
    let r := KFCausalClockFloorGrowingRadialCrossEstimate.radialOutput ε hε h hh hb m g k xG
    let z := KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput ε hε h hh hb m g k xG
    ‖r‖^2+‖z‖^2 ≤ ‖g_out‖^2 ∧
      (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph ∧
      (f,y+(Real.exp (2*t):ℂ) • g_out) ∈ (H).graph ∧
      Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
        ‖y+(Real.exp (2*t):ℂ) • g_out‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  let xG : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hg⟩
  let r := KFCausalClockFloorGrowingRadialCrossEstimate.radialOutput ε hε h hh hb m g k xG
  let z := KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput ε hε h hh hb m g k xG
  have hG : G xG=g_out := (G).mem_graph_snd_inj' ((G).mem_graph xG) hg rfl
  have hr : (f,r) ∈ (K).graph :=
    (K).mem_graph ⟨f,KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k xG⟩
  have hp : (f,z) ∈ (P).graph :=
    KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb m g k xG
  have hrz : r+z=g_out := by
    dsimp [r,z]
    unfold KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput
    rw [hG]
    abel
  have hsplit : ‖r‖^2+‖z‖^2 ≤ ‖g_out‖^2 := by
    simpa only [hG] using
      KFCausalClockFloorGrowingRadialCrossEstimate.split_norm_square ε hε h hh hb m g k xG
  have h3 := unconditional_three_operator_cross_estimate
    ε hε h hh hb m g k t f y r z ht hr hp hres
  have hh_g : (f,y+(Real.exp (2*t):ℂ) • g_out) ∈ (H).graph := by
    rw [← hrz]
    exact h3.2.1
  have hcross : Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
      ‖y+(Real.exp (2*t):ℂ) • g_out‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
    rw [← hrz]
    exact h3.2.2.2.2
  exact ⟨hsplit,h3.1,hh_g,hcross⟩

theorem hamiltonian_growing_domain_cross_estimate (f : Hilbert)
    (hf : f ∈ (H).domain ∧ f ∈ (G).domain) :
    ∃ (hT : f ∈ (T).domain) (hK : f ∈ (K).domain) (hP : f ∈ (P).domain)
      (hS : f ∈ (S).domain) (hG : f ∈ (G).domain) (hH : f ∈ (H).domain),
      (G) ⟨f,hG⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ ∧
      (S) ⟨f,hS⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (P) ⟨f,hP⟩ ∧
      (H) ⟨f,hH⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (G) ⟨f,hG⟩ ∧
      (H) ⟨f,hH⟩=(S) ⟨f,hS⟩+(Real.exp (2*t):ℂ) • (K) ⟨f,hK⟩ ∧
      ‖(K) ⟨f,hK⟩‖^2+‖(P) ⟨f,hP⟩‖^2 ≤ ‖(G) ⟨f,hG⟩‖^2 ∧
      Real.exp (4*t)*‖(K) ⟨f,hK⟩‖^2+‖(S) ⟨f,hS⟩‖^2 ≤
        ‖(H) ⟨f,hH⟩‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have hmem : f ∈ ((H).domain ⊓ (G).domain : Submodule ℂ Hilbert) := hf
  have h4 := (Set.ext_iff.mp (congrArg SetLike.coe
    (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t)) f).mp hmem
  rcases h4 with ⟨⟨⟨hT,hK⟩,hP⟩,hres⟩
  have hS : f ∈ (S).domain :=
    ((KFCausalClockFloorHamiltonianRadialSum.domain_iff ε hε h hh hb m g k t f).mp hf.1).2
  refine ⟨hT,hK,hP,hS,hf.2,hf.1,?_,?_,?_,?_,?_,?_⟩
  · have hg' : (f,(K) ⟨f,hK⟩+(P) ⟨f,hP⟩) ∈ (G).graph := by
      rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
      exact sum_graph (K) (P) f ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
        ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩)
    exact (G).mem_graph_snd_inj' ((G).mem_graph ⟨f,hf.2⟩) hg' rfl
  · have hs' := (unconditional_three_operator_cross_estimate
      ε hε h hh hb m g k t f ((T) ⟨f,hT⟩) ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
      ((T).mem_graph ⟨f,hT⟩) ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩) hres).1
    exact (S).mem_graph_snd_inj' ((S).mem_graph ⟨f,hS⟩) hs' rfl
  · have hg' : (f,(K) ⟨f,hK⟩+(P) ⟨f,hP⟩) ∈ (G).graph := by
      rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
      exact sum_graph (K) (P) f ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
        ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩)
    have hG_eq : (G) ⟨f,hf.2⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ :=
      (G).mem_graph_snd_inj' ((G).mem_graph ⟨f,hf.2⟩) hg' rfl
    have hh' := (unconditional_three_operator_cross_estimate
      ε hε h hh hb m g k t f ((T) ⟨f,hT⟩) ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
      ((T).mem_graph ⟨f,hT⟩) ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩) hres).2.1
    rw [hG_eq]
    exact (H).mem_graph_snd_inj' ((H).mem_graph ⟨f,hf.1⟩) hh' rfl
  · have hs' := (unconditional_three_operator_cross_estimate
      ε hε h hh hb m g k t f ((T) ⟨f,hT⟩) ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
      ((T).mem_graph ⟨f,hT⟩) ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩) hres).1
    have hS_eq : (S) ⟨f,hS⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (P) ⟨f,hP⟩ :=
      (S).mem_graph_snd_inj' ((S).mem_graph ⟨f,hS⟩) hs' rfl
    have hh' := (unconditional_three_operator_cross_estimate
      ε hε h hh hb m g k t f ((T) ⟨f,hT⟩) ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
      ((T).mem_graph ⟨f,hT⟩) ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩) hres).2.1
    have hH_eq : (H) ⟨f,hf.1⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • ((K) ⟨f,hK⟩+(P) ⟨f,hP⟩) :=
      (H).mem_graph_snd_inj' ((H).mem_graph ⟨f,hf.1⟩) hh' rfl
    rw [hH_eq,hS_eq,smul_add]
    abel
  · have hg' : (f,(K) ⟨f,hK⟩+(P) ⟨f,hP⟩) ∈ (G).graph := by
      rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
      exact sum_graph (K) (P) f ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
        ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩)
    have hG_eq : (G) ⟨f,hf.2⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ :=
      (G).mem_graph_snd_inj' ((G).mem_graph ⟨f,hf.2⟩) hg' rfl
    rw [hG_eq]
    exact (potential_radial_pairing ε hε h hh hb m g k f ((K) ⟨f,hK⟩) ((P) ⟨f,hP⟩)
      ((K).mem_graph ⟨f,hK⟩) ((P).mem_graph ⟨f,hP⟩)).2
  · exact (KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
      ε hε h hh hb m g k t f ((H) ⟨f,hf.1⟩) ((K) ⟨f,hK⟩) ((S) ⟨f,hS⟩)
      ((H).mem_graph ⟨f,hf.1⟩) ((K).mem_graph ⟨f,hK⟩) ((S).mem_graph ⟨f,hS⟩)).2

theorem hamiltonian_static_domain_cross_estimate (f : Hilbert)
    (hf : f ∈ (H).domain ∧ f ∈ (T).domain) :
    ∃ (hT : f ∈ (T).domain) (hK : f ∈ (K).domain) (hP : f ∈ (P).domain)
      (hS : f ∈ (S).domain) (hG : f ∈ (G).domain) (hH : f ∈ (H).domain),
      (G) ⟨f,hG⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ ∧
      (S) ⟨f,hS⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (P) ⟨f,hP⟩ ∧
      (H) ⟨f,hH⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (G) ⟨f,hG⟩ ∧
      (H) ⟨f,hH⟩=(S) ⟨f,hS⟩+(Real.exp (2*t):ℂ) • (K) ⟨f,hK⟩ ∧
      ‖(K) ⟨f,hK⟩‖^2+‖(P) ⟨f,hP⟩‖^2 ≤ ‖(G) ⟨f,hG⟩‖^2 ∧
      Real.exp (4*t)*‖(K) ⟨f,hK⟩‖^2+‖(S) ⟨f,hS⟩‖^2 ≤
        ‖(H) ⟨f,hH⟩‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have heq : (H).domain ⊓ (T).domain=(H).domain ⊓ (G).domain :=
    (hamiltonian_static_common_domain_eq ε hε h hh hb m g k t).trans
      (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t).symm
  have hmem : f ∈ ((H).domain ⊓ (T).domain : Submodule ℂ Hilbert) := hf
  have hg : f ∈ (H).domain ∧ f ∈ (G).domain :=
    (Set.ext_iff.mp (congrArg SetLike.coe heq) f).mp hmem
  exact hamiltonian_growing_domain_cross_estimate ε hε h hh hb m g k t f hg

theorem hamiltonian_potential_domain_cross_estimate (f : Hilbert)
    (hf : f ∈ (H).domain ∧ f ∈ (P).domain) :
    ∃ (hT : f ∈ (T).domain) (hK : f ∈ (K).domain) (hP : f ∈ (P).domain)
      (hS : f ∈ (S).domain) (hG : f ∈ (G).domain) (hH : f ∈ (H).domain),
      (G) ⟨f,hG⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ ∧
      (S) ⟨f,hS⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (P) ⟨f,hP⟩ ∧
      (H) ⟨f,hH⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (G) ⟨f,hG⟩ ∧
      (H) ⟨f,hH⟩=(S) ⟨f,hS⟩+(Real.exp (2*t):ℂ) • (K) ⟨f,hK⟩ ∧
      ‖(K) ⟨f,hK⟩‖^2+‖(P) ⟨f,hP⟩‖^2 ≤ ‖(G) ⟨f,hG⟩‖^2 ∧
      Real.exp (4*t)*‖(K) ⟨f,hK⟩‖^2+‖(S) ⟨f,hS⟩‖^2 ≤
        ‖(H) ⟨f,hH⟩‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have heq : (H).domain ⊓ (P).domain=(H).domain ⊓ (G).domain :=
    (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t).trans
      (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t).symm
  have hmem : f ∈ ((H).domain ⊓ (P).domain : Submodule ℂ Hilbert) := hf
  have hg : f ∈ (H).domain ∧ f ∈ (G).domain :=
    (Set.ext_iff.mp (congrArg SetLike.coe heq) f).mp hmem
  exact hamiltonian_growing_domain_cross_estimate ε hε h hh hb m g k t f hg

theorem residual_growing_domain_cross_estimate (f : Hilbert)
    (hf : f ∈ (S).domain ∧ f ∈ (G).domain) :
    ∃ (hT : f ∈ (T).domain) (hK : f ∈ (K).domain) (hP : f ∈ (P).domain)
      (hS : f ∈ (S).domain) (hG : f ∈ (G).domain) (hH : f ∈ (H).domain),
      (G) ⟨f,hG⟩=(K) ⟨f,hK⟩+(P) ⟨f,hP⟩ ∧
      (S) ⟨f,hS⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (P) ⟨f,hP⟩ ∧
      (H) ⟨f,hH⟩=(T) ⟨f,hT⟩+(Real.exp (2*t):ℂ) • (G) ⟨f,hG⟩ ∧
      (H) ⟨f,hH⟩=(S) ⟨f,hS⟩+(Real.exp (2*t):ℂ) • (K) ⟨f,hK⟩ ∧
      ‖(K) ⟨f,hK⟩‖^2+‖(P) ⟨f,hP⟩‖^2 ≤ ‖(G) ⟨f,hG⟩‖^2 ∧
      Real.exp (4*t)*‖(K) ⟨f,hK⟩‖^2+‖(S) ⟨f,hS⟩‖^2 ≤
        ‖(H) ⟨f,hH⟩‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have heq : (S).domain ⊓ (G).domain=(H).domain ⊓ (G).domain :=
    (residual_growing_common_domain_eq ε hε h hh hb m g k t).trans
      (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t).symm
  have hmem : f ∈ ((S).domain ⊓ (G).domain : Submodule ℂ Hilbert) := hf
  have hg : f ∈ (H).domain ∧ f ∈ (G).domain :=
    (Set.ext_iff.mp (congrArg SetLike.coe heq) f).mp hmem
  exact hamiltonian_growing_domain_cross_estimate ε hε h hh hb m g k t f hg

#print axioms unconditional_three_operator_cross_estimate
#print axioms unconditional_static_growing_cross_estimate
#print axioms hamiltonian_growing_domain_cross_estimate
#print axioms hamiltonian_static_domain_cross_estimate
#print axioms hamiltonian_potential_domain_cross_estimate
#print axioms residual_growing_domain_cross_estimate
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalHamiltonianCrossEstimate
