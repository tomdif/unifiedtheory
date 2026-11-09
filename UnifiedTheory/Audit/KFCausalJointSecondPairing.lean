/- Second factor witnesses represent the entire closed weighted energy
form. Extension is through the actual joint graph closure, not a presumed
common core for the individual closures. -/
import UnifiedTheory.Audit.KFCausalFiniteJointGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalJointSecondPairing
noncomputable section
open Set
open KFCausalFiniteJointGraph
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype ι]

theorem formal_graph_pairing (T R : H →ₗ.[ℂ] H) (hTR : T.IsFormalAdjoint R)
    (u z v w : H) (huz : (u,z) ∈ R.graph) (hvw : (v,w) ∈ T.graph) :
    inner ℂ u w = inner ℂ z v := by
  obtain ⟨x,hx,hz⟩ := (LinearPMap.mem_graph_iff R).mp huz
  obtain ⟨y,hy,hw⟩ := (LinearPMap.mem_graph_iff T).mp hvw
  simpa only [hx,hz,hy,hw] using (hTR.symm x y).symm

def weighted (c : ι → ℂ) (g : ι → H) : Output ι H :=
  WithLp.toLp 2 (fun i => c i • g i)

def secondWeighted (c : ι → ℂ) (z : ι → H) : H :=
  ∑ i, (star (c i)*c i) • z i

theorem joint_pairing (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (g z : ι → H)
    (hp : ∀ i v w, (v,w) ∈ (T i).graph → inner ℂ (g i) w = inner ℂ (z i) v)
    (v : H) (w : Output ι H) (hvw : (v,w) ∈ jointGraph T c) :
    inner ℂ (weighted c g) w = inner ℂ (secondWeighted c z) v := by
  rw [PiLp.inner_apply,secondWeighted,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (c i • g i) (w i) = _
  rw [inner_smul_left,hp i _ _ (hvw i),inner_smul_right,inner_smul_left]
  simp only [map_mul,starRingEnd_apply,star_star]
  ring

theorem joint_closure_pairing (T : ι → H →ₗ.[ℂ] H) (c : ι → ℂ) (g z : ι → H)
    (hp : ∀ i v w, (v,w) ∈ (T i).graph → inner ℂ (g i) w = inner ℂ (z i) v)
    (v : H) (w : Output ι H) (hvw : (v,w) ∈ (jointGraph T c).topologicalClosure) :
    inner ℂ (weighted c g) w = inner ℂ (secondWeighted c z) v := by
  have hc : IsClosed {p : H × Output ι H |
      inner ℂ (weighted c g) p.2 = inner ℂ (secondWeighted c z) p.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hs : (jointGraph T c : Set (H × Output ι H)) ⊆
      {p : H × Output ι H | inner ℂ (weighted c g) p.2 = inner ℂ (secondWeighted c z) p.1} := by
    intro p hp'
    exact joint_pairing T c g z hp p.1 p.2 hp'
  exact closure_minimal hs hc
    (show (v,w) ∈ closure (jointGraph T c : Set (H × Output ι H)) from hvw)

#print axioms formal_graph_pairing
#print axioms joint_pairing
#print axioms joint_closure_pairing
end
end UnifiedTheory.Audit.KFCausalJointSecondPairing
