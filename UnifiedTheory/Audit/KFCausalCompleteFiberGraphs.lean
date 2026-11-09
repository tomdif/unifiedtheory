/- A complete orthogonal fiber expansion identifies an entire closed graph.
Self-adjoint fiber graphs and their actual inclusion are sufficient. -/
import UnifiedTheory.Audit.KFCausalProductHilbertExpansion
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompleteFiberGraphs
noncomputable section
open Filter
open scoped Topology ENNReal
variable {ι H F : Type*} [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def column (W : H ≃ₗᵢ[ℂ] ℓ²(ι,F)) (i : ι) : F →L[ℂ] H :=
  W.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ι => F) 2 i)

theorem column_inner (W : H ≃ₗᵢ[ℂ] ℓ²(ι,F)) (i : ι) (u : F) (f : H) :
    inner ℂ (column W i u) f = inner ℂ u (W f i) := by
  rw [← W.inner_map_map]
  change inner ℂ (W (W.symm (lp.single 2 i u))) (W f) = _
  rw [LinearIsometryEquiv.apply_symm_apply, lp.inner_single_left]

theorem reconstruction (W : H ≃ₗᵢ[ℂ] ℓ²(ι,F)) (f : H) :
    HasSum (fun i => column W i (W f i)) f := by
  have he := W.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) (W f))
  change HasSum (fun i => column W i (W f i)) (W.symm (W f)) at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

/-- Closedness extends a verified packet graph through a separately proved graph core. -/
theorem core_inclusion {κ : Type*} (A : H →ₗ.[ℂ] H) (hA : A.IsClosed)
    (J : F →L[ℂ] H) (D : Submodule ℂ (F × F)) (v : κ → F × F)
    (hcore : (Submodule.span ℂ (Set.range v)).topologicalClosure = D)
    (hv : ∀ k, (J (v k).1,J (v k).2) ∈ A.graph) (u w : F) (huw : (u,w) ∈ D) :
    (J u,J w) ∈ A.graph := by
  let L := J.prodMap J
  let S := A.graph.comap L.toLinearMap
  have hs : IsClosed (S : Set (F × F)) := hA.preimage L.continuous
  have hi : Submodule.span ℂ (Set.range v) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact hv k
  have he := Submodule.topologicalClosure_minimal _ hi hs
  rw [hcore] at he
  exact he huw

variable (W : H ≃ₗᵢ[ℂ] ℓ²(ι,F)) (A : H →ₗ.[ℂ] H) (D : ι → F →ₗ.[ℂ] F)
  (hA : IsSelfAdjoint A) (hD : ∀ i, IsSelfAdjoint (D i))
  (hinc : ∀ i u v, (u,v) ∈ (D i).graph → (column W i u,column W i v) ∈ A.graph)

include hA hD hinc
theorem graph_iff (f g : H) : (f,g) ∈ A.graph ↔ ∀ i, (W f i,W g i) ∈ (D i).graph := by
  constructor
  · intro hfg i
    have hs := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at hs
    rw [← LinearPMap.isSelfAdjoint_def.mp (hD i),
      LinearPMap.adjoint_graph_eq_graph_adjoint (hD i).dense_domain,
      Submodule.mem_adjoint_iff]
    intro u v huv
    have hj := hinc i u v huv
    obtain ⟨a,ha,hb⟩ := (LinearPMap.mem_graph_iff A).mp hj
    obtain ⟨r,hr,hs'⟩ := (LinearPMap.mem_graph_iff A).mp hfg
    have he := hs a r
    rw [ha,hb,hr,hs',column_inner,column_inner] at he
    exact sub_eq_zero.mpr he
  · intro hf
    have hm i := hinc i (W f i) (W g i) (hf i)
    exact hA.isClosed.mem_of_tendsto ((reconstruction W f).prodMk_nhds (reconstruction W g))
      (Filter.Eventually.of_forall (fun s : Finset ι => by
        simpa only [← prod_mk_sum] using A.graph.sum_mem (fun i (_ : i ∈ s) => hm i)))

theorem domain_iff (f : H) : f ∈ A.domain ↔
    ∃ G : ι → F, Memℓp G 2 ∧ ∀ i, (W f i,G i) ∈ (D i).graph := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨fun i => W g i, lp.memℓp (W g), (graph_iff W A D hA hD hinc f g).mp hg⟩
  · rintro ⟨G,hG,hg⟩
    refine ⟨W.symm ⟨G,hG⟩,(graph_iff W A D hA hD hinc f _).mpr ?_⟩
    intro i
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hg i

#print axioms graph_iff
#print axioms domain_iff
end
end UnifiedTheory.Audit.KFCausalCompleteFiberGraphs
