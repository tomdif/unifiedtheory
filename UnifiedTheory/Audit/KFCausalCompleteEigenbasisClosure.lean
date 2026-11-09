/- A complete eigenbasis determines the entire graph closure of a symmetric
operator. Finite eigenvector sums converge in the graph norm exactly when
the weighted coefficients are square summable. -/
import UnifiedTheory.Audit.KFCausalProductHilbertExpansion
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompleteEigenbasisClosure
noncomputable section
open Filter
open scoped Topology ENNReal

variable {ι : Type*} [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →ₗ.[ℂ] H) (B : HilbertBasis ι ℂ H) (e : ι → ℝ)
  (hs : A.IsFormalAdjoint A) (he : ∀ n, (B n, (e n:ℂ) • B n) ∈ A.graph)

include he
theorem dense : Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← B.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (he n)

include hs
theorem closable : A.IsClosable :=
  (LinearPMap.adjoint_isClosed (dense A B e he)).isClosable.leIsClosable
    (hs.le_adjoint (dense A B e he))

theorem core_coefficient (f g : H) (hfg : (f, g) ∈ A.graph) (n : ι) :
    inner ℂ (B n) g = (e n:ℂ)*inner ℂ (B n) f := by
  obtain ⟨u, hu, hv⟩ := (LinearPMap.mem_graph_iff A).mp (he n)
  obtain ⟨v, hf, hg⟩ := (LinearPMap.mem_graph_iff A).mp hfg
  have hp := hs u v
  rw [hu, hv, hf, hg, inner_smul_left, Complex.conj_ofReal] at hp
  exact hp.symm

theorem graph_iff (f g : H) : (f, g) ∈ A.closure.graph ↔
    ∀ n, inner ℂ (B n) g = (e n:ℂ)*inner ℂ (B n) f := by
  constructor
  · intro hfg n
    have hc : IsClosed {p : H × H |
        inner ℂ (B n) p.2 = (e n:ℂ)*inner ℂ (B n) p.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : (A.graph : Set (H × H)) ⊆ {p : H × H |
        inner ℂ (B n) p.2 = (e n:ℂ)*inner ℂ (B n) p.1} :=
      fun p hp => core_coefficient A B e hs he p.1 p.2 hp n
    rw [← (closable A B e hs he).graph_closure_eq_closure_graph] at hfg
    exact closure_minimal hsub hc hfg
  · intro hfg
    have hm (n : ι) :
        (inner ℂ (B n) f • B n, inner ℂ (B n) g • B n) ∈ A.closure.graph := by
      rw [hfg n]
      have hn := A.graph.smul_mem (inner ℂ (B n) f) (he n)
      apply LinearPMap.le_graph_of_le A.le_closure
      simpa only [Prod.smul_mk, smul_smul, mul_comm] using hn
    have hf : HasSum (fun n => inner ℂ (B n) f • B n) f := by
      simpa only [HilbertBasis.repr_apply_apply] using B.hasSum_repr f
    have hg : HasSum (fun n => inner ℂ (B n) g • B n) g := by
      simpa only [HilbertBasis.repr_apply_apply] using B.hasSum_repr g
    exact (closable A B e hs he).closure_isClosed.mem_of_tendsto (hf.prodMk_nhds hg)
      (Filter.Eventually.of_forall (fun s : Finset ι => by
        simpa only [← prod_mk_sum] using A.closure.graph.sum_mem (fun n (_ : n ∈ s) => hm n)))

theorem domain_iff (f : H) : f ∈ A.closure.domain ↔
    Memℓp (fun n => (e n:ℂ)*inner ℂ (B n) f) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hc := (graph_iff A B e hs he f g).mp hg
    have hm := lp.memℓp (B.repr g)
    change Memℓp (fun n => B.repr g n) 2 at hm
    simpa only [HilbertBasis.repr_apply_apply, hc] using hm
  · intro hf
    let G : ℓ²(ι, ℂ) := ⟨(fun n => (e n:ℂ)*inner ℂ (B n) f), hf⟩
    refine ⟨B.repr.symm G, (graph_iff A B e hs he f _).mpr ?_⟩
    intro n
    rw [← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

theorem domain_iff_summable (f : H) : f ∈ A.closure.domain ↔
    Summable (fun n => (e n)^2*‖inner ℂ (B n) f‖^2) := by
  rw [domain_iff A B e hs he, memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

#print axioms closable
#print axioms graph_iff
#print axioms domain_iff_summable
end
end UnifiedTheory.Audit.KFCausalCompleteEigenbasisClosure
