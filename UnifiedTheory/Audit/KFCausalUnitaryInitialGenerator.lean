/- A unitary family's strong initial derivative, known on an operator
core, identifies the closure of its entire initial derivative graph. -/
import UnifiedTheory.Audit.KFCausalResolventGraphCore
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalUnitaryInitialGenerator
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem derivative_mem_graph (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (C : Set (H × H)) (hC : closure C = (T.graph : Set (H × H)))
    (U : ℝ → H → H) (s : ℝ) (hi : ∀ t x y, inner ℂ (U t x) (U t y) = inner ℂ x y)
    (h0 : ∀ x, U s x = x) (c : ℂ) (hc : c ≠ 0) (hconj : starRingEnd ℂ c = -c)
    (hd : ∀ p ∈ C, HasDerivAt (fun t => U t p.1) (c • p.2) s)
    (f z : H) (hf : HasDerivAt (fun t => U t f) (c • z) s) :
    (f,z) ∈ T.graph := by
  have hzero : C ⊆ {p : H × H | inner ℂ p.2 f-inner ℂ p.1 z = 0} := by
    intro p hp
    have hi0 : HasDerivAt (fun t => inner ℂ (U t p.1) (U t f)) 0 s := by
      have he : (fun t => inner ℂ (U t p.1) (U t f)) = fun _ : ℝ => inner ℂ p.1 f :=
        funext (fun t => hi t p.1 f)
      rw [he]
      exact hasDerivAt_const s _
    have he := ((hd p hp).inner ℂ hf).unique hi0
    have he' : c*(inner ℂ p.1 z-inner ℂ p.2 f) = 0 := by
      simpa only [h0,inner_smul_left,inner_smul_right,hconj,neg_mul,mul_sub,
        sub_eq_add_neg,mul_add,mul_neg] using he
    exact sub_eq_zero.mpr (sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left hc)).symm
  have hclosed : IsClosed {p : H × H | inner ℂ p.2 f-inner ℂ p.1 z = 0} :=
    isClosed_eq ((continuous_snd.inner (𝕜 := ℂ) continuous_const).sub
      (continuous_fst.inner (𝕜 := ℂ) continuous_const)) continuous_const
  have hall := closure_minimal hzero hclosed
  rw [hC] at hall
  have hadj : (f,z) ∈ T.graph.adjoint :=
    (Submodule.mem_adjoint_iff T.graph (f,z)).mpr (fun a b hab => hall hab)
  have heq : T.graph.adjoint = T.graph :=
    (LinearPMap.adjoint_graph_eq_graph_adjoint hT.dense_domain).symm.trans
      (congrArg LinearPMap.graph (LinearPMap.isSelfAdjoint_def.mp hT))
  exact heq ▸ hadj

theorem initial_generator_graph_closure (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (C : Set (H × H)) (hC : closure C = (T.graph : Set (H × H)))
    (U : ℝ → H → H) (s : ℝ) (hi : ∀ t x y, inner ℂ (U t x) (U t y) = inner ℂ x y)
    (h0 : ∀ x, U s x = x) (c : ℂ) (hc : c ≠ 0) (hconj : starRingEnd ℂ c = -c)
    (hd : ∀ p ∈ C, HasDerivAt (fun t => U t p.1) (c • p.2) s) :
    closure {p : H × H | HasDerivAt (fun t => U t p.1) (c • p.2) s} =
      (T.graph : Set (H × H)) := by
  apply Subset.antisymm
  · exact closure_minimal
      (fun p hp => derivative_mem_graph T hT C hC U s hi h0 c hc hconj hd p.1 p.2 hp)
      hT.isClosed
  · rw [← hC]
    exact closure_mono hd

#print axioms derivative_mem_graph
#print axioms initial_generator_graph_closure
end
end UnifiedTheory.Audit.KFCausalUnitaryInitialGenerator
