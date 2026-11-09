/- A bounded sequence in an injective closed operator graph converges
weakly to zero when an injective bounded detector of its outputs tends
strongly to zero. No compact embedding or coercive detector is assumed. -/
import UnifiedTheory.Audit.KFCausalWeakEmbeddingLimit
import UnifiedTheory.Audit.KFCausalWeakLimitTransport
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeightedGraphWeakDecay
noncomputable section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weak_zero (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (hker : ∀ x, (x,0) ∈ T.graph → x = 0)
    (B : H →L[ℂ] H) (hB : Function.Injective B)
    (x y : ℕ → H) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hx : ∀ n, ‖x n‖ ≤ C) (hy : ∀ n, ‖y n‖ ≤ D)
    (hg : ∀ n, (x n,y n) ∈ T.graph)
    (hz : Tendsto (fun n => B (y n)) atTop (𝓝 0)) :
    ∀ z, Tendsto (fun n => inner ℂ (x n) z) atTop (𝓝 0) := by
  let S : Submodule ℂ (WithLp 2 (H × H)) :=
    T.graph.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toLinearMap
  have hS : IsClosed (S : Set (WithLp 2 (H × H))) :=
    hT.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H H).continuous
  letI : CompleteSpace S := hS.completeSpace_coe
  let P : S →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp S.subtypeL
  let Q : S →L[ℂ] H := (WithLp.sndL 2 ℂ H H).comp S.subtypeL
  let A : S →L[ℂ] H := B.comp Q
  have hA : Function.Injective A := by
    intro u v huv
    have hq : Q u = Q v := hB huv
    have hzq : Q (u-v) = 0 := by rw [map_sub,hq,sub_self]
    have hg' : (P (u-v),Q (u-v)) ∈ T.graph := (u-v).property
    rw [hzq] at hg'
    have hp := hker _ hg'
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext hp hzq
  let u : ℕ → S := fun n => ⟨WithLp.toLp 2 (x n,y n),hg n⟩
  have hu (n : ℕ) : ‖u n‖ ≤ C+D := by
    have hs : ‖u n‖^2 = ‖x n‖^2+‖y n‖^2 := WithLp.prod_norm_sq_eq_of_L2 (u n).val
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hx n) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hy n) 2
    nlinarith [norm_nonneg (u n),mul_nonneg hC hD]
  have ha : Tendsto (fun n => A (u n)) atTop (𝓝 (A 0)) := by
    simpa only [map_zero] using hz
  have hw := KFCausalWeakEmbeddingLimit.weak_of_embedding A hA u 0 (C+D)
    (add_nonneg hC hD) hu ha
  intro z
  simpa only [map_zero,inner_zero_left] using KFCausalWeakLimitTransport.weak_map P hw z

#print axioms weak_zero
end
end UnifiedTheory.Audit.KFCausalWeightedGraphWeakDecay
