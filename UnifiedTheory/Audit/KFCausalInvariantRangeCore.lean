/- A constructive core argument for an invariant linear subspace.
Strong decay of (I-P)^n makes the range of P graph-dense. The explicit
approximants use finite geometric sums, without an inverse assumption. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalInvariantRangeCore
noncomputable section
open Filter
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

def residual (P : X →L[ℂ] X) : X →L[ℂ] X := ContinuousLinearMap.id ℂ X-P

def geometricSum (P : X →L[ℂ] X) (z : X) : ℕ → X
  | 0 => 0
  | n+1 => z+residual P (geometricSum P z n)

theorem geometricSum_identity (P : X →L[ℂ] X) (z : X) (n : ℕ) :
    P (geometricSum P z n) = z-(residual P : X → X)^[n] z := by
  induction n with
  | zero => simp [geometricSum]
  | succ n ih =>
      simp only [geometricSum,residual,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
        map_add,map_sub,ih,Function.iterate_succ_apply']
      abel

theorem geometricSum_mem (P : X →L[ℂ] X) (K : Submodule ℂ X)
    (hP : ∀ z ∈ K, P z ∈ K) (z : X) (hz : z ∈ K) (n : ℕ) : geometricSum P z n ∈ K := by
  induction n with
  | zero => exact K.zero_mem
  | succ n ih => exact K.add_mem hz (K.sub_mem ih (hP _ ih))

theorem approximation_tendsto (P : X →L[ℂ] X) (z : X)
    (hz : Tendsto (fun n : ℕ => (residual P : X → X)^[n] z) atTop (𝓝 0)) :
    Tendsto (fun n => P (geometricSum P z n)) atTop (𝓝 z) := by
  simpa only [geometricSum_identity,sub_zero] using tendsto_const_nhds.sub hz

theorem range_core (P : X →L[ℂ] X) (K : Submodule ℂ X)
    (hP : ∀ z ∈ K, P z ∈ K)
    (hdec : ∀ z ∈ K, Tendsto (fun n : ℕ => (residual P : X → X)^[n] z) atTop (𝓝 0)) :
    (K.map P.toLinearMap).topologicalClosure = K.topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    rintro _ ⟨z,hz,rfl⟩
    exact hP z hz
  · apply K.topologicalClosure_minimal _ (K.map P.toLinearMap).isClosed_topologicalClosure
    intro z hz
    apply (K.map P.toLinearMap).isClosed_topologicalClosure.mem_of_tendsto
      (approximation_tendsto P z (hdec z hz))
    exact Filter.Eventually.of_forall (fun n => (K.map P.toLinearMap).le_topologicalClosure
      ⟨geometricSum P z n,geometricSum_mem P K hP z hz n,rfl⟩)

theorem prod_residual_iterate (D : X →L[ℂ] X) (B : Y →L[ℂ] Y) (f : X) (g : Y) (n : ℕ) :
    (residual (D.prodMap B) : X × Y → X × Y)^[n] (f,g) =
      ((residual D : X → X)^[n] f,(residual B : Y → Y)^[n] g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih]
      rfl

theorem prod_residual_tendsto (D : X →L[ℂ] X) (B : Y →L[ℂ] Y) (f : X) (g : Y)
    (hf : Tendsto (fun n : ℕ => (residual D : X → X)^[n] f) atTop (𝓝 0))
    (hg : Tendsto (fun n : ℕ => (residual B : Y → Y)^[n] g) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (residual (D.prodMap B) : X × Y → X × Y)^[n] (f,g)) atTop (𝓝 0) := by
  simpa only [prod_residual_iterate] using hf.prodMk_nhds hg

#print axioms geometricSum_identity
#print axioms geometricSum_mem
#print axioms approximation_tendsto
#print axioms range_core
#print axioms prod_residual_iterate
#print axioms prod_residual_tendsto

end
end UnifiedTheory.Audit.KFCausalInvariantRangeCore
