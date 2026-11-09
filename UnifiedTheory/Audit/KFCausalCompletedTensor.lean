/- Completed Hilbert tensor products and density of algebraic dense cores. -/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCompletedTensor
noncomputable section
open scoped TensorProduct

variable (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Space := UniformSpace.Completion (H ⊗[ℂ] K)

def includeTensor : H ⊗[ℂ] K →ₗᵢ[ℂ] Space H K := UniformSpace.Completion.toComplₗᵢ

def pure (x : H) (y : K) : Space H K := includeTensor H K (x ⊗ₜ[ℂ] y)

theorem pure_inner (x x' : H) (y y' : K) :
    inner ℂ (pure H K x y) (pure H K x' y') = inner ℂ x x' * inner ℂ y y' := by
  rw [pure, pure, (includeTensor H K).inner_map_map, TensorProduct.inner_tmul]

def left (y : K) : H →L[ℂ] Space H K :=
  ((includeTensor H K).toLinearMap.comp ((TensorProduct.mk ℂ H K).flip y)).mkContinuous
    ‖y‖ (by intro x; simp [mul_comm])

def right (x : H) : K →L[ℂ] Space H K :=
  ((includeTensor H K).toLinearMap.comp (TensorProduct.mk ℂ H K x)).mkContinuous
    ‖x‖ (by intro y; simp)

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def coreEmbedding (I : V →ₗ[ℂ] H) (J : W →ₗ[ℂ] K) :
    V ⊗[ℂ] W →ₗ[ℂ] Space H K :=
  (includeTensor H K).toLinearMap.comp (TensorProduct.map I J)

theorem coreEmbedding_dense (I : V →ₗ[ℂ] H) (J : W →ₗ[ℂ] K)
    (hi : DenseRange I) (hj : DenseRange J) : DenseRange (coreEmbedding H K I J) := by
  let S := (coreEmbedding H K I J).range.topologicalClosure
  have hS : IsClosed (S : Set (Space H K)) :=
    (coreEmbedding H K I J).range.isClosed_topologicalClosure
  have hp (x : H) (y : K) : pure H K x y ∈ S := by
    refine hi.induction_on x (hS.preimage (left H K y).continuous) ?_
    intro v
    refine hj.induction_on y (hS.preimage (right H K (I v)).continuous) ?_
    intro w
    exact (coreEmbedding H K I J).range.le_topologicalClosure
      ⟨v ⊗ₜ[ℂ] w, rfl⟩
  have ha (x : H ⊗[ℂ] K) : includeTensor H K x ∈ S := by
    induction x using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | tmul x y => exact hp x y
    | add x y hx hy => simpa only [map_add] using S.add_mem hx hy
  intro z
  exact UniformSpace.Completion.denseRange_coe.induction_on z
    (coreEmbedding H K I J).range.isClosed_topologicalClosure ha

def swap : Space H H ≃ₗᵢ[ℂ] Space H H :=
  KFCausalDenseUnitaryExtension.extension (includeTensor H H).toLinearMap
    UniformSpace.Completion.denseRange_coe (TensorProduct.comm ℂ H H)
    (by intro x; simp)

theorem swap_include (x : H ⊗[ℂ] H) :
    swap H (includeTensor H H x) = includeTensor H H (TensorProduct.comm ℂ H H x) :=
  KFCausalDenseUnitaryExtension.extension_embedding _ _ _ _ x

theorem swap_pure (x y : H) : swap H (pure H H x y) = pure H H y x :=
  swap_include H (x ⊗ₜ[ℂ] y)

theorem swap_involutive : Function.Involutive (swap H) := by
  intro x
  refine UniformSpace.Completion.denseRange_coe.induction_on x
    (isClosed_eq ((swap H).continuous.comp (swap H).continuous) continuous_id) ?_
  intro u
  change swap H (swap H (includeTensor H H u)) = includeTensor H H u
  rw [swap_include, swap_include]
  congr 1
  exact (TensorProduct.comm ℂ H H).symm_apply_apply u

def symmetric : Submodule ℂ (Space H H) :=
  LinearMap.ker ((swap H).toLinearMap - LinearMap.id)

theorem mem_symmetric (x : Space H H) : x ∈ symmetric H ↔ swap H x = x := by
  simp [symmetric, sub_eq_zero]

theorem symmetric_closed : IsClosed (symmetric H : Set (Space H H)) := by
  have he : (symmetric H : Set (Space H H)) = {x | swap H x = x} := by
    ext x
    exact mem_symmetric H x
  rw [he]
  exact isClosed_eq (swap H).continuous continuous_id

instance symmetricComplete : CompleteSpace (symmetric H) := (symmetric_closed H).completeSpace_coe

def symmetrize : Space H H →L[ℂ] symmetric H :=
  (ContinuousLinearMap.id ℂ (Space H H) +
    (swap H).toContinuousLinearEquiv.toContinuousLinearMap).codRestrict (symmetric H) (by
      intro x
      rw [mem_symmetric]
      change swap H (x + swap H x) = x + swap H x
      rw [map_add, swap_involutive, add_comm])

theorem symmetrize_surjective : Function.Surjective (symmetrize H) := by
  intro x
  refine ⟨(2 : ℂ)⁻¹ • (x : Space H H), ?_⟩
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • (x : Space H H) + swap H ((2 : ℂ)⁻¹ • (x : Space H H)) = x
  rw [map_smul, (mem_symmetric H x).mp x.property, ← add_smul]
  norm_num

end
end UnifiedTheory.Audit.KFCausalCompletedTensor
