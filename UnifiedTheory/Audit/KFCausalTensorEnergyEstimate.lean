/- Tensorization of a lower energy bound, without an energy eigenbasis.
Only a finite-dimensional spectator subspace is used for each algebraic tensor. -/
import UnifiedTheory.Audit.KFCausalCompletedTensor
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTensorEnergyEstimate
noncomputable section
open scoped TensorProduct

variable {V W H K X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem norm_sum_tmul {ι : Type*} (s : Finset ι) (e : ι → W)
    (he : Orthonormal ℂ e) (f : ι → H) :
    ‖∑ i ∈ s, f i ⊗ₜ[ℂ] e i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  have hi : inner ℂ (∑ i ∈ s, f i ⊗ₜ[ℂ] e i) (∑ i ∈ s, f i ⊗ₜ[ℂ] e i) =
      ∑ i ∈ s, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    simp [TensorProduct.inner_tmul, orthonormal_iff_ite.mp he, hi]
  have hr := congrArg Complex.re hi
  have hs (y : H ⊗[ℂ] W) : (inner ℂ y y).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
  have ht (y : H) : (inner ℂ y y).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
  simpa only [Complex.re_sum, hs, ht] using hr

theorem finite_right_lower [FiniteDimensional ℂ W]
    (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (J : W →ₗᵢ[ℂ] X) (δ : ℝ)
    (hb : ∀ v, δ * ‖I v‖ ^ 2 ≤ ‖O v‖ ^ 2) (u : V ⊗[ℂ] W) :
    δ * ‖TensorProduct.map I J.toLinearMap u‖ ^ 2 ≤
      ‖TensorProduct.map O J.toLinearMap u‖ ^ 2 := by
  classical
  let e := stdOrthonormalBasis ℂ W
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right e.toBasis u
  have he : Orthonormal ℂ (fun i => J (e i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [J.inner_map_map]
    exact e.inner_eq_ite i j
  simp only [Finsupp.sum, map_sum, TensorProduct.map_tmul]
  change δ * ‖∑ i ∈ c.support, I (c i) ⊗ₜ[ℂ] J (e i)‖ ^ 2 ≤
    ‖∑ i ∈ c.support, O (c i) ⊗ₜ[ℂ] J (e i)‖ ^ 2
  rw [norm_sum_tmul _ _ he, norm_sum_tmul _ _ he, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hb (c i))

theorem right_lower (I : V →ₗ[ℂ] H) (O : V →ₗ[ℂ] K) (J : W →ₗᵢ[ℂ] X) (δ : ℝ)
    (hb : ∀ v, δ * ‖I v‖ ^ 2 ≤ ‖O v‖ ^ 2) (u : V ⊗[ℂ] W) :
    δ * ‖TensorProduct.map I J.toLinearMap u‖ ^ 2 ≤
      ‖TensorProduct.map O J.toLinearMap u‖ ^ 2 := by
  obtain ⟨V', W', iV, iW, hu⟩ :=
    TensorProduct.exists_finite_submodule_of_setFinite {u} (Set.finite_singleton u)
  obtain ⟨v, rfl⟩ := Set.singleton_subset_iff.mp hu
  have h := finite_right_lower (I.comp V'.subtype) (O.comp V'.subtype)
    (J.comp W'.subtypeₗᵢ) δ (fun v => hb (v : V)) v
  change δ * ‖TensorProduct.map I J.toLinearMap (TensorProduct.map V'.subtype W'.subtype v)‖ ^ 2 ≤
    ‖TensorProduct.map O J.toLinearMap (TensorProduct.map V'.subtype W'.subtype v)‖ ^ 2
  simpa only [TensorProduct.map_map] using h

theorem left_lower (J : V →ₗᵢ[ℂ] H) (I : W →ₗ[ℂ] X) (O : W →ₗ[ℂ] K) (δ : ℝ)
    (hb : ∀ v, δ * ‖I v‖ ^ 2 ≤ ‖O v‖ ^ 2) (u : V ⊗[ℂ] W) :
    δ * ‖TensorProduct.map J.toLinearMap I u‖ ^ 2 ≤
      ‖TensorProduct.map J.toLinearMap O u‖ ^ 2 := by
  have h := right_lower I O J δ hb (TensorProduct.comm ℂ V W u)
  simpa only [TensorProduct.map_comm, TensorProduct.norm_comm] using h

end
end UnifiedTheory.Audit.KFCausalTensorEnergyEstimate
