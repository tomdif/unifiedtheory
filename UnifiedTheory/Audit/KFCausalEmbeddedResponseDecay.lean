/- Transfer strong response decay through a pair of continuous embeddings
whose squared norms recover the form norm. -/
import UnifiedTheory.Audit.KFCausalInvariantRangeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEmbeddedResponseDecay
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)
variable {V H K : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K]

theorem intertwine (J : V →L[ℂ] H) (F : V →L[ℂ] V) (D : H →L[ℂ] H)
    (hJ : ∀ u, J (F u) = D (J u)) (u : V) : J (residual F u) = residual D (J u) := by
  change J (u-F u) = J u-D (J u)
  rw [map_sub,hJ]

theorem intertwine_iterate (J : V →L[ℂ] H) (F : V →L[ℂ] V) (D : H →L[ℂ] H)
    (hJ : ∀ u, J (F u) = D (J u)) (u : V) (n : ℕ) :
    J ((residual F : V → V)^[n] u) = (residual D : H → H)^[n] (J u) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',intertwine J F D hJ,ih,Function.iterate_succ_apply']

theorem residual_decay (J : V →L[ℂ] H) (A : V →L[ℂ] K)
    (F : V →L[ℂ] V) (D : H →L[ℂ] H) (R : K →L[ℂ] K) (a : ℝ)
    (hJ : ∀ u, J (F u) = D (J u)) (hA : ∀ u, A (F u) = R (A u))
    (hn : ∀ u, ‖u‖^2 = a*‖J u‖^2+‖A u‖^2)
    (hd : ∀ f, Tendsto (fun n : ℕ => (residual D : H → H)^[n] f) atTop (𝓝 0))
    (hr : ∀ g, Tendsto (fun n : ℕ => (residual R : K → K)^[n] g) atTop (𝓝 0)) (u : V) :
    Tendsto (fun n : ℕ => (residual F : V → V)^[n] u) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => ‖(residual F : V → V)^[n] u‖^2) atTop (𝓝 0) := by
    simp_rw [hn,intertwine_iterate J F D hJ,intertwine_iterate A F R hA]
    simpa using (((hd (J u)).norm.pow 2).const_mul a).add ((hr (A u)).norm.pow 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,sub_zero,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

theorem residual_norm (J : V →L[ℂ] H) (A : V →L[ℂ] K)
    (F : V →L[ℂ] V) (D : H →L[ℂ] H) (R : K →L[ℂ] K) (a : ℝ) (ha : 0 ≤ a)
    (hJ : ∀ u, J (F u) = D (J u)) (hA : ∀ u, A (F u) = R (A u))
    (hn : ∀ u, ‖u‖^2 = a*‖J u‖^2+‖A u‖^2)
    (hd : ∀ f, ‖residual D f‖ ≤ ‖f‖) (hr : ∀ g, ‖residual R g‖ ≤ ‖g‖) (u : V) :
    ‖residual F u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hn,hn,intertwine J F D hJ,intertwine A F R hA]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hd (J u)) 2) ha)
    (pow_le_pow_left₀ (norm_nonneg _) (hr (A u)) 2)

#print axioms intertwine
#print axioms intertwine_iterate
#print axioms residual_decay
#print axioms residual_norm
end
end UnifiedTheory.Audit.KFCausalEmbeddedResponseDecay
