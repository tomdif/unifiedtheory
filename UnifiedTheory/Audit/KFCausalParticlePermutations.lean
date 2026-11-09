/- Unitary permutation actions on every completed finite particle sector. -/
import UnifiedTheory.Audit.KFCausalParticlePureTensors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalParticlePermutations
noncomputable section
open KFCausalClosedGraphForm KFCausalTensorParticleSectors KFCausalParticlePureTensors

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def tuplePerm (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (Fin (n + 1) → H) ≃ (Fin (n + 1) → H) where
  toFun v i := v (σ.symm i)
  invFun v i := v (σ i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp

def corePerm (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : Core D n ≃ₗ[ℂ] Core D n :=
  Finsupp.domLCongr (tuplePerm n σ)

theorem pure_inner_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v w : Fin (n + 1) → H) :
    inner ℂ (pureTuple D n (tuplePerm n σ v)) (pureTuple D n (tuplePerm n σ w)) =
      inner ℂ (pureTuple D n v) (pureTuple D n w) := by
  rw [pureTuple_inner, pureTuple_inner]
  exact Equiv.prod_comp σ.symm (fun i => inner ℂ (v i) (w i))

theorem core_inner_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (u v : Core D n) :
    inner ℂ (embedding D n (corePerm D n σ u)) (embedding D n (corePerm D n σ v)) =
      inner ℂ (embedding D n u) (embedding D n v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, inner_add_left, hu, hw]
  | single a c =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, inner_add_right, hv, hw]
    | single b d =>
      simp only [corePerm, Finsupp.domLCongr_single, embedding_single,
        inner_smul_left, inner_smul_right, pure_inner_permute]

theorem core_norm_permute (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (u : Core D n) : ‖embedding D n (corePerm D n σ u)‖ = ‖embedding D n u‖ := by
  have he := congrArg Complex.re (core_inner_permute D n σ u u)
  have hnorm (x : (nonemptySector D n).State) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) x
  simp only [hnorm] at he
  nlinarith [norm_nonneg (embedding D n (corePerm D n σ u)), norm_nonneg (embedding D n u)]

def action (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (nonemptySector D n).State ≃ₗᵢ[ℂ] (nonemptySector D n).State :=
  KFCausalDenseUnitaryExtension.extension (embedding D n) (embedding_dense D n)
    (corePerm D n σ) (core_norm_permute D n σ)

theorem action_embedding (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (u : Core D n) :
    action D n σ (embedding D n u) = embedding D n (corePerm D n σ u) :=
  KFCausalDenseUnitaryExtension.extension_embedding _ _ _ _ u

theorem action_pure (D : Data H K) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (v : Fin (n + 1) → H) : action D n σ (pureTuple D n v) = pureTuple D n (tuplePerm n σ v) := by
  have he := action_embedding D n σ (Finsupp.single v 1)
  simpa only [corePerm, Finsupp.domLCongr_single, embedding_single, one_smul] using he

theorem action_one (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    action D n 1 x = x := by
  have he := linear_ext D n (action D n 1).toContinuousLinearEquiv.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ _) (by
      intro v
      change action D n 1 (pureTuple D n v) = pureTuple D n v
      rw [action_pure]
      rfl)
  exact congrArg (fun L => L x) he

theorem action_mul (D : Data H K) (n : ℕ) (σ τ : Equiv.Perm (Fin (n + 1)))
    (x : (nonemptySector D n).State) : action D n (σ * τ) x = action D n σ (action D n τ x) := by
  have he := linear_ext D n (action D n (σ * τ)).toContinuousLinearEquiv.toContinuousLinearMap
    ((action D n σ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (action D n τ).toContinuousLinearEquiv.toContinuousLinearMap) (by
      intro v
      change action D n (σ * τ) (pureTuple D n v) = action D n σ (action D n τ (pureTuple D n v))
      rw [action_pure, action_pure, action_pure]
      rfl)
  exact congrArg (fun L => L x) he

end
end UnifiedTheory.Audit.KFCausalParticlePermutations
