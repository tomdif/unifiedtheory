/- Completed Bose-symmetric sectors and normalized finite-group averaging. -/
import UnifiedTheory.Audit.KFCausalParticlePermutations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicSectorProjection
noncomputable section
open KFCausalClosedGraphForm KFCausalTensorParticleSectors KFCausalParticlePureTensors
open KFCausalParticlePermutations

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def invariant (D : Data H K) (n : ℕ) : Submodule ℂ (nonemptySector D n).State where
  carrier := {x | ∀ σ, action D n σ x = x}
  zero_mem' := by intro σ; simp
  add_mem' := by intro x y hx hy σ; rw [map_add, hx σ, hy σ]
  smul_mem' := by intro c x hx σ; rw [map_smul, hx σ]

theorem invariant_closed (D : Data H K) (n : ℕ) :
    IsClosed (invariant D n : Set (nonemptySector D n).State) := by
  change IsClosed {x | ∀ σ, action D n σ x = x}
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun σ => isClosed_eq (action D n σ).continuous continuous_id)

instance invariantComplete (D : Data H K) (n : ℕ) : CompleteSpace (invariant D n) :=
  (invariant_closed D n).completeSpace_coe

def average (D : Data H K) (n : ℕ) :
    (nonemptySector D n).State →L[ℂ] (nonemptySector D n).State :=
  (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin (n + 1)), (action D n σ).toContinuousLinearEquiv.toContinuousLinearMap

theorem average_apply (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    average D n x = (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin (n + 1)), action D n σ x := by
  simp only [average, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  rfl

theorem average_fixed (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    average D n x ∈ invariant D n := by
  intro τ
  rw [average_apply, map_smul, map_sum]
  congr 1
  simp_rw [← action_mul]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => action D n σ x)

def projection (D : Data H K) (n : ℕ) : (nonemptySector D n).State →L[ℂ] invariant D n :=
  (average D n).codRestrict (invariant D n) (average_fixed D n)

theorem average_on_invariant (D : Data H K) (n : ℕ) (x : invariant D n) :
    average D n (x : (nonemptySector D n).State) = x := by
  rw [average_apply]
  have hx (σ : Equiv.Perm (Fin (n + 1))) : action D n σ (x : (nonemptySector D n).State) = x :=
    x.property σ
  simp_rw [hx]
  have hc : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]

theorem projection_surjective (D : Data H K) (n : ℕ) : Function.Surjective (projection D n) := by
  intro x
  exact ⟨x, Subtype.ext (average_on_invariant D n x)⟩

theorem average_idempotent (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    average D n (average D n x) = average D n x :=
  average_on_invariant D n (projection D n x)

theorem symmetric_core_dense (D : Data H K) (n : ℕ) :
    DenseRange ((projection D n).toLinearMap.comp (embedding D n)) :=
  (projection_surjective D n).denseRange.comp (embedding_dense D n) (projection D n).continuous

end
end UnifiedTheory.Audit.KFCausalBosonicSectorProjection
