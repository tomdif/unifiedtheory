/- A discrete resolvent reflection kernel and its exact Hilbert-space quotient.
The kernel is constructed from a bounded symmetric operator, rather than assumed
to satisfy reflection positivity. This is a positive-time, two-point construction;
it does not assert a Euclidean field measure, spatial locality, or gauge dynamics.
The discrete transfer is R, not the continuous-time semigroup exp(-t H). -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalResolventReflectionKernel
noncomputable section
open scoped BigOperators InnerProduct

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev History (X : Type*) [Zero X] := ℕ →₀ X

/-- A finite positive-time history is sent to its propagated Hilbert vector. -/
def reconstruct (R : X →L[ℂ] X) : History X →ₗ[ℂ] X :=
  Finsupp.lsum ℂ (fun n => (R ^ n).toLinearMap)

theorem reconstruct_single (R : X →L[ℂ] X) (n : ℕ) (f : X) :
    reconstruct R (Finsupp.single n f) = (R ^ n) f :=
  Finsupp.lsum_single _ _ _ _

theorem reconstruct_surjective (R : X →L[ℂ] X) :
    Function.Surjective (reconstruct R) := by
  intro f
  refine ⟨Finsupp.single 0 f, ?_⟩
  simp [reconstruct_single]

def reflectionPairing (R : X →L[ℂ] X) (u v : History X) : ℂ :=
  u.sum (fun n f => v.sum (fun m g => inner ℂ f ((R ^ (n + m)) g)))

theorem power_pairing (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (n : ℕ) (x y : X) :
    inner ℂ ((R ^ n) x) y = inner ℂ x ((R ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply]
      rw [hs, ih]
      rw [← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ']
      rfl

theorem kernel_factorization (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (n m : ℕ) (f g : X) :
    inner ℂ f ((R ^ (n + m)) g) = inner ℂ ((R ^ n) f) ((R ^ m) g) := by
  rw [power_pairing R hs, pow_add, ContinuousLinearMap.mul_apply]

theorem pairing_reconstruction (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u v : History X) :
    reflectionPairing R u v = inner ℂ (reconstruct R u) (reconstruct R v) := by
  classical
  simp only [reflectionPairing, reconstruct, Finsupp.lsum_apply, Finsupp.sum,
    sum_inner, inner_sum, ContinuousLinearMap.coe_coe]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  exact kernel_factorization R hs n m (u n) (v m)

theorem reflection_positive (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u : History X) :
    0 ≤ (reflectionPairing R u u).re := by
  rw [pairing_reconstruction R hs]
  exact inner_self_nonneg (𝕜 := ℂ) (x := reconstruct R u)

theorem null_history_iff (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u : History X) :
    reflectionPairing R u u = 0 ↔ reconstruct R u = 0 := by
  rw [pairing_reconstruction R hs, inner_self_eq_zero]

/-- Quotient by exactly the zero-norm histories of the reflection pairing. -/
def Reconstructed (R : X →L[ℂ] X) := History X ⧸ LinearMap.ker (reconstruct R)

instance (R : X →L[ℂ] X) : AddCommGroup (Reconstructed R) :=
  inferInstanceAs (AddCommGroup (History X ⧸ LinearMap.ker (reconstruct R)))

instance (R : X →L[ℂ] X) : Module ℂ (Reconstructed R) :=
  inferInstanceAs (Module ℂ (History X ⧸ LinearMap.ker (reconstruct R)))

def reconstructionEquiv (R : X →L[ℂ] X) : Reconstructed R ≃ₗ[ℂ] X :=
  (reconstruct R).quotKerEquivOfSurjective (reconstruct_surjective R)

theorem reconstructionEquiv_mk (R : X →L[ℂ] X) (u : History X) :
    reconstructionEquiv R (Submodule.Quotient.mk u) = reconstruct R u :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

private def quotientCore (R : X →L[ℂ] X) : InnerProductSpace.Core ℂ (Reconstructed R) where
  inner x y := inner ℂ (reconstructionEquiv R x) (reconstructionEquiv R y)
  conj_inner_symm x y := inner_conj_symm _ _
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y c := by simp only [map_smul, inner_smul_left]
  definite x hx := (reconstructionEquiv R).injective (by
    simpa only [map_zero] using (inner_self_eq_zero.mp hx))

instance (R : X →L[ℂ] X) : NormedAddCommGroup (Reconstructed R) :=
  (quotientCore R).toNormedAddCommGroup

instance (R : X →L[ℂ] X) : InnerProductSpace ℂ (Reconstructed R) :=
  InnerProductSpace.ofCore { quotientCore R with }

def reconstructionIsometry (R : X →L[ℂ] X) : Reconstructed R ≃ₗᵢ[ℂ] X :=
  { reconstructionEquiv R with
    norm_map' := fun x => by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
      rfl }

theorem reconstruction_complete [CompleteSpace X] (R : X →L[ℂ] X) :
    CompleteSpace (Reconstructed R) :=
  (reconstructionIsometry R).toIsometryEquiv.completeSpace

theorem quotient_inner (R : X →L[ℂ] X)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (u v : History X) :
    @inner ℂ (Reconstructed R) _ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      reflectionPairing R u v := by
  change inner ℂ (reconstructionEquiv R (Submodule.Quotient.mk u))
    (reconstructionEquiv R (Submodule.Quotient.mk v)) = _
  rw [reconstructionEquiv_mk, reconstructionEquiv_mk, pairing_reconstruction R hs]

def shift : History X →ₗ[ℂ] History X := Finsupp.lmapDomain X ℂ Nat.succ

theorem shift_reconstruct (R : X →L[ℂ] X) (u : History X) :
    reconstruct R (shift u) = R (reconstruct R u) := by
  have he : (reconstruct R).comp shift = R.toLinearMap.comp (reconstruct R) := by
    apply Finsupp.lhom_ext
    intro n f
    simp [shift, reconstruct_single, pow_succ', ContinuousLinearMap.mul_apply]
  exact congrArg (fun L : History X →ₗ[ℂ] X => L u) he

theorem shift_preserves_null (R : X →L[ℂ] X) (u : History X)
    (hu : reconstruct R u = 0) : reconstruct R (shift u) = 0 := by
  rw [shift_reconstruct, hu, map_zero]

def transfer (R : X →L[ℂ] X) : Reconstructed R →L[ℂ] Reconstructed R :=
  (reconstructionIsometry R).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp (reconstructionIsometry R).toContinuousLinearEquiv.toContinuousLinearMap)

theorem transfer_intertwines (R : X →L[ℂ] X) (x : Reconstructed R) :
    reconstructionIsometry R (transfer R x) = R (reconstructionIsometry R x) := by
  simp [transfer]

theorem transfer_mk (R : X →L[ℂ] X) (u : History X) :
    transfer R (Submodule.Quotient.mk u) = Submodule.Quotient.mk (shift u) := by
  apply (reconstructionIsometry R).injective
  rw [transfer_intertwines]
  change R (reconstructionEquiv R (Submodule.Quotient.mk u)) =
    reconstructionEquiv R (Submodule.Quotient.mk (shift u))
  rw [reconstructionEquiv_mk, reconstructionEquiv_mk, shift_reconstruct]

theorem transfer_bound (R : X →L[ℂ] X) (q : ℝ) (hR : ∀ f, ‖R f‖ ≤ q * ‖f‖)
    (x : Reconstructed R) : ‖transfer R x‖ ≤ q * ‖x‖ := by
  rw [← (reconstructionIsometry R).norm_map (transfer R x), transfer_intertwines,
    ← (reconstructionIsometry R).norm_map x]
  exact hR _

end
end UnifiedTheory.Audit.KFCausalResolventReflectionKernel
