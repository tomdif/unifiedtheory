/-
  The finite-dimensional penalty inverse and kernel projector are constructed
  from the actual matrix spectral decomposition. No inverse supplier is
  postulated. These matrix identities provide the correction equation used
  by KFCausalFastPenaltyDynamics; uniform spectral gap estimates remain a
  separate problem for a growing spin family.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFinitePenaltyInverse
noncomputable section
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {D : Matrix n n ℝ}

def spectral (hD : D.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℝ := hD.cfc f

theorem spectral_mul (hD : D.IsHermitian) (f g : ℝ → ℝ) :
    spectral hD f * spectral hD g = spectral hD (fun x => f x*g x) := by
  unfold spectral Matrix.IsHermitian.cfc
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  rfl

theorem spectral_sub (hD : D.IsHermitian) (f g : ℝ → ℝ) :
    spectral hD f - spectral hD g = spectral hD (fun x => f x-g x) := by
  unfold spectral Matrix.IsHermitian.cfc
  rw [← map_sub, Matrix.diagonal_sub]
  rfl

theorem spectral_one (hD : D.IsHermitian) : spectral hD (fun _ => 1) = 1 := by
  simp [spectral, Matrix.IsHermitian.cfc, Function.comp_def]

theorem spectral_zero (hD : D.IsHermitian) : spectral hD (fun _ => 0) = 0 := by
  simp [spectral, Matrix.IsHermitian.cfc, Function.comp_def]

theorem spectral_id (hD : D.IsHermitian) : spectral hD (fun x => x) = D :=
  hD.spectral_theorem.symm

def kernelProjector (hD : D.IsHermitian) : Matrix n n ℝ :=
  spectral hD (fun x => if x = 0 then 1 else 0)

def penaltyInverse (hD : D.IsHermitian) : Matrix n n ℝ :=
  spectral hD (fun x => x⁻¹)

theorem penalty_inverse_identity (hD : D.IsHermitian) :
    D * penaltyInverse hD = 1-kernelProjector hD := by
  conv_lhs => lhs; rw [← spectral_id hD]
  rw [penaltyInverse, spectral_mul, ← spectral_one hD, kernelProjector, spectral_sub]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

theorem penalty_kernel_zero (hD : D.IsHermitian) : D * kernelProjector hD = 0 := by
  conv_lhs => lhs; rw [← spectral_id hD]
  rw [kernelProjector, spectral_mul, ← spectral_zero hD]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

theorem kernel_projector_idempotent (hD : D.IsHermitian) :
    kernelProjector hD * kernelProjector hD = kernelProjector hD := by
  rw [kernelProjector, spectral_mul]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

theorem inverse_kernel_zero (hD : D.IsHermitian) :
    penaltyInverse hD * kernelProjector hD = 0 := by
  rw [penaltyInverse, kernelProjector, spectral_mul, ← spectral_zero hD]
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

/-- The full leakage correction for the actual compression P S P, without
assuming that the slow term S preserves the penalty kernel. -/
theorem constructed_correction_equation (hD : D.IsHermitian) (S : Matrix n n ℝ) :
    D * (penaltyInverse hD * S * kernelProjector hD) =
      S * kernelProjector hD - kernelProjector hD * S * kernelProjector hD := by
  rw [← mul_assoc D, ← mul_assoc D, penalty_inverse_identity]
  noncomm_ring

/-- A strict gap of D on the complement is not needed for existence in
finite dimension; it is needed to make this inverse uniformly bounded. -/
theorem kernel_projector_exact_range (hD : D.IsHermitian) (x : n → ℝ) :
    D *ᵥ x = 0 ↔ kernelProjector hD *ᵥ x = x := by
  have hcomm : D * penaltyInverse hD = penaltyInverse hD * D := by
    conv_lhs => lhs; rw [← spectral_id hD]
    conv_rhs => rhs; rw [← spectral_id hD]
    rw [penaltyInverse, spectral_mul, spectral_mul]
    congr 1
    funext a
    ring
  constructor
  · intro hx
    have he := congrArg (fun A : Matrix n n ℝ => A *ᵥ x) (penalty_inverse_identity hD)
    dsimp only at he
    rw [hcomm, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
      Matrix.sub_mulVec, Matrix.one_mulVec] at he
    exact (sub_eq_zero.mp he.symm).symm
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, penalty_kernel_zero, Matrix.zero_mulVec]

#print axioms penalty_inverse_identity
#print axioms penalty_kernel_zero
#print axioms kernel_projector_idempotent
#print axioms inverse_kernel_zero
#print axioms constructed_correction_equation
#print axioms kernel_projector_exact_range

end
end UnifiedTheory.Audit.KFCausalFinitePenaltyInverse
