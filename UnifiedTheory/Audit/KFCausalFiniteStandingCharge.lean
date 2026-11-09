/- The exact finite occupation charge rotates the standing-wave position
pairs with the same orientation as the constructed continuum circle action.
These identities hold at every capacity and for arbitrary radial weights;
no canonical commutator or infinite-capacity identification is assumed. -/
import UnifiedTheory.Audit.KFCausalSpinSourceIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFiniteStandingCharge
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity

variable {n : Type*}
local notation "M" => Matrix n n ℂ

theorem spatialDeriv_add (q : n → ℤ) (A B : M) :
    spatialDeriv q (A+B) = spatialDeriv q A + spatialDeriv q B := by
  ext i j
  simp [spatialDeriv, mul_add]

theorem spatialDeriv_sub (q : n → ℤ) (A B : M) :
    spatialDeriv q (A-B) = spatialDeriv q A - spatialDeriv q B := by
  ext i j
  simp [spatialDeriv, mul_sub]

theorem spatialDeriv_smul (q : n → ℤ) (z : ℂ) (A : M) :
    spatialDeriv q (z • A) = z • spatialDeriv q A := by
  ext i j
  simp [spatialDeriv]
  ring

theorem spatialDeriv_adjoint (q : n → ℤ) (A : M) :
    spatialDeriv q Aᴴ = (spatialDeriv q A)ᴴ := by
  ext i j
  simp [spatialDeriv, Matrix.conjTranspose_apply]
  ring

theorem spatialDeriv_charged (q : n → ℤ) (k : ℤ) (A : M) (hA : HasCharge q k A) :
    spatialDeriv q A = (Complex.I*(k:ℂ)) • A := by
  ext i j
  by_cases h : q i-q j=k
  · simp [spatialDeriv, h]
  · simp [spatialDeriv, hA i j h]

def cosineMode (c : ℝ) (A B : M) : M := (c:ℂ) • (A+B)
def sineMode (c : ℝ) (A B : M) : M := (-Complex.I*(c:ℂ)) • (A-B)
def cosinePosition (c : ℝ) (A B : M) : M := cosineMode c A B+(cosineMode c A B)ᴴ
def sinePosition (c : ℝ) (A B : M) : M := sineMode c A B+(sineMode c A B)ᴴ

theorem cosineMode_derivative (q : n → ℤ) (c : ℝ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    spatialDeriv q (cosineMode c A B) = sineMode c A B := by
  rw [cosineMode, spatialDeriv_smul, spatialDeriv_add,
    spatialDeriv_charged q (-1) A hA, spatialDeriv_charged q 1 B hB]
  ext i j
  simp [sineMode]
  ring

theorem sineMode_derivative (q : n → ℤ) (c : ℝ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    spatialDeriv q (sineMode c A B) = -cosineMode c A B := by
  rw [sineMode, spatialDeriv_smul, spatialDeriv_sub,
    spatialDeriv_charged q (-1) A hA, spatialDeriv_charged q 1 B hB]
  ext i j
  simp [cosineMode]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

theorem cosinePosition_derivative (q : n → ℤ) (c : ℝ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    spatialDeriv q (cosinePosition c A B) = sinePosition c A B := by
  rw [cosinePosition, spatialDeriv_add, spatialDeriv_adjoint,
    cosineMode_derivative q c A B hA hB]
  rfl

theorem sinePosition_derivative (q : n → ℤ) (c : ℝ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    spatialDeriv q (sinePosition c A B) = -cosinePosition c A B := by
  rw [sinePosition, spatialDeriv_add, spatialDeriv_adjoint,
    sineMode_derivative q c A B hA hB]
  simp [cosinePosition, add_comm]

theorem gravity_cosine_derivative (R : ℕ) (r : ℕ → ℝ) (c : ℝ) :
    spatialDeriv (charge (R := R)) (cosinePosition c (ladder r 1) (ladder r 2)) =
      sinePosition c (ladder r 1) (ladder r 2) :=
  cosinePosition_derivative _ _ _ _
    (by simpa [flavorCharge] using ladder_charge (R := R) r 1)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 2)

theorem gravity_sine_derivative (R : ℕ) (r : ℕ → ℝ) (c : ℝ) :
    spatialDeriv (charge (R := R)) (sinePosition c (ladder r 1) (ladder r 2)) =
      -cosinePosition c (ladder r 1) (ladder r 2) :=
  sinePosition_derivative _ _ _ _
    (by simpa [flavorCharge] using ladder_charge (R := R) r 1)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 2)

theorem matter_cosine_derivative (R : ℕ) (r : ℕ → ℝ) (c : ℝ) :
    spatialDeriv (charge (R := R)) (cosinePosition c (ladder r 3) (ladder r 4)) =
      sinePosition c (ladder r 3) (ladder r 4) :=
  cosinePosition_derivative _ _ _ _
    (by simpa [flavorCharge] using ladder_charge (R := R) r 3)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 4)

theorem matter_sine_derivative (R : ℕ) (r : ℕ → ℝ) (c : ℝ) :
    spatialDeriv (charge (R := R)) (sinePosition c (ladder r 3) (ladder r 4)) =
      -cosinePosition c (ladder r 3) (ladder r 4) :=
  sinePosition_derivative _ _ _ _
    (by simpa [flavorCharge] using ladder_charge (R := R) r 3)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 4)

#print axioms spatialDeriv_add
#print axioms spatialDeriv_sub
#print axioms spatialDeriv_smul
#print axioms spatialDeriv_adjoint
#print axioms spatialDeriv_charged
#print axioms cosineMode_derivative
#print axioms sineMode_derivative
#print axioms cosinePosition_derivative
#print axioms sinePosition_derivative
#print axioms gravity_cosine_derivative
#print axioms gravity_sine_derivative
#print axioms matter_cosine_derivative
#print axioms matter_sine_derivative

end
end UnifiedTheory.Audit.KFCausalFiniteStandingCharge
