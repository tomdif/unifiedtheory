/-
  An explicit local unitary walk and its relativistic / chiral boundary.
  The three spatial axes and the update order are supplied model choices.
  This proves a finite-symbol construction, not gravity or Standard Model
  dynamics. The analytic continuum estimate is documented separately.
-/
import UnifiedTheory.Audit.KFCausalQuantumRefinement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeylWalk
noncomputable section
open Matrix
open scoped BigOperators

abbrev Spin := Matrix (Fin 2) (Fin 2) ℂ

/-- The real quaternion form c I - i(x X + y Y + z Z). -/
def quaternion (c x y z : ℝ) : Spin :=
  !![(c : ℂ) - z * Complex.I, -(y : ℂ) - x * Complex.I;
    (y : ℂ) - x * Complex.I, (c : ℂ) + z * Complex.I]

theorem quaternion_complete (c x y z : ℝ) (h : c ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (quaternion c x y z)ᴴ * quaternion c x y z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [quaternion, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> nlinarith

def rotateX (x : ℝ) : Spin := quaternion (Real.cos x) (Real.sin x) 0 0
def rotateY (y : ℝ) : Spin := quaternion (Real.cos y) 0 (Real.sin y) 0
def rotateZ (z : ℝ) : Spin := quaternion (Real.cos z) 0 0 (Real.sin z)

theorem rotateX_complete (x : ℝ) : (rotateX x)ᴴ * rotateX x = 1 := by
  apply quaternion_complete
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem rotateY_complete (y : ℝ) : (rotateY y)ᴴ * rotateY y = 1 := by
  apply quaternion_complete
  nlinarith [Real.sin_sq_add_cos_sq y]

theorem rotateZ_complete (z : ℝ) : (rotateZ z)ᴴ * rotateZ z = 1 := by
  apply quaternion_complete
  nlinarith [Real.sin_sq_add_cos_sq z]

private theorem unitary_mul (A B : Spin) (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  calc
    _ = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

def walk (x y z : ℝ) : Spin := rotateZ z * rotateY y * rotateX x

theorem walk_complete (x y z : ℝ) : (walk x y z)ᴴ * walk x y z = 1 :=
  unitary_mul _ _ (unitary_mul _ _ (rotateZ_complete z) (rotateY_complete y))
    (rotateX_complete x)

def scalar (x y z : ℝ) : ℝ :=
  Real.cos x * Real.cos y * Real.cos z + Real.sin x * Real.sin y * Real.sin z
def vectorX (x y z : ℝ) : ℝ :=
  Real.sin x * Real.cos y * Real.cos z - Real.cos x * Real.sin y * Real.sin z
def vectorY (x y z : ℝ) : ℝ :=
  Real.cos x * Real.sin y * Real.cos z + Real.sin x * Real.cos y * Real.sin z
def vectorZ (x y z : ℝ) : ℝ :=
  Real.cos x * Real.cos y * Real.sin z - Real.sin x * Real.sin y * Real.cos z

theorem walk_quaternion (x y z : ℝ) :
    walk x y z = quaternion (scalar x y z) (vectorX x y z)
      (vectorY x y z) (vectorZ x y z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [walk, rotateX, rotateY, rotateZ, quaternion, scalar, vectorX, vectorY, vectorZ,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem walk_zero : walk 0 0 0 = 1 := by
  rw [walk_quaternion]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quaternion, scalar, vectorX, vectorY, vectorZ, Matrix.one_apply]

/-- An exact second zero-quasienergy cone, with reversed y orientation. -/
theorem mirror_identity (x y z : ℝ) :
    walk (x + Real.pi/2) (y + Real.pi/2) (z + Real.pi/2) = walk x (-y) z := by
  rw [walk_quaternion, walk_quaternion]
  congr 1 <;>
    simp [scalar, vectorX, vectorY, vectorZ, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two] <;> ring

theorem mirror_node : walk (Real.pi/2) (Real.pi/2) (Real.pi/2) = 1 := by
  simpa [walk_zero] using mirror_identity 0 0 0

def hamiltonian (x y z : ℝ) : Spin :=
  !![(z : ℂ), (x : ℂ) - y * Complex.I;
    (x : ℂ) + y * Complex.I, -(z : ℂ)]

theorem hamiltonian_square (x y z : ℝ) :
    hamiltonian x y z * hamiltonian x y z = ((x^2+y^2+z^2 : ℝ) : ℂ) • (1 : Spin) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
      smul_eq_mul, pow_two] <;> ring

/-- First derivative of the actual update, entry by entry; no continuum
generator is supplied as a hypothesis. -/
theorem walk_generator (x y z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun a : ℝ => walk (a*x) (a*y) (a*z) i j)
      (-Complex.I * hamiltonian x y z i j) 0 := by
  have hc (k : ℝ) : HasDerivAt (fun a : ℝ => Real.cos (a*k)) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).cos
  have hs (k : ℝ) : HasDerivAt (fun a : ℝ => Real.sin (a*k)) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).sin
  have hd : HasDerivAt (fun a : ℝ => scalar (a*x) (a*y) (a*z)) 0 0 := by
    simpa [scalar] using (((hc x).mul (hc y)).mul (hc z)).add (((hs x).mul (hs y)).mul (hs z))
  have hx : HasDerivAt (fun a : ℝ => vectorX (a*x) (a*y) (a*z)) x 0 := by
    simpa [vectorX] using (((hs x).mul (hc y)).mul (hc z)).sub (((hc x).mul (hs y)).mul (hs z))
  have hy : HasDerivAt (fun a : ℝ => vectorY (a*x) (a*y) (a*z)) y 0 := by
    simpa [vectorY] using (((hc x).mul (hs y)).mul (hc z)).add (((hs x).mul (hc y)).mul (hs z))
  have hz : HasDerivAt (fun a : ℝ => vectorZ (a*x) (a*y) (a*z)) z 0 := by
    simpa [vectorZ] using (((hc x).mul (hc y)).mul (hs z)).sub (((hs x).mul (hs y)).mul (hc z))
  simp_rw [walk_quaternion]
  fin_cases i <;> fin_cases j
  · convert hd.ofReal_comp.sub (hz.ofReal_comp.mul_const Complex.I) using 1
    simp [hamiltonian]
    ring
  · convert hy.ofReal_comp.neg.sub (hx.ofReal_comp.mul_const Complex.I) using 1
    simp [hamiltonian]
    ring_nf
    simp [sub_eq_add_neg]
  · convert hy.ofReal_comp.sub (hx.ofReal_comp.mul_const Complex.I) using 1
    simp [hamiltonian]
    ring_nf
    simp
  · convert hd.ofReal_comp.add (hz.ofReal_comp.mul_const Complex.I) using 1
    simp [hamiltonian]
    ring

theorem mirror_generator (x y z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun a : ℝ =>
      walk (a*x + Real.pi/2) (a*y + Real.pi/2) (a*z + Real.pi/2) i j)
      (-Complex.I * hamiltonian x (-y) z i j) 0 := by
  simp_rw [mirror_identity, ← mul_neg]
  exact walk_generator x (-y) z i j

theorem mirror_orientation :
    Matrix.det (Matrix.diagonal (![1, -1, 1] : Fin 3 → ℝ)) = -1 := by
  norm_num [Matrix.det_diagonal, Fin.prod_univ_three]
  rfl

/-- Dimension-independent stability for repeated contractive updates.
For the walk the operator-norm one-step estimate is derived analytically
from the explicit rotations; it is not assumed to establish the generator. -/
theorem power_error {R : Type*} [NormedRing R] [NormOneClass R]
    (A B : R) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    ‖A^n - B^n‖ ≤ (n : ℝ) * ‖A-B‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ‖B^n‖ ≤ 1 :=
      (norm_pow_le B n).trans (pow_le_one₀ (norm_nonneg B) hB)
    calc
      ‖A^(n+1) - B^(n+1)‖ = ‖(A^n-B^n)*A + B^n*(A-B)‖ := by
        congr 1
        simp only [pow_succ]
        noncomm_ring
      _ ≤ ‖(A^n-B^n)*A‖ + ‖B^n*(A-B)‖ := norm_add_le _ _
      _ ≤ ‖A^n-B^n‖ * ‖A‖ + ‖B^n‖ * ‖A-B‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((n : ℝ) * ‖A-B‖) * 1 + 1 * ‖A-B‖ := by
        apply add_le_add
        · exact mul_le_mul ih hA (norm_nonneg A)
            (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))
        · exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = ((n+1 : ℕ) : ℝ) * ‖A-B‖ := by push_cast; ring

#print axioms quaternion_complete
#print axioms walk_complete
#print axioms walk_quaternion
#print axioms walk_generator
#print axioms hamiltonian_square
#print axioms mirror_identity
#print axioms mirror_node
#print axioms mirror_generator
#print axioms mirror_orientation
#print axioms power_error

end
end UnifiedTheory.Audit.KFCausalWeylWalk
