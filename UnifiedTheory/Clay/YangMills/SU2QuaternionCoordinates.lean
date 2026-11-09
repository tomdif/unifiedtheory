/- Explicit quaternion coordinates for the fundamental SU(2) representation.
Multiplication, star, determinant, trace, injectivity, and continuity are proved.
Unit quaternions map into the actual determinant-one matrix group. Surjectivity,
Haar transport, sphere-coordinate density, and Wilson source identification are
separate obligations and are not assumed or claimed in this module. -/
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2QuaternionCoordinates
noncomputable section
open Matrix

abbrev TwoMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- For `q = a + b i + c j + d k`, the matrix is
`[[a + b I, c + d I], [-c + d I, a - b I]]`. -/
def toMatrix (q : Quaternion ℝ) : TwoMatrix :=
  !![Complex.mk q.re q.imI, Complex.mk q.imJ q.imK;
     Complex.mk (-q.imJ) q.imK, Complex.mk q.re (-q.imI)]

@[simp] theorem toMatrix_zero : toMatrix 0 = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix]

@[simp] theorem toMatrix_one : toMatrix 1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix]

theorem toMatrix_add (p q : Quaternion ℝ) : toMatrix (p + q) = toMatrix p + toMatrix q := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix] <;> ring

/-- This coordinate map preserves the actual quaternion multiplication law. -/
theorem toMatrix_mul (p q : Quaternion ℝ) : toMatrix (p * q) = toMatrix p * toMatrix q := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_two, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem toMatrix_star (q : Quaternion ℝ) : toMatrix (star q) = star (toMatrix q) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [toMatrix, Matrix.star_apply]

theorem toMatrix_real (a : ℝ) : toMatrix (a : Quaternion ℝ) = (a : ℂ) • (1 : TwoMatrix) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [toMatrix]

/-- The unnormalized fundamental trace has the required factor of two. -/
theorem trace_toMatrix (q : Quaternion ℝ) : Matrix.trace (toMatrix q) = (2 * q.re : ℝ) := by
  apply Complex.ext
  · simp [toMatrix, Matrix.trace, Fin.sum_univ_two]
    ring
  · simp [toMatrix, Matrix.trace, Fin.sum_univ_two]

/-- The determinant is the quaternion norm squared. -/
theorem det_toMatrix (q : Quaternion ℝ) :
    Matrix.det (toMatrix q) = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Quaternion.normSq_def']
  apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im] <;>
    simp [toMatrix, Matrix.det_fin_two, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem realTrace_toMatrix (q : Quaternion ℝ) : (Matrix.trace (toMatrix q)).re = 2 * q.re := by
  rw [trace_toMatrix]
  rfl

theorem trace_im_toMatrix (q : Quaternion ℝ) : (Matrix.trace (toMatrix q)).im = 0 := by
  rw [trace_toMatrix]
  rfl

/-- The real trace pairing is exactly twice the Euclidean quaternion pairing. -/
theorem realTrace_toMatrix_mul_star (p q : Quaternion ℝ) :
    (Matrix.trace (toMatrix p * star (toMatrix q))).re = 2 * inner ℝ p q := by
  rw [← toMatrix_star, ← toMatrix_mul, realTrace_toMatrix, Quaternion.inner_def]

theorem toMatrix_continuous : Continuous toMatrix := by
  have hc (f g : Quaternion ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun q => Complex.mk (f q) (g q)) := by
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp hf).add
      ((Complex.continuous_ofReal.comp hg).mul continuous_const)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact hc _ _ Quaternion.continuous_re Quaternion.continuous_imI
  · exact hc _ _ Quaternion.continuous_imJ Quaternion.continuous_imK
  · exact hc _ _ Quaternion.continuous_imJ.neg Quaternion.continuous_imK
  · exact hc _ _ Quaternion.continuous_re Quaternion.continuous_imI.neg

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro p q h
  apply Quaternion.ext
  · simpa [toMatrix] using congrArg (fun M : TwoMatrix => (M 0 0).re) h
  · simpa [toMatrix] using congrArg (fun M : TwoMatrix => (M 0 0).im) h
  · simpa [toMatrix] using congrArg (fun M : TwoMatrix => (M 0 1).re) h
  · simpa [toMatrix] using congrArg (fun M : TwoMatrix => (M 0 1).im) h

theorem toMatrix_mul_star (q : Quaternion ℝ) :
    toMatrix q * star (toMatrix q) = ((Quaternion.normSq q : ℝ) : ℂ) • (1 : TwoMatrix) := by
  rw [← toMatrix_star, ← toMatrix_mul, Quaternion.self_mul_star, toMatrix_real]

theorem mem_specialUnitary_of_normSq_one (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    toMatrix q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_specialUnitaryGroup_iff.mpr
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    rw [toMatrix_mul_star, hq]
    simp
  · rw [det_toMatrix, hq]
    norm_num

theorem mem_specialUnitary_of_norm_one (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
    toMatrix q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  apply mem_specialUnitary_of_normSq_one
  rw [Quaternion.normSq_eq_norm_mul_self, hq]
  norm_num

/-- A constructed homomorphism into SU(2), without a surjectivity premise. -/
def unitaryToSpecialUnitary :
    unitary (Quaternion ℝ) →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun q := ⟨toMatrix q, mem_specialUnitary_of_normSq_one q (by
    rw [Quaternion.normSq_def, q.property.2]
    rfl)⟩
  map_one' := Subtype.ext toMatrix_one
  map_mul' p q := Subtype.ext (toMatrix_mul p q)

theorem unitaryToSpecialUnitary_injective : Function.Injective unitaryToSpecialUnitary := by
  intro p q h
  apply Subtype.ext
  exact toMatrix_injective (congrArg Subtype.val h)

theorem unitaryToSpecialUnitary_continuous : Continuous unitaryToSpecialUnitary :=
  (toMatrix_continuous.comp continuous_subtype_val).subtype_mk
    (fun q => (unitaryToSpecialUnitary q).property)


end
end UnifiedTheory.Clay.YangMills.SU2QuaternionCoordinates

