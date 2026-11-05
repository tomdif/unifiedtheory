/- A concrete small SU(2) root distributes the central seam. Its total
squared displacement is at most pi squared times the linear period. -/
import UnifiedTheory.Clay.YangMills.WilsonDistributedSeam
import UnifiedTheory.Clay.YangMills.SU2WilsonAlignedRealization
import UnifiedTheory.Clay.YangMills.WilsonJointRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamRoot
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonDistributedSeam
open SU2WilsonAlignedRealization (rotorUnit coe_rotorUnit rotorUnit_zero)
open SU2AlignedGaussianApproximation (rotor)
open SU2ConditionalInfluence (imaginaryUnit)
open scoped Quaternion

theorem rotor_add (s t : ℝ) : rotorUnit (s+t) = rotorUnit s * rotorUnit t := by
  apply Subtype.ext
  ext <;> simp [rotorUnit, rotor, imaginaryUnit, Real.cos_add, Real.sin_add]; ring

theorem rotor_pow (t : ℝ) (k : ℕ) : (rotorUnit t)^k = rotorUnit ((k : ℝ)*t) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, rotorUnit_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← rotor_add]
    congr 1
    push_cast
    ring

theorem rotor_pi : rotorUnit Real.pi = -1 := by
  apply Subtype.ext
  simp [rotorUnit, rotor, imaginaryUnit, Unitary.coe_neg]

variable (n : ℕ) [NeZero n]

def root : Q := rotorUnit (Real.pi / n)

theorem root_power : (root n)^n = -1 := by
  rw [root, rotor_pow, mul_div_cancel₀ Real.pi (by exact_mod_cast NeZero.ne n)]
  exact rotor_pi

omit [NeZero n] in
theorem root_distance : ‖(root n : ℍ)-1‖ ≤ Real.pi / n := by
  have hh := SU2ConditionalInfluence.rotating_staple_distance (Real.pi/n)
  simpa only [root, coe_rotorUnit, rotor, abs_of_nonneg (by positivity : 0 ≤ Real.pi/n)] using hh

theorem uniform_cost (i : Fin 3) (q : Q) :
    WilsonJointRotation.cost n (uniform n i q) = (n : ℝ)^3 * ‖(q : ℍ)-1‖^2 := by
  classical
  have hd (x : SpatialVertex n) (j : Fin 3) :
      ‖(uniform n i q (x,j) : ℍ)-1‖^2 = if j = i then ‖(q : ℍ)-1‖^2 else 0 := by
    by_cases hj : j = i <;> simp [uniform, hj]
  simp only [WilsonJointRotation.cost, WilsonJointRotation.displacement, Fintype.sum_prod_type]
  simp_rw [hd]
  simp [SpatialVertex]

theorem root_cost (i : Fin 3) :
    WilsonJointRotation.cost n (uniform n i (root n)) ≤ Real.pi^2 * n := by
  rw [uniform_cost]
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.pi/n)).mpr (root_distance n)
  have hs := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (n : ℝ)^3)
  apply hs.trans_eq
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

end
end UnifiedTheory.Clay.YangMills.WilsonSeamRoot
