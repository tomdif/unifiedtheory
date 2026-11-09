/-
  The concrete nonzero-momentum tensor constraint symbol of the holomorphic
  spin parent, in real symmetric tensor coordinates xx,yy,zz,xy,yz,zx.

  Proves the two-dimensional kernel for every real nonzero wavevector,
  not only sampled momenta. The wave generator is the supplied canonical
  quadratic limit. A microscopic many-body/continuum limit remains separate.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTensorModeDynamics
noncomputable section
open Matrix
open scoped BigOperators

abbrev Tensor := Fin 6 → ℝ

def ell (x y z : ℝ) : ℝ := x^2 + y^2 + z^2
def tr (h : Tensor) : ℝ := h 0 + h 1 + h 2
def divergence (x y z : ℝ) (h : Tensor) : Fin 3 → ℝ :=
  ![x*h 0+y*h 3+z*h 5, x*h 3+y*h 1+z*h 4, x*h 5+y*h 4+z*h 2]
def scalarConstraint (x y z : ℝ) (h : Tensor) : ℝ :=
  x * divergence x y z h 0 + y * divergence x y z h 1 +
    z * divergence x y z h 2 - ell x y z * tr h

/-- Constraint operator G G* + B* B; adjoints use the Frobenius pairing. -/
def tensorPenalty (x y z : ℝ) (h : Tensor) : Tensor :=
  let d := divergence x y z h
  let b := scalarConstraint x y z h
  ![4*x*d 0+(x^2-ell x y z)*b,
    4*y*d 1+(y^2-ell x y z)*b,
    4*z*d 2+(z^2-ell x y z)*b,
    2*(x*d 1+y*d 0)+x*y*b,
    2*(y*d 2+z*d 1)+y*z*b,
    2*(z*d 0+x*d 2)+z*x*b]

def frobenius (h k : Tensor) : ℝ :=
  h 0*k 0+h 1*k 1+h 2*k 2+2*(h 3*k 3+h 4*k 4+h 5*k 5)

theorem penalty_energy_identity (x y z : ℝ) (h : Tensor) :
    frobenius h (tensorPenalty x y z h) =
      4*((divergence x y z h 0)^2+(divergence x y z h 1)^2+
        (divergence x y z h 2)^2) + (scalarConstraint x y z h)^2 := by
  simp [frobenius, tensorPenalty, divergence, scalarConstraint, ell, tr]
  ring

theorem ell_pos (x y z : ℝ) (hv : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < ell x y z := by
  rcases hv with hx | hy | hz <;> dsimp [ell]
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg z]
  · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_pos_of_ne_zero hz, sq_nonneg x, sq_nonneg y]

/-- The kernel is precisely transverse and tracefree at nonzero momentum. -/
theorem penalty_zero_iff (x y z : ℝ) (h : Tensor)
    (hv : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    tensorPenalty x y z h = 0 ↔ divergence x y z h = 0 ∧ tr h = 0 := by
  constructor
  · intro hk
    have he := penalty_energy_identity x y z h
    rw [hk] at he
    simp only [frobenius, Pi.zero_apply, mul_zero, add_zero] at he
    have hd0 : divergence x y z h 0 = 0 := by nlinarith [sq_nonneg (scalarConstraint x y z h), sq_nonneg (divergence x y z h 1), sq_nonneg (divergence x y z h 2)]
    have hd1 : divergence x y z h 1 = 0 := by nlinarith [sq_nonneg (scalarConstraint x y z h), sq_nonneg (divergence x y z h 0), sq_nonneg (divergence x y z h 2)]
    have hd2 : divergence x y z h 2 = 0 := by nlinarith [sq_nonneg (scalarConstraint x y z h), sq_nonneg (divergence x y z h 0), sq_nonneg (divergence x y z h 1)]
    have hb : scalarConstraint x y z h = 0 := by nlinarith
    constructor
    · ext i
      fin_cases i <;> assumption
    · have hp := ell_pos x y z hv
      simp only [scalarConstraint, hd0, hd1, hd2, mul_zero, add_zero, zero_sub] at hb
      exact (mul_eq_zero.mp (neg_eq_zero.mp hb)).resolve_left (ne_of_gt hp)
  · rintro ⟨hd, ht⟩
    have hb : scalarConstraint x y z h = 0 := by simp [scalarConstraint, hd, ht]
    ext i
    fin_cases i <;> simp [tensorPenalty, hd, hb]

/-- Transversality and trace as one concrete four-by-six matrix. -/
def constraintMatrix (x y z : ℝ) : Matrix (Fin 4) (Fin 6) ℝ :=
  !![x,0,0,y,0,z; 0,y,0,x,z,0; 0,0,z,0,y,x; 1,1,1,0,0,0]

def inverseFrobenius : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal ![1,1,1,1/2,1/2,1/2]

theorem constraintMatrix_apply (x y z : ℝ) (h : Tensor) :
    constraintMatrix x y z *ᵥ h =
      ![divergence x y z h 0, divergence x y z h 1, divergence x y z h 2, tr h] := by
  ext i
  fin_cases i <;> simp [constraintMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, divergence, tr] <;> ring

set_option maxHeartbeats 2000000 in
/-- The weighted Gram determinant is positive at every nonzero momentum. -/
theorem constraint_gram_det (x y z : ℝ) :
    ((constraintMatrix x y z * inverseFrobenius) * (constraintMatrix x y z)ᵀ).det =
      (ell x y z)^3 / 2 := by
  have hg : (constraintMatrix x y z * inverseFrobenius) * (constraintMatrix x y z)ᵀ =
      !![x^2+(y^2+z^2)/2, x*y/2, x*z/2, x;
         x*y/2, y^2+(x^2+z^2)/2, y*z/2, y;
         x*z/2, y*z/2, z^2+(x^2+y^2)/2, z;
         x, y, z, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, constraintMatrix, inverseFrobenius,
        Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring
  rw [hg]
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, ell]
  ring

theorem constraint_rank_four (x y z : ℝ) (hv : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    (constraintMatrix x y z).rank = 4 := by
  have hdet : IsUnit
      (((constraintMatrix x y z * inverseFrobenius) * (constraintMatrix x y z)ᵀ).det) := by
    rw [constraint_gram_det, isUnit_iff_ne_zero]
    exact ne_of_gt (div_pos (pow_pos (ell_pos x y z hv) 3) (by norm_num))
  have hr := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have hlow := (Matrix.rank_mul_le_left
    (constraintMatrix x y z * inverseFrobenius) (constraintMatrix x y z)ᵀ).trans
    (Matrix.rank_mul_le_left (constraintMatrix x y z) inverseFrobenius)
  have hu := Matrix.rank_le_card_height (constraintMatrix x y z)
  norm_num at hr hu
  omega

def tensorSector (x y z : ℝ) : Submodule ℝ Tensor :=
  LinearMap.ker (constraintMatrix x y z).mulVecLin

theorem mem_tensorSector_iff (x y z : ℝ) (h : Tensor) :
    h ∈ tensorSector x y z ↔ divergence x y z h = 0 ∧ tr h = 0 := by
  simp only [tensorSector, LinearMap.mem_ker, Matrix.mulVecLin_apply, constraintMatrix_apply]
  constructor
  · intro he
    constructor
    · ext i
      fin_cases i
      · simpa using congrFun he 0
      · simpa using congrFun he 1
      · simpa using congrFun he 2
    · simpa using congrFun he 3
  · rintro ⟨hd, ht⟩
    ext i
    fin_cases i <;> simp [hd, ht]

/-- Exactly two real tensor components survive for every nonzero symbol. -/
theorem tensorSector_finrank (x y z : ℝ) (hv : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    Module.finrank ℝ (tensorSector x y z) = 2 := by
  have h := (constraintMatrix x y z).mulVecLin.finrank_range_add_finrank_ker
  have hr := constraint_rank_four x y z hv
  change Module.finrank ℝ (LinearMap.range (constraintMatrix x y z).mulVecLin) = 4 at hr
  rw [hr] at h
  change 4 + Module.finrank ℝ (tensorSector x y z) = Module.finrank ℝ (Fin 6 → ℝ) at h
  rw [Module.finrank_pi] at h
  norm_num at h
  omega

/-- The zero symbol has six homogeneous channels, not two. -/
theorem homogeneous_penalty_zero (h : Tensor) : tensorPenalty 0 0 0 h = 0 := by
  ext i
  fin_cases i <;> simp [tensorPenalty, divergence, scalarConstraint, ell]

/-- Canonical wave equations of the specified slow quadratic Hamiltonian. -/
def waveFlow (U stiffness : ℝ) (state : Tensor × Tensor) : Tensor × Tensor :=
  (U • state.2, -stiffness • state.1)

theorem wave_preserves_tensor_sector (x y z U stiffness : ℝ) (q p : Tensor)
    (hq : q ∈ tensorSector x y z) (hp : p ∈ tensorSector x y z) :
    (waveFlow U stiffness (q,p)).1 ∈ tensorSector x y z ∧
      (waveFlow U stiffness (q,p)).2 ∈ tensorSector x y z :=
  ⟨(tensorSector x y z).smul_mem U hp, (tensorSector x y z).smul_mem (-stiffness) hq⟩

theorem wave_second_derivative (U stiffness : ℝ) (state : Tensor × Tensor) :
    waveFlow U stiffness (waveFlow U stiffness state) = (-U*stiffness) • state := by
  apply Prod.ext <;> ext i <;> change _ = (-U*stiffness) * _
  · change U * (-stiffness * state.1 i) = _
    ring
  · change -stiffness * (U * state.2 i) = _
    ring

theorem positive_massless_frequency_squared (x y z U g : ℝ)
    (hv : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (hU : 0 < U) (hg : 0 < g) :
    0 < U * (g * ell x y z) := mul_pos hU (mul_pos hg (ell_pos x y z hv))

/-- The gravitational trace correction agrees with the positive kinetic term
    on tracefree momenta, but is indefinite before imposing constraints. -/
def dewittKinetic (p : Tensor) : ℝ := frobenius p p - (tr p)^2/2

theorem dewitt_agrees_on_tensor_sector (x y z : ℝ) (p : Tensor)
    (hp : p ∈ tensorSector x y z) : dewittKinetic p = frobenius p p := by
  simp [dewittKinetic, ((mem_tensorSector_iff x y z p).mp hp).2]

theorem homogeneous_trace_kinetic (s : ℝ) :
    dewittKinetic ![s,s,s,0,0,0] = -(3/2)*s^2 := by
  simp [dewittKinetic, frobenius, tr]
  ring

/-- No strength of the existing zero-momentum penalty removes this negative
    quadratic direction. This concerns the unreduced quadratic Hamiltonian. -/
theorem homogeneous_penalty_cannot_stabilize_trace (penalty s : ℝ) :
    penalty * frobenius ![s,s,s,0,0,0] (tensorPenalty 0 0 0 ![s,s,s,0,0,0]) +
      dewittKinetic ![s,s,s,0,0,0] = -(3/2)*s^2 := by
  rw [homogeneous_penalty_zero, homogeneous_trace_kinetic]
  simp [frobenius]

#print axioms penalty_zero_iff
#print axioms constraint_rank_four
#print axioms tensorSector_finrank
#print axioms homogeneous_penalty_zero
#print axioms wave_preserves_tensor_sector
#print axioms wave_second_derivative
#print axioms homogeneous_penalty_cannot_stabilize_trace

end
end UnifiedTheory.Audit.KFCausalTensorModeDynamics
