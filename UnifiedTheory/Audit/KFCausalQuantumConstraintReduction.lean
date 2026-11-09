/-
  A finite reduced-quantization construction, in a simultaneous positive
  clock / integer translation-charge basis. A Jordan inverse reconstructs
  the local symmetrized constraint. Charge dephasing preserves positivity
  and the remaining zero-charge sector exactly.

  This is a specified operator constraint, not a derivation of an
  unreduced quantum gravitational constraint algebra or a continuum limit.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
noncomputable section
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n : Type*}
local notation "M" => Matrix n n ℂ

def jordan (c : n → ℝ) (A : M) : M := fun i j => ((c i+c j : ℝ) : ℂ)/2*A i j
def inverseJordan (c : n → ℝ) (A : M) : M := fun i j => 2/((c i+c j : ℝ) : ℂ)*A i j
def spatialDeriv (q : n → ℤ) (A : M) : M :=
  fun i j => Complex.I*((q i-q j : ℤ) : ℂ)*A i j
def meanPart (q : n → ℤ) (A : M) : M := fun i j => if q i=q j then A i j else 0
def primitive (q : n → ℤ) (A : M) : M :=
  fun i j => if q i=q j then 0 else A i j/(Complex.I*((q i-q j : ℤ) : ℂ))

theorem jordan_inverse (c : n → ℝ) (hc : ∀ i, 0 < c i) (A : M) :
    jordan c (inverseJordan c A)=A := by
  ext i j
  have hne : ((c i+c j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (add_pos (hc i) (hc j))
  push_cast at hne
  simp [jordan, inverseJordan]
  field_simp

theorem inverseJordan_hermitian (c : n → ℝ) (A : M) (hA : A.IsHermitian) :
    (inverseJordan c A).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  have he := congrFun (congrFun hA.eq i) j
  simp only [Matrix.conjTranspose_apply] at he
  simp [inverseJordan, Matrix.conjTranspose_apply, he, add_comm]

theorem spatialDeriv_primitive (q : n → ℤ) (A : M) :
    spatialDeriv q (primitive q A)=A-meanPart q A := by
  ext i j
  by_cases hq : q i=q j
  · simp [spatialDeriv, primitive, meanPart, hq]
  · have hn : ((q i-q j : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hq
    push_cast at hn
    simp [spatialDeriv, primitive, meanPart, hq]
    field_simp

theorem inverseJordan_spatialDeriv (c : n → ℝ) (q : n → ℤ) (A : M) :
    spatialDeriv q (inverseJordan c A)=inverseJordan c (spatialDeriv q A) := by
  ext i j
  simp only [spatialDeriv, inverseJordan]
  ring

theorem primitive_hermitian (q : n → ℤ) (A : M) (hA : A.IsHermitian) :
    (primitive q A).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  have he := congrFun (congrFun hA.eq i) j
  simp only [Matrix.conjTranspose_apply] at he
  by_cases hq : q i=q j
  · simp [primitive, Matrix.conjTranspose_apply, hq]
  · simp [primitive, Matrix.conjTranspose_apply, hq, Ne.symm hq, he]
    congr 1
    ring

def reconstructedL (c : n → ℝ) (q : n → ℤ) (base source : M) : M :=
  base+inverseJordan c (primitive q source)

/-- The operator constraint is source - (C L_x + L_x C)/2.
The homogeneous clock has no spatial derivative in this gauge. -/
theorem reconstructed_local_constraint (c : n → ℝ) (hc : ∀ i, 0 < c i)
    (q : n → ℤ) (base source : M) (hb : spatialDeriv q base=0) :
    source-jordan c (spatialDeriv q (reconstructedL c q base source))=meanPart q source := by
  have hadd (A B : M) : spatialDeriv q (A+B)=spatialDeriv q A+spatialDeriv q B := by
    ext i j; simp [spatialDeriv, mul_add]
  rw [reconstructedL, hadd, hb, zero_add, inverseJordan_spatialDeriv,
    jordan_inverse c hc, spatialDeriv_primitive]
  abel

variable [Fintype n] [DecidableEq n]

theorem jordan_is_anticommutator (c : n → ℝ) (A : M) :
    jordan c A = (1/2 : ℂ) •
      (Matrix.diagonal (fun i => (c i : ℂ))*A+A*Matrix.diagonal (fun i => (c i : ℂ))) := by
  ext i j
  simp [jordan, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem spatialDeriv_is_commutator (q : n → ℤ) (A : M) :
    spatialDeriv q A = Complex.I •
      (Matrix.diagonal (fun i => (q i : ℂ))*A-A*Matrix.diagonal (fun i => (q i : ℂ))) := by
  ext i j
  simp [spatialDeriv, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

def sector (q : n → ℤ) (k : ℤ) : M := Matrix.diagonal (fun i => if q i=k then 1 else 0)
def dephase (q : n → ℤ) (H : M) : M :=
  ∑ k ∈ Finset.univ.image q, (sector q k)ᴴ*H*sector q k

omit [Fintype n] in
theorem sector_hermitian (q : n → ℤ) (k : ℤ) : (sector q k).IsHermitian := by
  unfold Matrix.IsHermitian
  simp [sector]

theorem sector_idempotent (q : n → ℤ) (k : ℤ) : sector q k*sector q k=sector q k := by
  ext i j
  simp [sector, Matrix.diagonal_apply]
  aesop

theorem dephase_positive (q : n → ℤ) (H : M) (hH : H.PosSemidef) : (dephase q H).PosSemidef :=
  Matrix.posSemidef_sum _ (fun k _ => hH.conjTranspose_mul_mul_same (sector q k))

theorem dephase_eq_meanPart (q : n → ℤ) (H : M) : dephase q H=meanPart q H := by
  ext i j
  simp only [dephase, Matrix.sum_apply]
  rw [Finset.sum_eq_single (q i)]
  · simp [sector, Matrix.diagonal_mul, Matrix.mul_diagonal, meanPart, eq_comm]
  · intro k _ hki
    have hik : q i ≠ k := Ne.symm hki
    simp [sector, Matrix.diagonal_mul, Matrix.mul_diagonal, hik]
  · intro hn
    exact False.elim (hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

theorem dephase_commutes_sector (q : n → ℤ) (H : M) (k : ℤ) :
    Commute (dephase q H) (sector q k) := by
  change dephase q H*sector q k=sector q k*dephase q H
  rw [dephase_eq_meanPart]
  ext i j
  simp [sector, meanPart, Matrix.diagonal_mul, Matrix.mul_diagonal]
  split_ifs <;> simp_all

/-- Exact preservation by every frozen-time exponential, and hence by
products of such steps. This does not bound the time-discretization error. -/
theorem exponential_commutes_sector (q : n → ℤ) (H : M) (k : ℤ) (z : ℂ) :
    Commute (NormedSpace.exp (z • dephase q H)) (sector q k) := by
  letI : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M
  exact ((dephase_commutes_sector q H k).smul_left z).exp_left

theorem zero_sector_step (q : n → ℤ) (H : M) (z : ℂ) (v : n → ℂ)
    (hv : (sector q 0).mulVec v=v) :
    (sector q 0).mulVec ((NormedSpace.exp (z • dephase q H)).mulVec v)=
      (NormedSpace.exp (z • dephase q H)).mulVec v := by
  rw [Matrix.mulVec_mulVec, ← (exponential_commutes_sector q H 0 z).eq,
    ← Matrix.mulVec_mulVec, hv]

/-- In the spin construction the averaged source is a number-dependent
factor times translation charge. Identifying that source with the ladder
operators is checked separately, not assumed to be a CCR identity. -/
theorem charge_weighted_mean_annihilates_zero (q : n → ℤ) (g : n → ℂ) :
    Matrix.diagonal (fun i => g i*(q i : ℂ))*sector q 0=0 := by
  ext i j
  simp [sector, Matrix.diagonal_apply]
  aesop

theorem reconstructed_constraint_annihilates_physical_sector
    (c : n → ℝ) (hc : ∀ i, 0 < c i) (q : n → ℤ) (base source : M)
    (hb : spatialDeriv q base=0) (hs : meanPart q source*sector q 0=0) :
    (source-jordan c (spatialDeriv q (reconstructedL c q base source)))*sector q 0=0 := by
  rw [reconstructed_local_constraint c hc q base source hb, hs]

/-- Combines reconstruction with evolution: the specified local constraint
continues to annihilate a state after each exponential step. -/
theorem reconstructed_constraint_after_step
    (c : n → ℝ) (hc : ∀ i, 0 < c i) (q : n → ℤ) (base source H : M)
    (hb : spatialDeriv q base=0) (hs : meanPart q source*sector q 0=0)
    (z : ℂ) (v : n → ℂ) (hv : (sector q 0).mulVec v=v) :
    (source-jordan c (spatialDeriv q (reconstructedL c q base source))).mulVec
      ((NormedSpace.exp (z • dephase q H)).mulVec v)=0 := by
  have hcst := reconstructed_constraint_annihilates_physical_sector c hc q base source hb hs
  have hstep := zero_sector_step q H z v hv
  rw [← hstep, Matrix.mulVec_mulVec, hcst, Matrix.zero_mulVec]

#print axioms jordan_inverse
#print axioms inverseJordan_hermitian
#print axioms spatialDeriv_primitive
#print axioms inverseJordan_spatialDeriv
#print axioms primitive_hermitian
#print axioms reconstructed_local_constraint
#print axioms jordan_is_anticommutator
#print axioms spatialDeriv_is_commutator
#print axioms sector_idempotent
#print axioms dephase_positive
#print axioms dephase_eq_meanPart
#print axioms dephase_commutes_sector
#print axioms exponential_commutes_sector
#print axioms zero_sector_step
#print axioms charge_weighted_mean_annihilates_zero
#print axioms reconstructed_constraint_annihilates_physical_sector
#print axioms reconstructed_constraint_after_step

end
end UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
