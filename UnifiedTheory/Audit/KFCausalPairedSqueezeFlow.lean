/- A paired transverse squeeze for the actual five-coordinate model.
The symmetric coordinates and neutral coordinate dilate together, while
the antisymmetric coordinates contract. This commutes with the coupled
longitudinal shear and scales the full field, including its neutral part.
These are coordinate identities, not an evolution or virial theorem. -/
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
import UnifiedTheory.Audit.KFCausalTransverseDilationFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def diagonal (a : ℝ) : ℝ := (Real.exp a + Real.exp (-a))/2
def offDiagonal (a : ℝ) : ℝ := (Real.exp a - Real.exp (-a))/2

def squeeze (a : ℝ) (x : Transverse) : Transverse :=
  ![diagonal a*x 0+offDiagonal a*x 1,
    offDiagonal a*x 0+diagonal a*x 1,
    diagonal a*x 2+offDiagonal a*x 3,
    offDiagonal a*x 2+diagonal a*x 3,Real.exp a*x 4]

theorem squeeze_initial (x : Transverse) : squeeze 0 x = x := by
  funext i
  fin_cases i <;> simp [squeeze,diagonal,offDiagonal]

theorem squeeze_compose (a b : ℝ) (x : Transverse) :
    squeeze b (squeeze a x) = squeeze (a+b) x := by
  funext i
  fin_cases i <;> simp [squeeze,diagonal,offDiagonal,Real.exp_add] <;> ring

theorem squeeze_reverse (a : ℝ) (x : Transverse) : squeeze (-a) (squeeze a x) = x := by
  rw [squeeze_compose,add_neg_cancel,squeeze_initial]

def squeezeEquiv (a : ℝ) : Transverse ≃ₗ[ℝ] Transverse where
  toFun := squeeze a
  map_add' x y := by
    funext i
    fin_cases i <;> simp [squeeze] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [squeeze] <;> ring
  invFun := squeeze (-a)
  left_inv := squeeze_reverse a
  right_inv x := by simpa using squeeze_reverse (-a) x

theorem squeeze_bijective (a : ℝ) : Function.Bijective (squeeze a) :=
  (squeezeEquiv a).bijective

theorem squeeze_shear (a t : ℝ) (x : Transverse) :
    squeeze a (flow t x) = flow t (squeeze a x) := by
  funext i
  fin_cases i <;> simp [squeeze,flow,diagonal,offDiagonal] <;> ring

theorem squeeze_directions (a : ℝ) (i : Fin 4) :
    squeeze a (modelDirections i) =
      (if i < 2 then Real.exp a else Real.exp (-a)) • modelDirections i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [squeeze,modelDirections,diagonal,offDiagonal,Fin.lt_def] <;> ring

theorem squeeze_field (a : ℝ) (x : Transverse) :
    pointField (squeeze a x) = Real.exp a * pointField x := by
  change (diagonal a*x 2+offDiagonal a*x 3) +
    (offDiagonal a*x 2+diagonal a*x 3) + Real.exp a*x 4 =
    Real.exp a*(x 2+x 3+x 4)
  unfold diagonal offDiagonal
  ring

def squeezeMatrix (a : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![diagonal a,offDiagonal a,0,0,0;
     offDiagonal a,diagonal a,0,0,0;
     0,0,diagonal a,offDiagonal a,0;
     0,0,offDiagonal a,diagonal a,0;
     0,0,0,0,Real.exp a]

theorem squeezeMatrix_apply (a : ℝ) (x : Transverse) :
    (squeezeMatrix a).mulVec x = squeeze a x := by
  funext i
  fin_cases i <;> simp [squeezeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,squeeze]

theorem squeezeMatrix_det (a : ℝ) : (squeezeMatrix a).det = Real.exp a := by
  have h : diagonal a ^ 2 - offDiagonal a ^ 2 = 1 := by
    have he : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    unfold diagonal offDiagonal
    nlinarith
  have hd : (squeezeMatrix a).det =
      (diagonal a ^ 2 - offDiagonal a ^ 2)^2 * Real.exp a := by
    simp [squeezeMatrix,Matrix.det_succ_row_zero,Fin.sum_univ_succ,
      Matrix.submatrix,Fin.succAbove]
    ring
  rw [hd,h]
  ring

#print axioms squeeze_initial
#print axioms squeeze_reverse
#print axioms squeeze_compose
#print axioms squeeze_bijective
#print axioms squeeze_shear
#print axioms squeeze_directions
#print axioms squeeze_field
#print axioms squeezeMatrix_apply
#print axioms squeezeMatrix_det

end
end UnifiedTheory.Audit.KFCausalPairedSqueezeFlow
