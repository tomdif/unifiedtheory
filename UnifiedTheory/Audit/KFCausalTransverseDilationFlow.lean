/- Complete transverse dilation/shear flow associated with the quadratic
primitive's symmetrically ordered position-momentum expression. This is
an exact real coordinate flow, not a six-mode Hamiltonian domain theorem. -/
import UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseDilationFlow
noncomputable section

abbrev Transverse := Fin 5 → ℝ

def scale (t : ℝ) : ℝ := Real.exp (t/2)

theorem scale_add (t u : ℝ) : scale (t+u) = scale t*scale u := by
  simp only [scale,add_div,Real.exp_add]

theorem scale_zero : scale 0 = 1 := by simp [scale]

theorem scale_derivative (t : ℝ) : HasDerivAt scale (scale t/2) t := by
  convert ((hasDerivAt_id t).div_const 2).exp using 1
  simp [scale,div_eq_mul_inv]

def velocity (x : Transverse) (i : Fin 5) : ℝ := if i = 4 then x 2+x 3 else x i/2

def flow (t : ℝ) (x : Transverse) (i : Fin 5) : ℝ :=
  if i = 4 then x 4+2*(scale t-1)*(x 2+x 3) else scale t*x i

theorem flow_initial (x : Transverse) : flow 0 x = x := by
  funext i
  fin_cases i <;> simp [flow,scale_zero]

theorem flow_compose (t u : ℝ) (x : Transverse) : flow u (flow t x) = flow (t+u) x := by
  funext i
  fin_cases i <;> simp [flow,scale_add] <;> ring

theorem flow_reverse (t : ℝ) (x : Transverse) : flow (-t) (flow t x) = x := by
  rw [flow_compose,add_neg_cancel,flow_initial]

theorem flow_derivative (t : ℝ) (x : Transverse) :
    HasDerivAt (fun u => flow u x) (velocity (flow t x)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i = 4
  · subst i
    have hh := (((scale_derivative t).sub_const 1).const_mul 2 |>.mul_const (x 2+x 3)).const_add (x 4)
    convert hh using 1
    simp [flow,velocity]
    ring
  · have hh := (scale_derivative t).mul_const (x i)
    convert hh using 1
    · simp [flow,hi]
    · simp [flow,velocity,hi]
      ring

theorem flow_shear_invariant (t : ℝ) (x : Transverse) :
    flow t x 4-2*flow t x 2-2*flow t x 3 = x 4-2*x 2-2*x 3 := by
  simp only [flow,Fin.reduceEq,ite_true,ite_false]
  ring

def flowEquiv (t : ℝ) : Transverse ≃ₗ[ℝ] Transverse where
  toFun := flow t
  map_add' x y := by
    funext i
    fin_cases i <;> simp [flow] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [flow] <;> ring
  invFun := flow (-t)
  left_inv := flow_reverse t
  right_inv x := by simpa using flow_reverse (-t) x

theorem flow_bijective (t : ℝ) : Function.Bijective (flow t) := (flowEquiv t).bijective

def flowMatrix (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![scale t,0,0,0,0; 0,scale t,0,0,0; 0,0,scale t,0,0; 0,0,0,scale t,0;
     0,0,2*(scale t-1),2*(scale t-1),1]

theorem flowMatrix_apply (t : ℝ) (x : Transverse) : (flowMatrix t).mulVec x = flow t x := by
  funext i
  fin_cases i <;> simp [flowMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,flow]
  ring

theorem flowMatrix_det (t : ℝ) : (flowMatrix t).det = Real.exp (2*t) := by
  have ht : (flowMatrix t).BlockTriangular OrderDual.toDual := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [flowMatrix] at *
  rw [Matrix.det_of_lowerTriangular _ ht]
  norm_num [flowMatrix,Fin.prod_univ_succ]
  simp only [scale,← Real.exp_add]
  congr 1
  ring

#print axioms flow_compose
#print axioms flow_derivative
#print axioms flow_shear_invariant
#print axioms flow_bijective
#print axioms flowMatrix_apply
#print axioms flowMatrix_det

end
end UnifiedTheory.Audit.KFCausalTransverseDilationFlow
