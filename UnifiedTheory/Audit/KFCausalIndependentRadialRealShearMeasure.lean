/- The real five-dimensional physical shear preserves Lebesgue measure.
The reciprocal Fourier dilations cancel the two position dilations;
the neutral shear contributes no determinant factor. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Block

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialRealShearMeasure
noncomputable section
open MeasureTheory
open KFCausalIndependentRadialTransverseMeasure (RealSpace)

def flow (σ s : ℝ) (x : RealSpace) : RealSpace :=
  ![Real.exp (-s/2)*x 0,Real.exp (-s/2)*x 1,
    Real.exp (s/2)*x 2,Real.exp (s/2)*x 3,
    x 4+2*σ*(Real.exp (s/2)-1)*x 3]

def matrix (σ s : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![Real.exp (-s/2),0,0,0,0;
     0,Real.exp (-s/2),0,0,0;
     0,0,Real.exp (s/2),0,0;
     0,0,0,Real.exp (s/2),0;
     0,0,0,2*σ*(Real.exp (s/2)-1),1]

theorem flow_matrix (σ s : ℝ) : flow σ s=Matrix.toLin' (matrix σ s) := by
  funext x i
  fin_cases i <;> simp [flow,matrix,Matrix.toLin'_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ]
  ring

theorem determinant_one (σ s : ℝ) : Matrix.det (matrix σ s)=1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    change Real.exp (-s/2)*(Real.exp (-s/2)*(Real.exp (s/2)*(Real.exp (s/2)*1)))=1
    rw [mul_one]
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [matrix]

theorem flow_inverse (σ s : ℝ) (x : RealSpace) : flow σ (-s) (flow σ s x)=x := by
  funext i
  fin_cases i <;> simp [flow,neg_div,Real.exp_neg,mul_assoc]
  field_simp
  ring

def homeomorph (σ s : ℝ) : RealSpace≃ₜRealSpace where
  toFun := flow σ s
  invFun := flow σ (-s)
  left_inv := flow_inverse σ s
  right_inv x := by simpa only [neg_neg] using flow_inverse σ (-s) x
  continuous_toFun := by rw [flow_matrix]; exact (Matrix.toLin' (matrix σ s)).continuous_of_finiteDimensional
  continuous_invFun := by rw [flow_matrix]; exact (Matrix.toLin' (matrix σ (-s))).continuous_of_finiteDimensional

theorem flow_preserving (σ s : ℝ) : MeasurePreserving (flow σ s) := by
  refine ⟨(homeomorph σ s).continuous.measurable,?_⟩
  rw [flow_matrix,Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by rw [determinant_one]; norm_num),determinant_one]
  simp

theorem complex_flow (σ s : ℝ) (x : RealSpace) :
    KFCausalComplexShearPerturbation.flow σ (s:ℂ) (WithLp.toLp 2 (fun i=>(x i:ℂ)))=
      WithLp.toLp 2 (fun i=>(flow σ s x i:ℂ)) := by
  ext i
  fin_cases i <;> simp [KFCausalComplexShearPerturbation.flow,flow,
    Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integrable_flow_iff (σ s : ℝ) (f : RealSpace→E) :
    Integrable (fun x=>f (flow σ s x)) ↔ Integrable f :=
  (flow_preserving σ s).integrable_comp_emb (homeomorph σ s).toMeasurableEquiv.measurableEmbedding

theorem integral_flow (σ s : ℝ) (f : RealSpace→E) :
    (∫x:RealSpace,f (flow σ s x))=∫x:RealSpace,f x :=
  (flow_preserving σ s).integral_comp (homeomorph σ s).toMeasurableEquiv.measurableEmbedding f

#print axioms flow_matrix
#print axioms determinant_one
#print axioms flow_inverse
#print axioms flow_preserving
#print axioms complex_flow
#print axioms integrable_flow_iff
#print axioms integral_flow
end
end UnifiedTheory.Audit.KFCausalIndependentRadialRealShearMeasure
