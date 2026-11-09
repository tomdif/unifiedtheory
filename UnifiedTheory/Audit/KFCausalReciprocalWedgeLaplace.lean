/- The broad charged factor is an actual absolutely integrable Laplace
transform. Finite reciprocal interference becomes the squared norm of
one common Laplace sum, the algebraic input to the wedge representation. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeGeometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeLaplace
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalCrossGeometry (A B)
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalReciprocalWedgeGeometry (chart)

theorem laplace_integrable (b : ℂ) (hb : 0 < b.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-b*(y:ℂ))) (Set.Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hb) 0

theorem laplace_integral (b : ℂ) (hb : 0 < b.re) :
    (∫ y : ℝ in Set.Ioi 0, Complex.exp (-b*(y:ℂ))) = 1/b := by
  simpa only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq] using
    integral_exp_mul_complex_Ioi (a := -b) (by simpa using neg_neg_of_pos hb) 0

theorem broad_laplace (α w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) (r : ℂ)
    (hB : 0 < (B α w v r).re) :
    gaussianValue (A α w v r)^2 = (Real.pi:ℂ)*(w:ℂ)*(v:ℂ)*
      ∫ y : ℝ in Set.Ioi 0, Complex.exp (-conj (B α w v r)*(y:ℂ)) := by
  rw [KFCausalReciprocalWedgeGeometry.broad_factor α w v hw hv,
    laplace_integral _ (by simpa only [Complex.conj_re] using hB)]
  ring

def laplaceSum (n : ℕ) (w : Fin n → ℝ) (c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ i, c i*(w i:ℂ)*Complex.exp (-(w i:ℂ)*z)

theorem laplaceSum_norm (n : ℕ) (α x y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (r : ℂ) :
    ((‖laplaceSum n w c (chart α r x y)‖^2:ℝ):ℂ) =
      ∑ i, ∑ j, (conj (c i)*c j)*(w i:ℂ)*(w j:ℂ)*
        Complex.exp (-B α (w i) (w j) r*(x:ℂ)-conj (B α (w i) (w j) r)*(y:ℂ)) := by
  rw [Complex.ofReal_pow,← Complex.conj_mul']
  unfold laplaceSum
  simp only [map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← KFCausalReciprocalWedgeGeometry.mode_product α (w i) (w j) x y r]
  ring

#print axioms laplace_integrable
#print axioms laplace_integral
#print axioms broad_laplace
#print axioms laplaceSum_norm
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeLaplace
