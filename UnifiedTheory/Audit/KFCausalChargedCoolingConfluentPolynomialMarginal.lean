/- Actual quadratic charged-polynomial marginal. The complex translation is
arbitrary; all mixed moments and their Gaussian integrability are retained. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentMoments
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeDissipation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialMarginal
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingConfluentMoments
open KFCausalChargedCoolingConfluentThreeCoercivity (gram)

def translation (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,0,0; z,1,0; z^2,2*z,1]

def shiftedCross (s : ℝ) (p z : ℂ) (m n : Fin 3) (q : ℝ × ℝ) : ℂ :=
  (chargedCoordinate p q+z)^m.val*(chargedCoordinate (conj p) q+conj z)^n.val*
    Complex.exp (-(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ)))

theorem shifted_cross_expansion (s : ℝ) (p z : ℂ) (m n : Fin 3) (q : ℝ × ℝ) :
    shiftedCross s p z m n q =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (translation z m i*conj (translation z n j))*cross s p i j q := by
  fin_cases m <;> fin_cases n <;>
    norm_num [shiftedCross,cross,translation,Fin.sum_univ_three,map_mul,map_pow,map_ofNat,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem shifted_cross_integrable (s : ℝ) (hs : 0 < s) (p z : ℂ) (m n : Fin 3) :
    Integrable (shiftedCross s p z m n) planeMeasure := by
  change Integrable (fun q => shiftedCross s p z m n q) planeMeasure
  simp_rw [shifted_cross_expansion]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (cross_integrable s hs p i j).const_mul _))

theorem shifted_cross_integral (s x : ℝ) (hs : 0 < s) (z : ℂ) (m n : Fin 3) :
    (∫ q, shiftedCross s ((s:ℂ)*halfParameter x) z m n q ∂planeMeasure) =
      (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ))*
        (translation z*gram x*(translation z).conjTranspose) m n := by
  simp_rw [shifted_cross_expansion]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (cross_integrable s hs _ i j).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ => (cross_integrable s hs _ _ j).const_mul _),
    integral_const_mul,scaled_gram_integral s x hs]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,Fin.sum_univ_three]
  ring

def quadraticDensity (s : ℝ) (p z : ℂ) (q : ℝ × ℝ) : ℝ :=
  ‖chargedCoordinate p q+z‖^4*Real.exp (-s*(q.1^2+q.2))

theorem quadratic_density_complex (s : ℝ) (p z : ℂ) (q : ℝ × ℝ) :
    (quadraticDensity s p z q:ℂ) = shiftedCross s p z 2 2 q := by
  change (quadraticDensity s p z q:ℂ) =
    (chargedCoordinate p q+z)^2*(chargedCoordinate (conj p) q+conj z)^2*
      Complex.exp (-(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ)))
  have hn : ((‖chargedCoordinate p q+z‖^2:ℝ):ℂ) =
      (chargedCoordinate p q+z)*(chargedCoordinate (conj p) q+conj z) := by
    rw [Complex.sq_norm,← Complex.mul_conj]
    simp only [chargedCoordinate,map_add,map_mul,map_pow,Complex.conj_ofReal]
  rw [quadraticDensity,show ‖chargedCoordinate p q+z‖^4 = (‖chargedCoordinate p q+z‖^2)^2 by ring,
    Complex.ofReal_mul,Complex.ofReal_pow,hn,Complex.ofReal_exp]
  simp only [Complex.ofReal_neg,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_pow]
  ring

theorem quadratic_density_integrable (s : ℝ) (hs : 0 < s) (p z : ℂ) :
    Integrable (quadraticDensity s p z) planeMeasure := by
  have h := (shifted_cross_integrable s hs p z 2 2).re
  exact h.congr (Filter.Eventually.of_forall (fun q => by
    change (shiftedCross s p z 2 2 q).re = _
    rw [← quadratic_density_complex]
    rfl))

theorem quadratic_density_integral (s x : ℝ) (hs : 0 < s) (z : ℂ) :
    (∫ q, quadraticDensity s ((s:ℂ)*halfParameter x) z q ∂planeMeasure) =
      ((KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ))*
        (translation z*gram x*(translation z).conjTranspose) 2 2).re := by
  have h := shifted_cross_integral s x hs z 2 2
  rw [← h]
  change _ = RCLike.re (∫ q, shiftedCross s ((s:ℂ)*halfParameter x) z 2 2 q ∂planeMeasure)
  rw [← integral_re (shifted_cross_integrable s hs _ z 2 2)]
  apply integral_congr_ae
  filter_upwards [] with q
  change _ = (shiftedCross s _ z 2 2 q).re
  rw [← quadratic_density_complex]
  rfl

theorem charged_parameter_identity (α a b w : ℝ) (hA : a^2-b^2 ≠ 0) :
    (((α*(a^2-b^2)*w:ℝ):ℂ)*halfParameter (a*b/(a^2-b^2))) =
      (w:ℂ)*((α:ℂ)*((a:ℂ)+(b:ℂ)*Complex.I)^2/2) := by
  have hAc : (a:ℂ)^2-(b:ℂ)^2 ≠ 0 := by exact_mod_cast hA
  unfold halfParameter
  push_cast
  field_simp [hAc]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem sector_quadratic_integral (α a b w : ℝ) (hα : 0 < α) (hw : 0 < w)
    (hr : |b| < a) (z : ℂ) :
    (∫ q, quadraticDensity (α*(a^2-b^2)*w)
      ((w:ℂ)*((α:ℂ)*((a:ℂ)+(b:ℂ)*Complex.I)^2/2)) z q ∂planeMeasure) =
      ((KFCausalComplexGaussianMoments.gaussianValue ((α*(a^2-b^2)*w:ℝ):ℂ)/
        ((α*(a^2-b^2)*w:ℝ):ℂ))*
        (translation z*gram (a*b/(a^2-b^2))*(translation z).conjTranspose) 2 2).re := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hr
  have hA : 0 < a^2-b^2 := by nlinarith [sq_abs b,abs_nonneg b]
  rw [← charged_parameter_identity α a b w hA.ne']
  exact quadratic_density_integral _ _ (by positivity) z

#print axioms shifted_cross_expansion
#print axioms shifted_cross_integrable
#print axioms shifted_cross_integral
#print axioms quadratic_density_complex
#print axioms quadratic_density_integrable
#print axioms quadratic_density_integral
#print axioms charged_parameter_identity
#print axioms sector_quadratic_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialMarginal
