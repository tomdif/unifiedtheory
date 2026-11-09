/- Exact Gaussian/half-line moments for the charged response. The
half-line boundary at zero and the limit at infinity are evaluated from
integrable functions and derivatives, not assumed to vanish. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
import UnifiedTheory.Audit.KFCausalJointPolynomialIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingResponseMoments
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology
open KFCausalChargedCoolingGramIntegral (planeMeasure gaussianValue_split)
open KFCausalComplexGaussianMoments (moment value gaussianValue)
open KFCausalReciprocalWedgeLaplace (laplace_integrable laplace_integral)

def laplaceMoment (T : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  (y:ℂ)^n*Complex.exp (-T*(y:ℂ))

def planeMoment (S T : ℂ) (m n : ℕ) (v : ℝ) (q : ℝ × ℝ) : ℂ :=
  moment S m q.1 * Complex.exp (-S*(v:ℂ)^2) * laplaceMoment T n q.2

def responseDensity (S T Sd Td : ℂ) (v : ℝ) (q : ℝ × ℝ) : ℂ :=
  -Sd*(planeMoment S T 2 0 v q+(v:ℂ)^2*planeMoment S T 0 0 v q)-
    Td*planeMoment S T 0 1 v q

theorem laplace_moment_integrable (T : ℂ) (hT : 0 < T.re) (n : ℕ) :
    Integrable (laplaceMoment T n) (volume.restrict (Set.Ioi 0)) := by
  have hi := (KFCausalJointPolynomialIntegrability.laplace_moment_integrable T.re hT n).norm
  apply hi.mono' (by unfold laplaceMoment; fun_prop)
  filter_upwards [] with y
  simp [laplaceMoment,norm_pow,Complex.norm_exp,Complex.mul_re]

theorem laplace_first_derivative (T : ℂ) (y : ℝ) :
    HasDerivAt (laplaceMoment T 1)
      (Complex.exp (-T*(y:ℂ))-T*laplaceMoment T 1 y) y := by
  have hd := (hasDerivAt_id y).ofReal_comp.mul
    (((hasDerivAt_id y).ofReal_comp.const_mul (-T)).cexp)
  convert hd using 1
  · funext x
    simp [laplaceMoment]
  · simp only [laplaceMoment,pow_one,id_eq,Complex.ofReal_one,mul_one,one_mul]
    ring

theorem laplace_first_integral (T : ℂ) (hT : 0 < T.re) :
    (∫ y : ℝ in Set.Ioi 0, laplaceMoment T 1 y) = 1/T^2 := by
  have hi := laplace_moment_integrable T hT 1
  have he := laplace_integrable T hT
  have hd : IntegrableOn (fun y : ℝ => Complex.exp (-T*(y:ℂ))-T*laplaceMoment T 1 y)
      (Set.Ioi 0) := he.sub (hi.const_mul T)
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := (0:ℝ)) (fun y _ => laplace_first_derivative T y) hd hi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0:ℝ)) (fun y _ => laplace_first_derivative T y) hd ht
  rw [integral_sub he (hi.const_mul T),integral_const_mul,laplace_integral T hT] at h
  simp only [laplaceMoment,pow_one,Complex.ofReal_zero,zero_mul,sub_zero] at h
  have hT0 : T ≠ 0 := by intro hz; rw [hz] at hT; exact lt_irrefl _ hT
  apply mul_left_cancel₀ hT0
  have hz : T*(∫ y : ℝ in Set.Ioi 0, laplaceMoment T 1 y) = 1/T := by
    simpa only [laplaceMoment,pow_one] using (sub_eq_zero.mp h).symm
  rw [hz]
  field_simp

theorem plane_moment_integrable (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re)
    (m n : ℕ) (v : ℝ) : Integrable (planeMoment S T m n v) planeMeasure :=
  ((KFCausalComplexGaussianMoments.moment_integrable S hS m).mul_const _).mul_prod
    (laplace_moment_integrable T hT n)

private theorem plane_moment_product (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re)
    (m n : ℕ) (v : ℝ) :
    (∫ q, planeMoment S T m n v q ∂planeMeasure) =
      value S m*Complex.exp (-S*(v:ℂ)^2)*(∫ y in Set.Ioi 0, laplaceMoment T n y) := by
  unfold planeMeasure
  rw [integral_prod _ (plane_moment_integrable S T hS hT m n v)]
  unfold planeMoment
  simp_rw [integral_const_mul]
  rw [integral_mul_const,integral_mul_const]
  rfl

theorem plane_moment_zero (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (v : ℝ) :
    (∫ q, planeMoment S T 0 0 v q ∂planeMeasure) =
      (Real.sqrt Real.pi:ℂ)*Complex.exp (-S*(v:ℂ)^2)/(S^(1/2:ℂ)*T) := by
  rw [plane_moment_product S T hS hT 0 0 v]
  simp only [laplaceMoment,pow_zero,one_mul]
  rw [laplace_integral T hT,KFCausalComplexGaussianMoments.value_zero S hS,
    gaussianValue_split S hS]
  ring

theorem plane_moment_gaussian (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (v : ℝ) :
    (∫ q, planeMoment S T 2 0 v q ∂planeMeasure) =
      (Real.sqrt Real.pi:ℂ)*Complex.exp (-S*(v:ℂ)^2)/(2*S*S^(1/2:ℂ)*T) := by
  rw [plane_moment_product S T hS hT 2 0 v]
  simp only [laplaceMoment,pow_zero,one_mul]
  rw [laplace_integral T hT,KFCausalComplexGaussianMoments.value_two S hS,
    gaussianValue_split S hS]
  ring

theorem plane_moment_laplace (S T : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (v : ℝ) :
    (∫ q, planeMoment S T 0 1 v q ∂planeMeasure) =
      (Real.sqrt Real.pi:ℂ)*Complex.exp (-S*(v:ℂ)^2)/(S^(1/2:ℂ)*T^2) := by
  rw [plane_moment_product S T hS hT 0 1 v]
  rw [laplace_first_integral T hT,KFCausalComplexGaussianMoments.value_zero S hS,
    gaussianValue_split S hS]
  ring

theorem response_density_integrable (S T Sd Td : ℂ) (hS : 0 < S.re) (hT : 0 < T.re)
    (v : ℝ) : Integrable (responseDensity S T Sd Td v) planeMeasure :=
  (((plane_moment_integrable S T hS hT 2 0 v).add
    ((plane_moment_integrable S T hS hT 0 0 v).const_mul ((v:ℂ)^2))).const_mul (-Sd)).sub
    ((plane_moment_integrable S T hS hT 0 1 v).const_mul Td)

theorem response_density_integral (S T Sd Td : ℂ) (hS : 0 < S.re) (hT : 0 < T.re)
    (v : ℝ) :
    (∫ q, responseDensity S T Sd Td v q ∂planeMeasure) =
      -(Real.sqrt Real.pi:ℂ)*Complex.exp (-S*(v:ℂ)^2)*
        ((v:ℂ)^2*Sd/(S^(1/2:ℂ)*T)+Sd/(2*S*S^(1/2:ℂ)*T)+Td/(S^(1/2:ℂ)*T^2)) := by
  unfold responseDensity
  have hiA : Integrable (fun q => -Sd*(planeMoment S T 2 0 v q+
      (v:ℂ)^2*planeMoment S T 0 0 v q)) planeMeasure :=
    ((plane_moment_integrable S T hS hT 2 0 v).add
      ((plane_moment_integrable S T hS hT 0 0 v).const_mul ((v:ℂ)^2))).const_mul (-Sd)
  have hiB : Integrable (fun q => Td*planeMoment S T 0 1 v q) planeMeasure :=
    (plane_moment_integrable S T hS hT 0 1 v).const_mul Td
  have hAdd := integral_add (plane_moment_integrable S T hS hT 2 0 v)
    ((plane_moment_integrable S T hS hT 0 0 v).const_mul ((v:ℂ)^2))
  rw [integral_sub hiA hiB,integral_const_mul,integral_const_mul,hAdd,
    integral_const_mul,plane_moment_zero S T hS hT v,
    plane_moment_gaussian S T hS hT v,plane_moment_laplace S T hS hT v]
  ring

#print axioms laplace_moment_integrable
#print axioms laplace_first_derivative
#print axioms laplace_first_integral
#print axioms plane_moment_integrable
#print axioms plane_moment_zero
#print axioms plane_moment_gaussian
#print axioms plane_moment_laplace
#print axioms response_density_integrable
#print axioms response_density_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingResponseMoments
