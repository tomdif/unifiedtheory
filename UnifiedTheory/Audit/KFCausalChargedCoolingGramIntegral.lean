/- The cooling kernel is the actual Gaussian/half-line Gram integral.
The polynomial factors at fixed v are absorbed into a finite coefficient
vector; no cross terms are discarded. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
import UnifiedTheory.Audit.KFCausalChargedFourierPolynomialGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (density)
open KFCausalChargedFourierPolynomialGram (Index width family)
open KFCausalShiftedComplexGaussianMoments (moment value mass)
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingDerivative (kernel form)

def planeMeasure : Measure (ℝ × ℝ) := volume.prod (volume.restrict (Set.Ioi 0))

theorem gaussianValue_split (S : ℂ) (hS : 0 < S.re) :
    gaussianValue S = (Real.sqrt Real.pi:ℂ)/S^(1/2:ℂ) := by
  have hn : S ≠ 0 := by intro hz; rw [hz] at hS; norm_num at hS
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : S.arg ≠ Real.pi := by
    have hb := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hS))).2
    linarith [Real.pi_pos]
  have hr : (Real.pi:ℂ)^(1/2:ℂ) = (Real.sqrt Real.pi:ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le,← Real.sqrt_eq_rpow]
  rw [← hr,gaussianValue,Complex.cpow_def_of_ne_zero (div_ne_zero hp hn),
    Complex.cpow_def_of_ne_zero hp,Complex.cpow_def_of_ne_zero hn,← Complex.exp_sub]
  congr 1
  rw [div_eq_mul_inv,Complex.log_ofReal_mul Real.pi_pos (inv_ne_zero hn),Complex.log_inv S ha,← Complex.ofReal_log Real.pi_pos.le]
  ring

theorem fixed_density_integrable (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (n : ℕ) (v : ℝ) :
    Integrable (fun q : ℝ × ℝ => density S T c n q.1 v q.2) planeMeasure :=
  ((KFCausalShiftedComplexGaussianMoments.moment_integrable S 0 hS 0).mul_const (moment S c n v)).mul_prod
    (KFCausalReciprocalWedgeLaplace.laplace_integrable T hT)

theorem fixed_density_integral (S T c : ℂ) (hS : 0 < S.re) (hT : 0 < T.re) (n : ℕ) (v : ℝ) :
    (∫ q : ℝ × ℝ, density S T c n q.1 v q.2 ∂planeMeasure) =
      (Real.sqrt Real.pi:ℂ)*(v:ℂ)^n*Complex.exp (-S*(v:ℂ)^2+c*(v:ℂ))/(S^(1/2:ℂ)*T) := by
  have hi := fixed_density_integrable S T c hS hT n v
  unfold planeMeasure at hi ⊢
  rw [integral_prod _ hi]
  unfold density
  simp_rw [integral_const_mul]
  rw [KFCausalReciprocalWedgeLaplace.laplace_integral T hT,integral_mul_const,integral_mul_const]
  change value S 0 0*moment S c n v*(1/T) = _
  rw [KFCausalShiftedComplexGaussianMoments.value_zero S 0 hS]
  simp only [mass,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,Complex.exp_zero,mul_one]
  rw [gaussianValue_split S hS]
  unfold moment
  ring

theorem width_kernel_identity (p : ℂ) (w z c v : ℝ) (n : ℕ) :
    (v:ℂ)^n*Complex.exp (-width p w z*(v:ℂ)^2+(c:ℂ)*(v:ℂ))/
      ((width p w z)^(1/2:ℂ)*conj (width p w z)) =
      (v:ℂ)^n*Complex.exp ((c:ℂ)*(v:ℂ))*kernel (conj p) w z v := by
  have hs : width p w z = widthSum (conj p) w z := by
    simp only [width,widthSum,starRingEnd_self_apply]
  have ht : conj (width p w z) = widthSum p w z := by
    simp only [width,widthSum,map_add,map_mul,starRingEnd_self_apply,Complex.conj_ofReal]
  rw [hs,show conj (widthSum (conj p) w z) = widthSum p w z from hs ▸ ht]
  unfold kernel
  simp only [starRingEnd_self_apply,Complex.ofReal_pow,Complex.exp_add]
  ring

def fixedCoefficients {n : ℕ} (a : Fin n → Fin 3 → ℂ) (c v : ℝ) (I : Index n) : ℂ :=
  a I.1 I.2*(v:ℂ)^I.2.val*Complex.exp ((c:ℂ)*(v:ℂ)/2)

theorem coefficient_product {n : ℕ} (a : Fin n → Fin 3 → ℂ) (c v : ℝ) (I J : Index n) :
    conj (fixedCoefficients a c v I)*fixedCoefficients a c v J =
      (conj (a I.1 I.2)*a J.1 J.2)*(v:ℂ)^(I.2.val+J.2.val)*Complex.exp ((c:ℂ)*(v:ℂ)) := by
  unfold fixedCoefficients
  simp only [map_mul,map_pow,← Complex.exp_conj,map_div₀,Complex.conj_ofReal,Complex.conj_ofNat,pow_add]
  have he : Complex.exp ((c:ℂ)*(v:ℂ)/2)*Complex.exp ((c:ℂ)*(v:ℂ)/2) =
      Complex.exp ((c:ℂ)*(v:ℂ)) := by rw [← Complex.exp_add]; congr 1; ring
  linear_combination (conj (a I.1 I.2)*a J.1 J.2*(v:ℂ)^I.2.val*(v:ℂ)^J.2.val)*he

variable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ) (a : Fin n → Fin 3 → ℂ)
  (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ)

include hp hw in
private theorem cross_integrable (I J : Index n) :
    Integrable (fun q : ℝ × ℝ => (conj (a I.1 I.2)*a J.1 J.2)*
      density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
        (c:ℂ) (I.2.val+J.2.val) q.1 v q.2) planeMeasure := by
  have hS := KFCausalChargedFourierPolynomialGram.width_positive p (w I.1) (w J.1) hp (hw _) (hw _)
  exact (fixed_density_integrable _ _ _ hS (by simpa only [Complex.conj_re] using hS) _ v).const_mul _

include hp hw in
theorem family_fixed_integrable :
    Integrable (fun q : ℝ × ℝ => ((‖family n p w c a q.1 v q.2‖^2:ℝ):ℂ)) planeMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun I _ =>
    integrable_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw v I J))
  exact hi.congr (Filter.Eventually.of_forall (fun q =>
    (KFCausalChargedFourierPolynomialGram.family_square_complex n p w c a q.1 v q.2).symm))

include hp hw in
theorem family_fixed_integral :
    (∫ q : ℝ × ℝ, ((‖family n p w c a q.1 v q.2‖^2:ℝ):ℂ) ∂planeMeasure) =
      (Real.sqrt Real.pi:ℂ)*form (conj p) (fun I : Index n => w I.1) v (fixedCoefficients a c v) := by
  simp_rw [KFCausalChargedFourierPolynomialGram.family_square_complex]
  rw [integral_finset_sum Finset.univ (fun I _ =>
    integrable_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw v I J))]
  simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,Complex.star_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [integral_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw v I J)]
  apply Finset.sum_congr rfl
  intro J _
  rw [integral_const_mul]
  have hS := KFCausalChargedFourierPolynomialGram.width_positive p (w I.1) (w J.1) hp (hw _) (hw _)
  rw [fixed_density_integral _ _ _ hS (by simpa only [Complex.conj_re] using hS)]
  have he := width_kernel_identity p (w I.1) (w J.1) c v (I.2.val+J.2.val)
  have hc := coefficient_product a c v I J
  linear_combination (Real.sqrt Real.pi:ℂ)*(conj (a I.1 I.2)*a J.1 J.2)*he-
    (Real.sqrt Real.pi:ℂ)*kernel (conj p) (w I.1) (w J.1) v*hc

#print axioms gaussianValue_split
#print axioms fixed_density_integrable
#print axioms fixed_density_integral
#print axioms width_kernel_identity
#print axioms coefficient_product
#print axioms family_fixed_integrable
#print axioms family_fixed_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
