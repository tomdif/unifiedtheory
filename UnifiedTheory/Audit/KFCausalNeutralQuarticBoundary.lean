/- The boundary term in the quartic square completion has zero integral.
Polynomial L2 domains imply every integration-by-parts hypothesis; no
endpoint condition is assumed for the actual finite profile family. -/
import UnifiedTheory.Audit.KFCausalNeutralLineDomain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain
open KFCausalQuarticNeutralDefect
open KFCausalQuarticPlaneDomination (potential potentialSlope potential_positive)

theorem norm_square_derivative (f g : ℝ → ℂ) (x : ℝ) (hd : HasDerivAt f (g x) x) :
    HasDerivAt (fun t => ‖f t‖^2) (2*(conj (f x)*g x).re) x := by
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd.star.mul hd)
  convert he using 1
  · funext t
    change ‖f t‖^2 = (star (f t)*f t).re
    simp only [Complex.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  · change 2*(conj (f x)*g x).re = (star (g x)*f x+star (f x)*g x).re
    simp only [Complex.star_def,Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring

theorem boundary_integrable (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => boundaryDensity x (f x) (g x)) := by
  simpa only [boundaryDensity,mul_assoc] using
    (weight_norm_integrable f hf 2).add ((weight_re_integrable f g hf hg 1).const_mul 2)

theorem boundary_integral (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    (∫ x, boundaryDensity x (f x) (g x)) = 0 := by
  have hi1 : Integrable (fun x => potentialSlope x*(2*(conj (f x)*g x).re)) := by
    simpa only [mul_left_comm,mul_assoc] using (weight_re_integrable f g hf hg 1).const_mul 2
  have hi2 : Integrable (fun x => potentialSecond x*‖f x‖^2) := weight_norm_integrable f hf 2
  have hi0 : Integrable (fun x => potentialSlope x*‖f x‖^2) := weight_norm_integrable f hf 1
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    potentialSlope_derivative (fun x => norm_square_derivative f g x (hd x)) hi1 hi2 hi0
  have hi : Integrable (fun x => 2*potentialSlope x*(conj (f x)*g x).re) := by
    simpa only [mul_assoc] using (weight_re_integrable f g hf hg 1).const_mul 2
  unfold boundaryDensity
  rw [integral_add hi2 hi]
  have hh : (∫ x, 2*potentialSlope x*(conj (f x)*g x).re) =
      ∫ x, potentialSlope x*(2*(conj (f x)*g x).re) := by
    congr 1
    funext x
    ring
  rw [hh,he]
  ring

theorem first_integrable (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => firstDensity η L x (f x) (g x)) := by
  have hi := ((weight_norm_integrable f hf 1).const_mul L).sub
    ((weight_im_integrable f g hf hg 0).const_mul (2*η))
  simpa only [firstDensity,mul_assoc] using hi

theorem second_integrable (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => secondDensity η L x (f x) (g x)) := by
  have hi := (((weight_norm_integrable g hg 0).const_mul (4*η^2)).sub
    ((weight_im_integrable f g hf hg 1).const_mul (4*L*η))).add
    ((weight_norm_integrable f hf 2).const_mul (L^2-η^2))
  simpa only [secondDensity,mul_assoc] using hi

theorem connection_regular (f : ℝ → ℂ) (hf : Regular f) :
    Regular (fun x => (connection x:ℂ)*f x) := by
  have hc : Continuous (fun x => (connection x:ℂ)) := by
    unfold connection potentialSlope potential
    fun_prop (disch := intro x; exact mul_ne_zero (by norm_num) (potential_positive x).ne')
  intro P
  have hm : MemLp (fun x => (connection x:ℂ)*(P.eval (x:ℂ)*f x)) 2 volume := by
    apply (hf P).of_le (hc.aestronglyMeasurable.mul (hf P).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(connection x:ℂ)*(P.eval (x:ℂ)*f x)‖ ≤ ‖P.eval (x:ℂ)*f x‖
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (connection_bound x) (norm_nonneg _)).trans_eq (one_mul _)
  simpa only [mul_left_comm] using hm

theorem direction_regular (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Regular (fun x => direction η L x (f x) (g x)) := by
  have hi := regular_add _ _ (regular_const_mul g hg ((η:ℂ)*Complex.I))
    (regular_const_mul _ (connection_regular f hf) ((L:ℂ)+(η:ℂ)*Complex.I))
  simpa only [direction,mul_assoc] using hi

#print axioms norm_square_derivative
#print axioms boundary_integrable
#print axioms boundary_integral
#print axioms first_integrable
#print axioms second_integrable
#print axioms connection_regular
#print axioms direction_regular
end
end UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary
