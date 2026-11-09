/- Exact Gamma(shape 3/2, rate 1) polynomial norms and differentiation.
These are normal-boundary polynomial identities, not global trace estimates. -/
import UnifiedTheory.Audit.KFCausalJointFourierBoundaryClockRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaForm
noncomputable section
open MeasureTheory Set

def weight (x : ℝ) : ℝ := Real.exp (-x)*x^((1:ℝ)/2)
def moment (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, ((k:ℝ)+3/2)
def normalPolynomial (z0 z1 z2 : ℂ) (x : ℝ) : ℂ :=
  z0+((x-3/2:ℝ):ℂ)*z1+((x^2-5*x+15/4:ℝ):ℂ)*z2
def gammaNorm (z0 z1 z2 : ℂ) : ℝ :=
  Complex.normSq z0+3/2*Complex.normSq z1+15/2*Complex.normSq z2
def gammaPair (z0 z1 z2 w0 w1 w2 : ℂ) : ℂ :=
  star z0*w0+(3/2:ℂ)*star z1*w1+(15/2:ℂ)*star z2*w2

private theorem moment_factor (n : ℕ) :
    Real.Gamma ((n:ℝ)+3/2) = moment n*Real.Gamma (3/2) := by
  induction n with
  | zero => simp [moment]
  | succ n ih =>
    rw [show ((n+1:ℕ):ℝ)+3/2 = ((n:ℝ)+3/2)+1 by push_cast; ring,
      Real.Gamma_add_one (by positivity : (n:ℝ)+3/2 ≠ 0),ih]
    simp only [moment,Finset.prod_range_succ]
    ring

private theorem moment_pointwise (n : ℕ) (x : ℝ) (hx : 0 < x) :
    weight x*x^n = Real.exp (-x)*x^(((n:ℝ)+3/2)-1) := by
  rw [show ((n:ℝ)+3/2)-1 = 1/2+(n:ℝ) by ring,
    Real.rpow_add hx,Real.rpow_natCast]
  unfold weight
  ring

theorem moment_integrable (n : ℕ) :
    IntegrableOn (fun x => weight x*x^n) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent (by positivity : 0 < (n:ℝ)+3/2)).congr_fun
    (fun x hx => (moment_pointwise n x hx).symm) measurableSet_Ioi

theorem moment_integral (n : ℕ) :
    ∫ x in Ioi (0:ℝ), weight x*x^n = moment n*Real.Gamma (3/2) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => rfl))]
  calc
    _ = ∫ x in Ioi (0:ℝ), Real.exp (-x)*x^(((n:ℝ)+3/2)-1) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => moment_pointwise n x hx)
    _ = Real.Gamma ((n:ℝ)+3/2) :=
      (Real.Gamma_eq_integral (by positivity : 0 < (n:ℝ)+3/2)).symm
    _ = _ := moment_factor n

theorem quartic_integrable (a0 a1 a2 a3 a4 : ℝ) :
    IntegrableOn (fun x => weight x*(a0+a1*x+a2*x^2+a3*x^3+a4*x^4)) (Ioi 0) := by
  have h := ((((moment_integrable 0).const_mul a0).add ((moment_integrable 1).const_mul a1)).add
    ((moment_integrable 2).const_mul a2)).add ((moment_integrable 3).const_mul a3)
  change Integrable _ (volume.restrict (Ioi 0))
  convert h.add ((moment_integrable 4).const_mul a4) using 1
  ext x
  dsimp only [Pi.add_apply]
  ring

theorem quartic_integral (a0 a1 a2 a3 a4 : ℝ) :
    ∫ x in Ioi (0:ℝ), weight x*(a0+a1*x+a2*x^2+a3*x^3+a4*x^4) =
      (a0+3/2*a1+15/4*a2+105/8*a3+945/16*a4)*Real.Gamma (3/2) := by
  have he : (fun x => weight x*(a0+a1*x+a2*x^2+a3*x^3+a4*x^4)) =
      (fun x => a0*(weight x*x^0)+a1*(weight x*x^1)+a2*(weight x*x^2)+
        a3*(weight x*x^3)+a4*(weight x*x^4)) := by funext x; ring
  rw [he]
  have h0 := (moment_integrable 0).const_mul a0
  have h1 := (moment_integrable 1).const_mul a1
  have h2 := (moment_integrable 2).const_mul a2
  have h3 := (moment_integrable 3).const_mul a3
  have h4 := (moment_integrable 4).const_mul a4
  rw [integral_add,integral_add,integral_add,integral_add]
  · simp only [integral_const_mul,moment_integral]
    norm_num [moment,Finset.prod_range_succ]
    ring
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 |
    exact h0.add h1 | exact (h0.add h1).add h2 | exact ((h0.add h1).add h2).add h3

theorem normalPolynomial_derivative (z0 z1 z2 : ℂ) (x : ℝ) :
    HasDerivAt (normalPolynomial z0 z1 z2)
      (normalPolynomial (z1-2*z2) (2*z2) 0 x) x := by
  have h1 := (((hasDerivAt_id x).sub_const (3/2:ℝ)).ofReal_comp).mul_const z1
  have h2 := (((((hasDerivAt_id x).pow 2).sub
      ((hasDerivAt_id x).const_mul 5)).add_const (15/4:ℝ)).ofReal_comp).mul_const z2
  convert ((hasDerivAt_const x z0).add h1).add h2 using 1
  simp only [normalPolynomial,id_eq]
  push_cast
  ring

theorem gammaNorm_nonneg (z0 z1 z2 : ℂ) : 0 ≤ gammaNorm z0 z1 z2 := by
  exact add_nonneg (add_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)))
    (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))

private theorem polynomial_norm_expansion (z0 z1 z2 : ℂ) (x : ℝ) :
    Complex.normSq (z0+(x:ℂ)*z1+(x:ℂ)^2*z2) =
      Complex.normSq z0+2*(star z0*z1).re*x+
      (Complex.normSq z1+2*(star z0*z2).re)*x^2+
      2*(star z1*z2).re*x^3+Complex.normSq z2*x^4 := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,pow_two]
  ring

private theorem normal_to_monomial (z0 z1 z2 : ℂ) (x : ℝ) :
    normalPolynomial z0 z1 z2 x =
      (z0-(3/2:ℂ)*z1+(15/4:ℂ)*z2)+(x:ℂ)*(z1-5*z2)+(x:ℂ)^2*z2 := by
  unfold normalPolynomial
  push_cast
  ring

theorem normal_norm_integrable (z0 z1 z2 : ℂ) :
    IntegrableOn (fun x => weight x*Complex.normSq (normalPolynomial z0 z1 z2 x)) (Ioi 0) := by
  simp_rw [normal_to_monomial,polynomial_norm_expansion]
  exact quartic_integrable _ _ _ _ _

theorem normal_norm_integral (z0 z1 z2 : ℂ) :
    ∫ x in Ioi (0:ℝ), weight x*Complex.normSq (normalPolynomial z0 z1 z2 x) =
      gammaNorm z0 z1 z2*Real.Gamma (3/2) := by
  simp_rw [normal_to_monomial,polynomial_norm_expansion]
  rw [quartic_integral]
  congr 1
  simp only [gammaNorm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.div_re,
    Complex.div_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  norm_num
  ring

private theorem normal_pair_polarization (z0 z1 z2 w0 w1 w2 : ℂ) (x : ℝ) :
    (star (normalPolynomial z0 z1 z2 x)*normalPolynomial w0 w1 w2 x).re =
      (Complex.normSq (normalPolynomial (z0+w0) (z1+w1) (z2+w2) x)-
        Complex.normSq (normalPolynomial z0 z1 z2 x)-
        Complex.normSq (normalPolynomial w0 w1 w2 x))/2 := by
  have he : normalPolynomial (z0+w0) (z1+w1) (z2+w2) x =
      normalPolynomial z0 z1 z2 x+normalPolynomial w0 w1 w2 x := by
    unfold normalPolynomial
    ring
  rw [he]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem normal_pair_integrable (z0 z1 z2 w0 w1 w2 : ℂ) :
    IntegrableOn (fun x => weight x*
      (star (normalPolynomial z0 z1 z2 x)*normalPolynomial w0 w1 w2 x).re) (Ioi 0) := by
  have h := (((normal_norm_integrable (z0+w0) (z1+w1) (z2+w2)).sub
    (normal_norm_integrable z0 z1 z2)).sub (normal_norm_integrable w0 w1 w2)).div_const 2
  change Integrable _ (volume.restrict (Ioi 0))
  convert h using 1
  ext x
  dsimp only [Pi.sub_apply]
  rw [normal_pair_polarization]
  ring

theorem normal_pair_integral (z0 z1 z2 w0 w1 w2 : ℂ) :
    ∫ x in Ioi (0:ℝ), weight x*
      (star (normalPolynomial z0 z1 z2 x)*normalPolynomial w0 w1 w2 x).re =
      (gammaPair z0 z1 z2 w0 w1 w2).re*Real.Gamma (3/2) := by
  have he : (fun x => weight x*
      (star (normalPolynomial z0 z1 z2 x)*normalPolynomial w0 w1 w2 x).re) =
      (fun x => (weight x*Complex.normSq (normalPolynomial (z0+w0) (z1+w1) (z2+w2) x)-
        weight x*Complex.normSq (normalPolynomial z0 z1 z2 x)-
        weight x*Complex.normSq (normalPolynomial w0 w1 w2 x))/2) := by
    funext x
    rw [normal_pair_polarization]
    ring
  rw [he,integral_div,integral_sub,integral_sub]
  · rw [normal_norm_integral,normal_norm_integral,normal_norm_integral]
    simp only [gammaNorm,gammaPair,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    norm_num
    ring
  all_goals first | exact normal_norm_integrable _ _ _ |
    exact (normal_norm_integrable _ _ _).sub (normal_norm_integrable _ _ _)

#print axioms moment_integrable
#print axioms moment_integral
#print axioms quartic_integrable
#print axioms quartic_integral
#print axioms normalPolynomial_derivative
#print axioms gammaNorm_nonneg
#print axioms normal_norm_integrable
#print axioms normal_norm_integral
#print axioms normal_pair_integrable
#print axioms normal_pair_integral
end
end UnifiedTheory.Audit.KFCausalJointFourierBoundaryGammaForm
