/- The paired quadratic multiplier has a strictly negative transverse
coupling to the centered Gaussian for the actual nonzero imaginary clock
shift and unit quartic potential. This is an integral identity. It does
not assert completed-form membership of the quadratic excited state. -/
import UnifiedTheory.Audit.KFCausalChargedPairCoordinates
import UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalChargedPairTransverseCoupling
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (exponent)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargedPairCoordinates
open KFCausalQuarticPlaneDomination (potential)
open KFCausalNeutralPlaneMarginal (integral_head_product)

def transverseDensity (α β : ℝ) (r : ℂ) (q : Transverse) : ℝ :=
  pairPolynomial q * potential (pointField q) *
    ‖Complex.exp (exponent α β 0 r q)‖^2

def headDensity (α β : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  u 0*u 1*potential (u 4+fieldSlope r*u 2)*Real.exp (-quadratic α β r u)

def tailDensity (α β : ℝ) (r : ℂ) (u : Transverse) : ℝ :=
  ((u 2)^2-(u 3)^2)*potential (u 4+fieldSlope r*u 2)*
    Real.exp (-quadratic α β r u)

theorem density_reconstruct (α β : ℝ) (r : ℂ) (u : Transverse) :
    transverseDensity α β r (reconstruct r u) =
      headDensity α β r u-tailDensity α β r u/4 := by
  rw [transverseDensity,pair_reconstruct,field_reconstruct,gaussian_norm_reconstruct]
  unfold headDensity tailDensity
  ring

theorem gaussian_factorization (α β : ℝ) (r : ℂ) (u : Transverse) :
    Real.exp (-quadratic α β r u) =
      Real.exp (-(2*wideWidth α r)*(u 0)^2)*
        (Real.exp (-(2*wideWidth α r)*(u 1)^2)*
          KFCausalChargedPairIntegral.gaussian (narrowWidth α β r)
            (wideWidth α r) (2*β) ![u 2,u 3,u 4]) := by
  change Real.exp (-quadratic α β r u) =
    Real.exp (-(2*wideWidth α r)*(u 0)^2)*
      (Real.exp (-(2*wideWidth α r)*(u 1)^2)*
        Real.exp (-narrowWidth α β r*(u 2)^2-wideWidth α r*(u 3)^2-(2*β)*(u 4)^2))
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  unfold quadratic
  ring

theorem gaussian_weight (α β : ℝ) (r : ℂ) (u : Transverse) :
    Real.exp (-quadratic α β r u) =
      KFCausalPolynomialGaussianIntegrals.weight
        ![2*wideWidth α r,2*wideWidth α r,narrowWidth α β r,wideWidth α r,2*β] u := by
  simp only [KFCausalPolynomialGaussianIntegrals.weight,Fin.prod_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one,← Real.exp_add]
  congr 1
  change -quadratic α β r u =
    -(2*wideWidth α r)*(u 0)^2+
      (-(2*wideWidth α r)*(u 1)^2+
        (-narrowWidth α β r*(u 2)^2+(-wideWidth α r*(u 3)^2+-(2*β)*(u 4)^2)))
  unfold quadratic
  ring

private theorem polynomial_integrable (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β)
    (P : MvPolynomial (Fin 5) ℝ) :
    Integrable (fun u : Transverse =>
      MvPolynomial.eval u P*Real.exp (-quadratic α β r u)) volume := by
  simp_rw [gaussian_weight]
  apply KFCausalPolynomialGaussianIntegrals.polynomial_integrable
  intro i
  fin_cases i <;> dsimp <;> positivity

theorem head_integrable (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (headDensity α β r) volume := by
  let X := fun i : Fin 5 => (MvPolynomial.X i : MvPolynomial (Fin 5) ℝ)
  let V := X 4+MvPolynomial.C (fieldSlope r)*X 2
  let P := X 0*X 1*(1+MvPolynomial.C (1/2)*V^2+MvPolynomial.C (1/4)*V^4)
  convert polynomial_integrable α β r hA hB hβ P using 1
  funext u
  simp only [headDensity,potential,P,V,X,map_mul,map_add,map_one,
    map_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
  ring

theorem tail_integrable (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    Integrable (tailDensity α β r) volume := by
  let X := fun i : Fin 5 => (MvPolynomial.X i : MvPolynomial (Fin 5) ℝ)
  let V := X 4+MvPolynomial.C (fieldSlope r)*X 2
  let P := (X 2^2-X 3^2)*(1+MvPolynomial.C (1/2)*V^2+MvPolynomial.C (1/4)*V^4)
  convert polynomial_integrable α β r hA hB hβ P using 1
  funext u
  simp only [tailDensity,potential,P,V,X,map_mul,map_sub,map_add,map_one,
    map_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
  ring

theorem first_moment_zero (B : ℝ) :
    (∫ x : ℝ, x*Real.exp (-B*x^2)) = 0 := by
  have hn := integral_neg_eq_self (fun x : ℝ => x*Real.exp (-B*x^2)) volume
  simp only [neg_sq,neg_mul,integral_neg] at hn ⊢
  linarith

theorem head_integral_zero (α β : ℝ) (r : ℂ) :
    (∫ u, headDensity α β r u) = 0 := by
  have he : headDensity α β r = fun u : Fin (4+1) → ℝ =>
      (u 0*Real.exp (-(2*wideWidth α r)*(u 0)^2))*
      (fun v : Fin 4 → ℝ => v 0*Real.exp (-(2*wideWidth α r)*(v 0)^2)*
        potential (v 3+fieldSlope r*v 1)*
        KFCausalChargedPairIntegral.gaussian (narrowWidth α β r)
          (wideWidth α r) (2*β) ![v 1,v 2,v 3]) (fun i => u i.succ) := by
    funext u
    rw [headDensity,gaussian_factorization]
    change u 0*u 1*potential (u 4+fieldSlope r*u 2)*
      (Real.exp (-(2*wideWidth α r)*(u 0)^2)*
        (Real.exp (-(2*wideWidth α r)*(u 1)^2)*
          KFCausalChargedPairIntegral.gaussian (narrowWidth α β r)
            (wideWidth α r) (2*β) ![u 2,u 3,u 4])) = _
    dsimp
    ring
  rw [he,integral_head_product 4
    (fun x => x*Real.exp (-(2*wideWidth α r)*x^2))
    (fun v => v 0*Real.exp (-(2*wideWidth α r)*(v 0)^2)*
        potential (v 3+fieldSlope r*v 1)*
        KFCausalChargedPairIntegral.gaussian (narrowWidth α β r)
          (wideWidth α r) (2*β) ![v 1,v 2,v 3]),
    first_moment_zero,zero_mul]

theorem tail_integral (α β : ℝ) (r : ℂ) :
    (∫ u, tailDensity α β r u) =
      (Real.sqrt (Real.pi/(2*wideWidth α r)))^2 *
        ∫ v, KFCausalChargedPairIntegral.density (narrowWidth α β r)
          (wideWidth α r) (2*β) (fieldSlope r) v := by
  have he : tailDensity α β r = fun u : Fin (4+1) → ℝ =>
      Real.exp (-(2*wideWidth α r)*(u 0)^2)*
      (fun v : Fin 4 → ℝ => Real.exp (-(2*wideWidth α r)*(v 0)^2)*
        KFCausalChargedPairIntegral.density (narrowWidth α β r)
          (wideWidth α r) (2*β) (fieldSlope r) ![v 1,v 2,v 3]) (fun i => u i.succ) := by
    funext u
    rw [tailDensity,gaussian_factorization]
    simp only [KFCausalChargedPairIntegral.density,Matrix.cons_val_zero]
    change _ = Real.exp (-(2*wideWidth α r)*(u 0)^2)*
      (Real.exp (-(2*wideWidth α r)*(u 1)^2)*
        (((u 2)^2-(u 3)^2)*potential (u 4+fieldSlope r*u 2)*
          KFCausalChargedPairIntegral.gaussian (narrowWidth α β r)
            (wideWidth α r) (2*β) ![u 2,u 3,u 4]))
    ring
  rw [he,integral_head_product 4
    (fun x => Real.exp (-(2*wideWidth α r)*x^2))
    (fun v => Real.exp (-(2*wideWidth α r)*(v 0)^2)*
        KFCausalChargedPairIntegral.density (narrowWidth α β r)
          (wideWidth α r) (2*β) (fieldSlope r) ![v 1,v 2,v 3]),
    integral_gaussian]
  have hvec (v : Fin 3 → ℝ) : ![v 0,v 1,v 2] = v := by
    funext i
    fin_cases i <;> rfl
  change _ * (∫ u : Fin (3+1) → ℝ, Real.exp (-(2*wideWidth α r)*(u 0)^2)*
    (fun v : Fin 3 → ℝ => KFCausalChargedPairIntegral.density (narrowWidth α β r)
      (wideWidth α r) (2*β) (fieldSlope r) ![v 0,v 1,v 2]) (fun i => u i.succ)) = _
  rw [integral_head_product 3 (fun x => Real.exp (-(2*wideWidth α r)*x^2))
    (fun v => KFCausalChargedPairIntegral.density (narrowWidth α β r)
      (wideWidth α r) (2*β) (fieldSlope r) ![v 0,v 1,v 2]),integral_gaussian]
  have hi : (∫ v : Fin 3 → ℝ, KFCausalChargedPairIntegral.density (narrowWidth α β r)
      (wideWidth α r) (2*β) (fieldSlope r) ![v 0,v 1,v 2]) =
    ∫ v, KFCausalChargedPairIntegral.density (narrowWidth α β r)
      (wideWidth α r) (2*β) (fieldSlope r) v := by
    apply integral_congr_ae
    filter_upwards [] with v
    rw [hvec]
  rw [hi]
  ring

theorem transverse_integral (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    (∫ q, transverseDensity α β r q) =
      -(1/8:ℝ)*(Real.sqrt (Real.pi/(2*wideWidth α r)))^2 *
        ∫ v, KFCausalChargedPairIntegral.density (narrowWidth α β r)
          (wideWidth α r) (2*β) (fieldSlope r) v := by
  rw [integral_coordinates r]
  simp_rw [density_reconstruct]
  rw [integral_sub (head_integrable α β r hA hB hβ)
    ((tail_integrable α β r hA hB hβ).div_const 4),
    integral_div,head_integral_zero,tail_integral]
  ring

theorem transverse_integral_negative (α β : ℝ) (r : ℂ)
    (hA : 0 < narrowWidth α β r) (hβ : 0 < β) (hi : r.im ≠ 0) :
    (∫ q, transverseDensity α β r q) < 0 := by
  have hAB := widths_strict α β r hβ hi
  have hB := hA.trans hAB
  rw [transverse_integral α β r hA hB hβ]
  have hp := KFCausalChargedPairIntegral.integral_positive (narrowWidth α β r)
    (wideWidth α r) (2*β) (fieldSlope r) hA hAB (by positivity)
  have hs : 0 < (Real.sqrt (Real.pi/(2*wideWidth α r)))^2 := by positivity
  nlinarith [mul_pos hs hp]

theorem actual_transverse_integral_negative (α β ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    (∫ q, transverseDensity α β (KFCausalClockFloorRelativeShift.scale ε y s) q) < 0 := by
  exact transverse_integral_negative α β _
    (actual_narrowWidth_positive α β ε y s hα hβ.le hw hε hy hy0) hβ
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0)

#print axioms density_reconstruct
#print axioms gaussian_factorization
#print axioms gaussian_weight
#print axioms head_integrable
#print axioms tail_integrable
#print axioms first_moment_zero
#print axioms head_integral_zero
#print axioms tail_integral
#print axioms transverse_integral
#print axioms transverse_integral_negative
#print axioms actual_transverse_integral_negative
end
end UnifiedTheory.Audit.KFCausalChargedPairTransverseCoupling
