/- The charged polynomial limiting density is genuinely integrable for
every neutral exponential-polynomial profile. The proof expands the exact
physical density into polynomial Gaussian/Laplace factors. -/
import UnifiedTheory.Audit.KFCausalJointPolynomialIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredWidthDensityIntegrability
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredWidthProfiles (limitDensity)
open KFCausalReciprocalWedgeGeometry (chart gamma)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalJointPolynomialIntegrability (coordinates)

abbrev Poly := MvPolynomial (Fin 4) ℂ
def chargedPolynomial (α : ℝ) (r : ℂ) : Poly :=
  MvPolynomial.C (gamma α r)*(MvPolynomial.X 0^2+MvPolynomial.X 1^2)+
    MvPolynomial.C (conj (gamma α r))*MvPolynomial.X 3
def neutralPolynomial (r : ℂ) : Poly :=
  MvPolynomial.X 2+MvPolynomial.C (2*(r.im:ℂ)*Complex.I)*MvPolynomial.X 1
def fieldPolynomial (r : ℂ) : Poly :=
  MvPolynomial.X 2+MvPolynomial.C (fieldSlope r:ℂ)*MvPolynomial.X 1
def factorPolynomial (n k : ℕ) (α : ℝ) (r : ℂ) (P : Polynomial ℂ) : Poly :=
  fieldPolynomial r^k*chargedPolynomial α r^n*P.eval₂ MvPolynomial.C (neutralPolynomial r)
def weight (α β : ℝ) (r b : ℂ) : Joint → ℝ :=
  KFCausalJointPolynomialIntegrability.weight (α*area r) (α*area r-8*β*r.im^2)
    (2*β) (-4*b.im*r.im) (2*b.re)

theorem chargedPolynomial_eval (α : ℝ) (r : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (chargedPolynomial α r) =
      chart α r (p.1.1^2+(p.1.2 0)^2) p.2 := by
  simp [chargedPolynomial,coordinates,chart]

theorem neutralPolynomial_eval (r : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (neutralPolynomial r) = neutral r (p.1.2 0) (p.1.2 1) := by
  simp [neutralPolynomial,coordinates,neutral]

theorem fieldPolynomial_eval (r : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (fieldPolynomial r) = (p.1.2 1+fieldSlope r*p.1.2 0:ℝ) := by
  simp [fieldPolynomial,coordinates]

theorem substitutedPolynomial_eval (r : ℂ) (p : Joint) (P : Polynomial ℂ) :
    MvPolynomial.eval (coordinates p) (P.eval₂ MvPolynomial.C (neutralPolynomial r)) =
      P.eval (neutral r (p.1.2 0) (p.1.2 1)) := by
  simp only [Polynomial.eval₂_eq_sum,Polynomial.eval_eq_sum,Polynomial.sum,map_sum,map_mul,
    map_pow,MvPolynomial.eval_C,neutralPolynomial_eval]

theorem factorPolynomial_eval (n k : ℕ) (α : ℝ) (r : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (factorPolynomial n k α r P) =
      ((p.1.2 1+fieldSlope r*p.1.2 0:ℝ):ℂ)^k*
        (chart α r (p.1.1^2+(p.1.2 0)^2) p.2)^n*P.eval (neutral r (p.1.2 0) (p.1.2 1)) := by
  simp only [factorPolynomial,map_mul,map_pow,fieldPolynomial_eval,chargedPolynomial_eval,
    substitutedPolynomial_eval]

theorem exponential_weight (α β : ℝ) (r b : ℂ) (p : Joint) :
    KFCausalReciprocalNeutralLaplace.weight β r p*
      ‖Complex.exp (-chart α r (p.1.1^2+(p.1.2 0)^2) p.2)*
        Complex.exp (b*neutral r (p.1.2 0) (p.1.2 1))‖^2 =
      KFCausalQuarticPlaneDomination.potential (p.1.2 1+fieldSlope r*p.1.2 0)*weight α β r b p := by
  unfold KFCausalReciprocalNeutralLaplace.weight weight KFCausalJointPolynomialIntegrability.weight
  simp only [norm_mul,Complex.norm_exp,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  rw [Complex.neg_re,KFCausalReciprocalWedgeGeometry.chart_re]
  simp only [neutral,Complex.mul_re,Complex.add_re,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,
    Complex.im_ofNat]
  ring

theorem density_decomposition (n : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitDensity n α β r (exponentialProfile b 1 P) p =
      (‖MvPolynomial.eval (coordinates p) (factorPolynomial n 0 α r P)‖^2+
        ‖MvPolynomial.eval (coordinates p) (factorPolynomial n 1 α r P)‖^2/2+
        ‖MvPolynomial.eval (coordinates p) (factorPolynomial n 2 α r P)‖^2/4)*weight α β r b p := by
  have he := exponential_weight α β r b p
  simp only [norm_mul,mul_pow] at he
  simp only [limitDensity,exponentialProfile,one_mul,norm_mul,mul_pow,factorPolynomial_eval,
    pow_zero,pow_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  unfold KFCausalQuarticPlaneDomination.potential at he
  linear_combination (‖chart α r (p.1.1^2+(p.1.2 0)^2) p.2‖^n)^2*
    ‖P.eval (neutral r (p.1.2 0) (p.1.2 1))‖^2*he

theorem limitDensity_integrable (n : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    Integrable (limitDensity n α β r (exponentialProfile b 1 P)) jointMeasure := by
  have hi (k : ℕ) : Integrable (fun p : Joint =>
      ‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r P)‖^2*weight α β r b p) jointMeasure :=
    KFCausalJointPolynomialIntegrability.squared_polynomial_integrable _ _ _ _ _ hA hC (by positivity) _
  apply (((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)).congr
  filter_upwards [] with p
  rw [density_decomposition]
  simp only [Pi.add_apply]
  ring

theorem actual_limitDensity_integrable (n : ℕ) (α β ε y s : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (limitDensity n α β (KFCausalClockFloorRelativeShift.scale ε y s)
      (exponentialProfile b 1 P)) jointMeasure := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hw hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact limitDensity_integrable n α β _ b P hβ ha hc

#print axioms chargedPolynomial_eval
#print axioms neutralPolynomial_eval
#print axioms fieldPolynomial_eval
#print axioms substitutedPolynomial_eval
#print axioms factorPolynomial_eval
#print axioms exponential_weight
#print axioms density_decomposition
#print axioms limitDensity_integrable
#print axioms actual_limitDensity_integrable
end
end UnifiedTheory.Audit.KFCausalClusteredWidthDensityIntegrability
