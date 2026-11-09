/- Identify the complete derived clock response with the actual positive
joint density derivative, including its neutral, Gaussian and field terms. -/
import UnifiedTheory.Audit.KFCausalClusteredClockFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockDensity
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalClusteredClockFactors
open KFCausalClusteredWidthProfiles (widths coefficients limitDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClusteredWidthDensityIntegrability (factorPolynomial)
open KFCausalJointPolynomialIntegrability (coordinates)

def component (n k : ℕ) (α β δ : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (factor n k α β δ r b P p)*slope n k α β δ r v b P p).re
def limitComponent (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (limitFactor n k α β r b P p)*limitSlope n k α β r v b P p).re
def response (n : ℕ) (α β δ : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  component n 0 α β δ r v b P p+component n 1 α β δ r v b P p/2+component n 2 α β δ r v b P p/4
def limitResponse (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  limitComponent n 0 α β r v b P p+limitComponent n 1 α β r v b P p/2+limitComponent n 2 α β r v b P p/4

theorem base_norm (α β : ℝ) (r b : ℂ) (p : Joint) :
    ‖Complex.exp (E α β r b p)‖^2 = KFCausalClusteredWidthDensityIntegrability.weight α β r b p := by
  rw [Complex.norm_exp,← Real.exp_nat_mul]
  unfold E G Z N KFCausalClusteredWidthDensityIntegrability.weight KFCausalJointPolynomialIntegrability.weight
  simp only [← Real.exp_add]
  congr 1
  rw [Complex.add_re,Complex.add_re,Complex.neg_re,KFCausalReciprocalWedgeGeometry.chart_re]
  simp only [Complex.ofReal_re,KFCausalReciprocalNeutralKernel.neutral,Complex.mul_re,
    Complex.add_re,Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem factor_joint (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    factor n k α β δ r b P p = (F r p:ℂ)^k*Complex.exp (G β r p:ℂ)*
      profileSum (n+1) (widths n δ) (coefficients n δ) (fun _ => exponentialProfile b 1 P) (Z α r p) (N r p) := by
  rw [KFCausalClusteredWidthProfiles.profileSum_factor,KFCausalClusteredWidthProfiles.laplaceSum_exact n δ hδ]
  simp only [factor,E,Complex.exp_add,exponentialProfile,one_mul]
  ring

theorem density_factors (n : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    positiveDensity (n+1) α β (widths n δ) r (coefficients n δ) (fun _ => exponentialProfile b 1 P) p =
      ‖factor n 0 α β δ r b P p‖^2+‖factor n 1 α β δ r b P p‖^2/2+‖factor n 2 α β δ r b P p‖^2/4 := by
  rw [factor_joint n 0 α β δ hδ,factor_joint n 1 α β δ hδ,factor_joint n 2 α β δ hδ]
  have hg : (Real.exp (G β r p))^2 = Real.exp (-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold G
    ring
  simp only [norm_mul,mul_pow,norm_pow,Complex.norm_exp,Complex.ofReal_re,Complex.norm_real,
    Real.norm_eq_abs,pow_zero,pow_one,one_mul,sq_abs,hg]
  unfold positiveDensity KFCausalReciprocalNeutralLaplace.weight KFCausalQuarticPlaneDomination.potential
  change _ = _
  simp only [F,Z,N]
  ring

theorem limitFactor_norm (n k : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    ‖limitFactor n k α β r b P p‖^2 =
      ‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r P)‖^2*
        KFCausalClusteredWidthDensityIntegrability.weight α β r b p := by
  have he : limitFactor n k α β r b P p = Complex.exp (E α β r b p)*
      MvPolynomial.eval (coordinates p) (factorPolynomial n k α r P) := by
    rw [KFCausalClusteredWidthDensityIntegrability.factorPolynomial_eval]
    unfold limitFactor F Z N
    ring
  rw [he,norm_mul,mul_pow,base_norm,mul_comm]

theorem limitDensity_factors (n : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitDensity n α β r (exponentialProfile b 1 P) p =
      ‖limitFactor n 0 α β r b P p‖^2+‖limitFactor n 1 α β r b P p‖^2/2+‖limitFactor n 2 α β r b P p‖^2/4 := by
  rw [KFCausalClusteredWidthDensityIntegrability.density_decomposition]
  simp only [limitFactor_norm]
  ring

theorem density_derivative (n : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r : ℝ → ℂ)
    (v b : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => positiveDensity (n+1) α β (widths n δ) (r t) (coefficients n δ)
      (fun _ => exponentialProfile b 1 P) p) (response n α β δ (r s) v b P p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => factor n k α β δ (r t) b P p) (fun _ => slope n k α β δ (r s) v b P p) s
    (factor_derivative n k α β δ hδ r v b P s p hr)
  convert ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4) using 1
  funext t
  exact density_factors n α β δ hδ (r t) b P p

theorem limitDensity_derivative (n : ℕ) (α β : ℝ) (r : ℝ → ℂ)
    (v b : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitDensity n α β (r t) (exponentialProfile b 1 P) p)
      (limitResponse n α β (r s) v b P p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => limitFactor n k α β (r t) b P p) (fun _ => limitSlope n k α β (r s) v b P p) s
    (limitFactor_derivative n k α β r v b P s p hr)
  convert ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4) using 1
  funext t
  exact limitDensity_factors n α β (r t) b P p

theorem response_tendsto (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => response n α β δ r v b P p) (𝓝[>] 0)
      (𝓝 (limitResponse n α β r v b P p)) := by
  have hk (k : ℕ) : Tendsto (fun δ : ℝ => component n k α β δ r v b P p) (𝓝[>] 0)
      (𝓝 (limitComponent n k α β r v b P p)) := by
    have ht := (Complex.continuous_re.tendsto _).comp
      (((factor_tendsto n k α β r b P p).star).mul (slope_tendsto n k α β r v b P p))
    simpa only [component,limitComponent,Complex.star_def] using ht.const_mul 2
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

#print axioms base_norm
#print axioms factor_joint
#print axioms density_factors
#print axioms limitFactor_norm
#print axioms limitDensity_factors
#print axioms density_derivative
#print axioms limitDensity_derivative
#print axioms response_tendsto
end
end UnifiedTheory.Audit.KFCausalClusteredClockDensity
