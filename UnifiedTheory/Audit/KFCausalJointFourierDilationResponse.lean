/- The full dilation response of each original neutral Fourier field
is integrable and has exactly the charged Jacobian contribution.
All integral hypotheses are derived from explicit positive widths. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationRepresentation
import UnifiedTheory.Audit.KFCausalCorrelatedDilationDivergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredClockFactors (Z Zd)
open KFCausalCorrelatedDilationEnvelope (scale geometry)
open KFCausalJointFourierDilationRepresentation (fieldDensity density_eq density_zero geometry_zero)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalJointFourierDilationJet (dilationCoefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalGaussianCoordinates (area)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ) (ell : ℝ)

def response (j : ℕ) (p : Joint) : ℝ :=
  KFCausalNeutralFourierResponseSplit.response n β b (coefficients n w c (Z α r p))
    (dilationCoefficients n α w c r ell (p.1.1) (p.1.2 0) p.2) P j
    (fieldSlope r*p.1.2 0) (2*r.im*p.1.2 0)
    (ell*(fieldSlope r*p.1.2 0)) (ell*(2*r.im*p.1.2 0)) (p.1.2 1)

theorem density_derivative (j : ℕ) (p : Joint) :
    HasDerivAt (fun t => fieldDensity n α β w b c P r ell t j p)
      (response n α β w b c P r ell j p) 0 := by
  have hr : HasDerivAt (geometry ell r) ((ell:ℂ)*r) 0 := by
    simpa only [KFCausalCorrelatedDilationPolynomials.velocity,geometry_zero] using
      KFCausalCorrelatedDilationPolynomials.geometry_derivative ell r 0
  have hz : HasDerivAt (fun t => Z α (geometry ell r t) p)
      (((2*ell:ℝ):ℂ)*Z α r p) 0 := by
    convert KFCausalClusteredClockFactors.Z_derivative α (geometry ell r) ((ell:ℂ)*r) 0 p hr using 1
    rw [geometry_zero]
    unfold Z Zd KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalWedgeGeometry.gamma
    simp only [map_mul,map_div₀,map_pow,Complex.conj_ofReal,map_ofNat]
    push_cast
    ring
  have hC (i : Fin n) : HasDerivAt
      (fun t => coefficients n w c (Z α (geometry ell r t) p) i)
      (dilationCoefficients n α w c r ell p.1.1 (p.1.2 0) p.2 i) 0 := by
    have hd := KFCausalNeutralFourierMovingJet.coefficients_derivative n w c _ _ 0 hz i
    rw [geometry_zero] at hd
    convert hd using 1
    unfold dilationCoefficients Z
    ring
  have hA : HasDerivAt (scale ell) ell 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul ell).exp using 1
    simp
  have hy := KFCausalNeutralFourierMovingJet.actual_translation_derivative
    (geometry ell r) ((ell:ℂ)*r) 0 (p.1.2 0) hr
  have hy' : HasDerivAt (fun t => 2*(geometry ell r t).im*p.1.2 0)
      (ell*(2*r.im*p.1.2 0)) 0 := by
    convert hy using 1
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring
  have hd := KFCausalNeutralFourierMovingJet.square_derivative n β b P
    (fun t => coefficients n w c (Z α (geometry ell r t) p))
    (dilationCoefficients n α w c r ell p.1.1 (p.1.2 0) p.2)
    (fun t => scale ell t*(fieldSlope r*p.1.2 0))
    (fun t => 2*(geometry ell r t).im*p.1.2 0)
    (ell*(fieldSlope r*p.1.2 0)) (ell*(2*r.im*p.1.2 0)) 0 (p.1.2 1) j
    hC (hA.mul_const _) hy'
  simpa only [fieldDensity,response,geometry_zero,scale,mul_zero,Real.exp_zero,one_mul] using hd

theorem response_eq (j : ℕ) (p : Joint) :
    response n α β w b c P r ell j p =
      KFCausalCorrelatedDilationDifferentiation.response n (fun _ => 0) j (fun i => w i*α)
        β ell r b (fun i => c i*(w i:ℂ)) P 0 p := by
  have hd := density_derivative n α β w b c P r ell j p
  simp_rw [density_eq] at hd
  exact hd.unique (KFCausalCorrelatedDilationDifferentiation.density_pointwise_derivative
    n (fun _ => 0) j (fun i => w i*α) β ell r b (fun i => c i*(w i:ℂ)) P 0 p)

variable (hβ : 0 < β) (hA : ∀ i, 0 < (w i*α)*area r)
  (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2)
include hβ hA hC

theorem density_integrable (j : ℕ) :
    Integrable (fieldDensity n α β w b c P r ell 0 j) jointMeasure := by
  change Integrable (fun p => fieldDensity n α β w b c P r ell 0 j p) jointMeasure
  simp_rw [density_eq]
  exact KFCausalCorrelatedDilationDifferentiation.density_integrable n (fun _ => 0) j
    (fun i => w i*α) β ell r b (fun i => c i*(w i:ℂ)) P hβ hA hC 0 (by constructor <;> norm_num)

theorem response_integrable (j : ℕ) :
    Integrable (response n α β w b c P r ell j) jointMeasure := by
  change Integrable (fun p => response n α β w b c P r ell j p) jointMeasure
  simp_rw [response_eq]
  exact KFCausalCorrelatedDilationDivergence.response_integrable n (fun _ => 0) j
    (fun i => w i*α) β ell r b (fun i => c i*(w i:ℂ)) P hβ hA hC 0 (by constructor <;> norm_num)

theorem response_integral (j : ℕ) :
    (∫ p, response n α β w b c P r ell j p ∂jointMeasure) =
      -4*ell*(∫ p, fieldDensity n α β w b c P r ell 0 j p ∂jointMeasure) := by
  simp_rw [response_eq,density_eq]
  exact KFCausalCorrelatedDilationDivergence.response_integral n (fun _ => 0) j
    (fun i => w i*α) β ell r b (fun i => c i*(w i:ℂ)) P hβ hA hC

#print axioms density_derivative
#print axioms response_eq
#print axioms density_integrable
#print axioms response_integrable
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationResponse
