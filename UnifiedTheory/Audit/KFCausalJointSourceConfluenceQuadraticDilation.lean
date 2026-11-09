/- The genuine quadratic joint-confluence profile has an integrable full
charged dilation response with the exact four-dimensional Jacobian. -/
import UnifiedTheory.Audit.KFCausalCorrelatedDilationDivergence
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticDilation
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalCorrelatedDilationEnvelope (scale geometry)
open KFCausalCorrelatedDilationPolynomials (field fieldVelocity velocity)
open KFCausalClusteredClockFactors (Z Zd N Nd F E Ed)
open KFCausalJointSourceConfluenceFactors (Q Qd limitFactor limitDensity)

def degrees : Fin 3 → ℕ := ![2,1,0]
def coefficients (w : ℝ) (ℓ : ℂ) : Fin 3 → ℂ := ![1/(w:ℂ)^2,-2*ℓ/(w:ℂ),ℓ^2]
def polynomials (P : Polynomial ℂ) : Fin 3 → Polynomial ℂ := ![P,Polynomial.X*P,Polynomial.X^2*P]

def dilationFactor (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) : ℂ :=
  Complex.exp (E (w*α) β (geometry ell r t) b p)*(field ell r t p:ℂ)^k*
    Q α (geometry ell r t) ℓ p^2*P.eval (N (geometry ell r t) p)

def dilationSlope (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w*α) β r b p)*
    (Q α r ℓ p^2*((k:ℂ)*(F r p:ℂ)^(k-1)*
      ((ell*KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0:ℝ):ℂ)*P.eval (N r p)+
      (F r p:ℂ)^k*(P.derivative.eval (N r p)*Nd ((ell:ℂ)*r) p+
        Ed (w*α) β r ((ell:ℂ)*r) b p*P.eval (N r p)))+
      2*(F r p:ℂ)^k*Q α r ℓ p*Qd α r ((ell:ℂ)*r) ℓ p*P.eval (N r p))

def dilationComponent (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (limitFactor 2 k α β w r b ℓ P p)*dilationSlope k α β w ell r b ℓ P p).re

def dilationResponse (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  dilationComponent 0 α β w ell r b ℓ P p+dilationComponent 1 α β w ell r b ℓ P p/2+
    dilationComponent 2 α β w ell r b ℓ P p/4

theorem scaled_Z (α w : ℝ) (r : ℂ) (p : Joint) : Z (w*α) r p=(w:ℂ)*Z α r p := by
  unfold Z KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalWedgeGeometry.gamma
  simp only [map_div₀,map_mul,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

theorem factor_representation (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw : w ≠ 0) (t : ℝ) (p : Joint) :
    KFCausalCorrelatedDilationDifferentiation.value 3 degrees k (fun _ => w*α) β ell r
      (fun _ => b) (coefficients w ℓ) (polynomials P) t p=dilationFactor k α β w ell r b ℓ P t p := by
  simp only [KFCausalCorrelatedDilationDifferentiation.value,Fin.sum_univ_succ,Fin.sum_univ_zero,
    degrees,coefficients,polynomials,Matrix.cons_val_zero,Matrix.cons_val_succ,
    KFCausalCorrelatedDilationPolynomials.packet,KFCausalCorrelatedDilationPolynomials.prefactor,
    Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_pow,pow_zero,pow_one,mul_one,add_zero,
    dilationFactor,Q,scaled_Z]
  field_simp [Complex.ofReal_ne_zero.mpr hw]
  ring

theorem factor_zero (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    dilationFactor k α β w ell r b ℓ P 0 p=limitFactor 2 k α β w r b ℓ P p := by
  simp only [dilationFactor,limitFactor,geometry,scale,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,field,F]

theorem factor_derivative (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    HasDerivAt (fun t => dilationFactor k α β w ell r b ℓ P t p)
      (dilationSlope k α β w ell r b ℓ P p) 0 := by
  have hr : HasDerivAt (geometry ell r) ((ell:ℂ)*r) 0 := by
    simpa only [velocity,geometry,scale,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul] using
      KFCausalCorrelatedDilationPolynomials.geometry_derivative ell r 0
  have hf : HasDerivAt (fun t => field ell r t p)
      (ell*KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0) 0 := by
    simpa only [fieldVelocity,scale,mul_zero,Real.exp_zero,mul_one] using
      KFCausalCorrelatedDilationPolynomials.field_derivative ell r 0 p
  have hp := (P.hasDerivAt (N (geometry ell r 0) p)).scomp 0
    (KFCausalClusteredClockFactors.N_derivative (geometry ell r) ((ell:ℂ)*r) 0 p hr)
  have he := KFCausalClusteredClockFactors.E_derivative (w*α) β (geometry ell r) ((ell:ℂ)*r) b 0 p hr
  have hq := KFCausalJointSourceConfluenceFactors.Q_derivative α (geometry ell r) ((ell:ℂ)*r) ℓ 0 p hr
  have hd := ((he.cexp.mul (hf.ofReal_comp.pow k)).mul (hq.pow 2)).mul hp
  convert hd using 1
  simp only [dilationSlope,geometry,scale,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,
    field,F,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.mul_apply,Pi.pow_apply,Function.comp_apply,smul_eq_mul]
  ring

theorem slope_representation (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw : w ≠ 0) (p : Joint) :
    KFCausalCorrelatedDilationDifferentiation.slope 3 degrees k (fun _ => w*α) β ell r
      (fun _ => b) (coefficients w ℓ) (polynomials P) 0 p=dilationSlope k α β w ell r b ℓ P p := by
  have hv := KFCausalCorrelatedDilationDifferentiation.value_derivative 3 degrees k (fun _ => w*α)
    β ell r (fun _ => b) (coefficients w ℓ) (polynomials P) 0 p
  simp_rw [factor_representation k α β w ell r b ℓ P hw] at hv
  exact hv.unique (factor_derivative k α β w ell r b ℓ P p)

theorem component_representation (k : ℕ) (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hw : w ≠ 0) (p : Joint) :
    KFCausalCorrelatedDilationDifferentiation.response 3 degrees k (fun _ => w*α) β ell r
      (fun _ => b) (coefficients w ℓ) (polynomials P) 0 p=dilationComponent k α β w ell r b ℓ P p := by
  rw [KFCausalCorrelatedDilationDifferentiation.response,factor_representation k α β w ell r b ℓ P hw,
    factor_zero,slope_representation k α β w ell r b ℓ P hw]
  rfl

variable (α β w ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (hw : 1 ≤ w)
  (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2)
include ell hw hβ hA hC

theorem channel_density_integrable (k : ℕ) :
    Integrable (fun p => ‖limitFactor 2 k α β w r b ℓ P p‖^2) jointMeasure := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w β hw hA hC
  have hi := KFCausalCorrelatedDilationDifferentiation.density_integrable 3 degrees k (fun _ => w*α)
    β ell r (fun _ => b) (coefficients w ℓ) (polynomials P) hβ (fun _ => hAw) (fun _ => hCw) 0
      (by constructor <;> norm_num)
  apply hi.congr
  filter_upwards [] with p
  rw [factor_representation k α β w ell r b ℓ P (zero_lt_one.trans_le hw).ne',factor_zero]

theorem channel_response_integrable (k : ℕ) :
    Integrable (dilationComponent k α β w ell r b ℓ P) jointMeasure := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w β hw hA hC
  have hi := KFCausalCorrelatedDilationDivergence.response_integrable 3 degrees k (fun _ => w*α)
    β ell r (fun _ => b) (coefficients w ℓ) (polynomials P) hβ (fun _ => hAw) (fun _ => hCw) 0
      (by constructor <;> norm_num)
  exact hi.congr (Filter.Eventually.of_forall
    (component_representation k α β w ell r b ℓ P (zero_lt_one.trans_le hw).ne'))

theorem channel_response_integral (k : ℕ) :
    (∫ p, dilationComponent k α β w ell r b ℓ P p ∂jointMeasure)=
      -4*ell*(∫ p, ‖limitFactor 2 k α β w r b ℓ P p‖^2 ∂jointMeasure) := by
  obtain ⟨hAw,hCw⟩ := KFCausalJointFourierDilationQuartic.width_floors α r w β hw hA hC
  have hi := KFCausalCorrelatedDilationDivergence.response_integral 3 degrees k (fun _ => w*α)
    β ell r (fun _ => b) (coefficients w ℓ) (polynomials P) hβ (fun _ => hAw) (fun _ => hCw)
  simpa only [component_representation k α β w ell r b ℓ P (zero_lt_one.trans_le hw).ne',
    factor_representation k α β w ell r b ℓ P (zero_lt_one.trans_le hw).ne',factor_zero] using hi

theorem response_integrable : Integrable (dilationResponse α β w ell r b ℓ P) jointMeasure := by
  have hi := channel_response_integrable α β w ell r b ℓ P hw hβ hA hC
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

theorem response_integral :
    (∫ p, dilationResponse α β w ell r b ℓ P p ∂jointMeasure)=
      -4*ell*(∫ p, limitDensity 2 α β w r b ℓ P p ∂jointMeasure) := by
  have hr := channel_response_integrable α β w ell r b ℓ P hw hβ hA hC
  have hd := channel_density_integrable α β w ell r b ℓ P hw hβ hA hC
  have hrs := integral_add ((hr 0).add ((hr 1).div_const 2)) ((hr 2).div_const 4)
  have hds := integral_add ((hd 0).add ((hd 1).div_const 2)) ((hd 2).div_const 4)
  simp only [Pi.add_apply] at hrs hds
  unfold dilationResponse limitDensity
  rw [hrs,integral_add (hr 0) ((hr 1).div_const 2),integral_div,integral_div,
    hds,integral_add (hd 0) ((hd 1).div_const 2),integral_div,integral_div]
  simp only [channel_response_integral α β w ell r b ℓ P hw hβ hA hC]
  ring

#print axioms scaled_Z
#print axioms factor_representation
#print axioms factor_zero
#print axioms factor_derivative
#print axioms slope_representation
#print axioms component_representation
#print axioms channel_density_integrable
#print axioms channel_response_integrable
#print axioms channel_response_integral
#print axioms response_integrable
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticDilation
