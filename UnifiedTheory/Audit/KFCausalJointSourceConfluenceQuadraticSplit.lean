/- Exact full-response decomposition for the genuine quadratic joint source
confluence profile.  The source slope is fixed under clock differentiation. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticDilation
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticCooling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticSplit
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClusteredClockFactors (Zd Nd Fd Gd Ed B0)
open KFCausalJointSourceConfluenceFactors (Qd B1 limitSlope limitComponent limitResponse limitDensity)
open KFCausalJointSourceConfluenceQuadraticDilation (dilationSlope dilationComponent dilationResponse)
open KFCausalJointSourceConfluenceQuadraticCooling (coolingSlope coolingComponent coolingResponse)

private theorem charged_split (α δ ell : ℝ) (r : ℂ) (p : Joint) :
    Zd α r ((δ:ℂ)+(ell:ℂ)*r) p=Zd α r (δ:ℂ) p+Zd α r ((ell:ℂ)*r) p := by
  simp only [Zd,map_add,map_mul,Complex.conj_ofReal]
  ring

private theorem charged_scale (α w : ℝ) (r v : ℂ) (p : Joint) :
    Zd (w*α) r v p=(w:ℂ)*Zd α r v p := by
  simp only [Zd,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

private theorem neutral_split (δ ell : ℝ) (r : ℂ) (p : Joint) :
    Nd ((δ:ℂ)+(ell:ℂ)*r) p=Nd ((ell:ℂ)*r) p := by
  simp only [Nd,Complex.add_im,Complex.ofReal_im,zero_add]

private theorem exponent_split (α β w δ ell : ℝ) (r b : ℂ) (p : Joint) :
    Ed (w*α) β r ((δ:ℂ)+(ell:ℂ)*r) b p=
      Ed (w*α) β r ((ell:ℂ)*r) b p-(w:ℂ)*Zd α r (δ:ℂ) p := by
  simp only [Ed,charged_split,charged_scale,neutral_split,Gd,Complex.add_im,
    Complex.ofReal_im,zero_add]
  ring

private theorem field_split (δ ell : ℝ) (r : ℂ) (p : Joint) :
    Fd ((δ:ℂ)+(ell:ℂ)*r) p=
      ell*KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0+(-2*δ-3*ell)*p.1.2 0 := by
  simp only [Fd,KFCausalChargedPairCoordinates.fieldSlope,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem slope_split (k : ℕ) (α β w δ ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitSlope 2 k α β w r ((δ:ℂ)+(ell:ℂ)*r) b ℓ P p=
      dilationSlope k α β w ell r b ℓ P p+coolingSlope k α β w δ (-2*δ-3*ell) r b ℓ P p := by
  simp only [limitSlope,B0,B1,Qd,charged_split,neutral_split,exponent_split,field_split,
    dilationSlope,coolingSlope,show 2-1=1 from rfl,pow_one,Nat.cast_ofNat,
    Complex.ofReal_add]
  ring

theorem component_split (k : ℕ) (α β w δ ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitComponent 2 k α β w r ((δ:ℂ)+(ell:ℂ)*r) b ℓ P p=
      dilationComponent k α β w ell r b ℓ P p+
        coolingComponent k α β w δ (-2*δ-3*ell) r b ℓ P p := by
  simp only [limitComponent,slope_split,dilationComponent,coolingComponent,mul_add,Complex.add_re]

theorem response_split (α β w δ ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitResponse 2 α β w r ((δ:ℂ)+(ell:ℂ)*r) b ℓ P p=
      dilationResponse α β w ell r b ℓ P p+coolingResponse α β w δ (-2*δ-3*ell) r b ℓ P p := by
  simp only [limitResponse,component_split,dilationResponse,coolingResponse]
  ring

variable (α β w δ ell : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (hw : 1 ≤ w)
  (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2)
include hw hβ hA hC

theorem cooling_integrable :
    Integrable (coolingResponse α β w δ (-2*δ-3*ell) r b ℓ P) jointMeasure := by
  have hr := KFCausalJointSourceConfluenceIntegrability.response_integrable 2 α β w r
    ((δ:ℂ)+(ell:ℂ)*r) b ℓ P hw hβ hA hC
  have hd := KFCausalJointSourceConfluenceQuadraticDilation.response_integrable
    α β w ell r b ℓ P hw hβ hA hC
  apply (hr.sub hd).congr
  filter_upwards [] with p
  simp only [Pi.sub_apply,response_split,add_sub_cancel_left]

theorem response_integral :
    (∫ p, limitResponse 2 α β w r ((δ:ℂ)+(ell:ℂ)*r) b ℓ P p ∂jointMeasure)=
      -4*ell*(∫ p, limitDensity 2 α β w r b ℓ P p ∂jointMeasure)+
        ∫ p, coolingResponse α β w δ (-2*δ-3*ell) r b ℓ P p ∂jointMeasure := by
  simp_rw [response_split]
  rw [integral_add
    (KFCausalJointSourceConfluenceQuadraticDilation.response_integrable α β w ell r b ℓ P hw hβ hA hC)
    (cooling_integrable α β w δ ell r b ℓ P hw hβ hA hC),
    KFCausalJointSourceConfluenceQuadraticDilation.response_integral α β w ell r b ℓ P hw hβ hA hC]

#print axioms slope_split
#print axioms component_split
#print axioms response_split
#print axioms cooling_integrable
#print axioms response_integral
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticSplit
