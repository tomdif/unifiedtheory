/- Exact corrected cooling for the simultaneous quadratic width/source jet.
The charged jet and the physical real field jet remain linked in the response. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceFactors
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticCooling
noncomputable section
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalClusteredClockFactors (Z Zd N F E)
open KFCausalJointSourceConfluenceFactors (Q limitFactor limitDensity)
open KFCausalChargedCoolingTwoWidthResponse (fieldWeight fieldGradient)

def coolingSlope (k : ℕ) (α β w δ κ : ℝ) (r b ℓ : ℂ)
    (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w*α) β r b p)*
    (-(w:ℂ)*Zd α r (δ:ℂ) p*(F r p:ℂ)^k*Q α r ℓ p^2*P.eval (N r p)+
      (k:ℂ)*(F r p:ℂ)^(k-1)*(κ*(p.1.2 0):ℝ)*Q α r ℓ p^2*P.eval (N r p)+
      2*(F r p:ℂ)^k*Q α r ℓ p*Zd α r (δ:ℂ) p*P.eval (N r p))

def coolingComponent (k : ℕ) (α β w δ κ : ℝ) (r b ℓ : ℂ)
    (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (limitFactor 2 k α β w r b ℓ P p)*
    coolingSlope k α β w δ κ r b ℓ P p).re

def coolingResponse (α β w δ κ : ℝ) (r b ℓ : ℂ)
    (P : Polynomial ℂ) (p : Joint) : ℝ :=
  coolingComponent 0 α β w δ κ r b ℓ P p+
    coolingComponent 1 α β w δ κ r b ℓ P p/2+
    coolingComponent 2 α β w δ κ r b ℓ P p/4

theorem scalar_density (g q : ℂ) (f : ℝ) :
    ‖g*q^2‖^2+‖g*(f:ℂ)*q^2‖^2/2+‖g*(f:ℂ)^2*q^2‖^2/4 =
      ‖g‖^2*‖q‖^4*fieldWeight f := by
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,fieldWeight]
  ring

theorem scalar_response (g q d : ℂ) (w f h : ℝ) :
    2*(conj (g*q^2)*(g*(-(w:ℂ)*d*q^2+2*q*d))).re+
      2*(conj (g*(f:ℂ)*q^2)*(g*(-(w:ℂ)*d*(f:ℂ)*q^2+(h:ℂ)*q^2+2*(f:ℂ)*q*d))).re/2+
      2*(conj (g*(f:ℂ)^2*q^2)*(g*(-(w:ℂ)*d*(f:ℂ)^2*q^2+2*(f:ℂ)*(h:ℂ)*q^2+
        2*(f:ℂ)^2*q*d))).re/4 =
      ‖g‖^2*(fieldWeight f*(4*‖q‖^2*(conj q*d).re-2*w*d.re*‖q‖^4)+
        h*fieldGradient f*‖q‖^4) := by
  simp only [show ‖q‖^4 = (‖q‖^2)^2 by ring,Complex.sq_norm,Complex.normSq_apply]
  norm_num [pow_two,fieldWeight,fieldGradient,map_mul,map_pow,
    Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.conj_re,
    Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem density_factorization (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    limitDensity 2 α β w r b ℓ P p =
      ‖Complex.exp (E (w*α) β r b p)*P.eval (N r p)‖^2*
        ‖Q α r ℓ p‖^4*fieldWeight (F r p) := by
  convert scalar_density (Complex.exp (E (w*α) β r b p)*P.eval (N r p))
    (Q α r ℓ p) (F r p) using 1
  simp only [limitDensity,limitFactor,pow_zero,pow_one,mul_one]
  congr 2 <;> congr 1 <;> ring

theorem response_factorization (α β w δ κ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    coolingResponse α β w δ κ r b ℓ P p =
      ‖Complex.exp (E (w*α) β r b p)*P.eval (N r p)‖^2*
        (fieldWeight (F r p)*(4*‖Q α r ℓ p‖^2*(conj (Q α r ℓ p)*Zd α r (δ:ℂ) p).re-
          2*w*(Zd α r (δ:ℂ) p).re*‖Q α r ℓ p‖^4)+
        κ*(p.1.2 0)*fieldGradient (F r p)*‖Q α r ℓ p‖^4) := by
  convert scalar_response (Complex.exp (E (w*α) β r b p)*P.eval (N r p))
    (Q α r ℓ p) (Zd α r (δ:ℂ) p) w (F r p) (κ*(p.1.2 0)) using 1
  simp only [coolingResponse,coolingComponent,coolingSlope,limitFactor,pow_zero,pow_one,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,zero_mul,one_mul,mul_one,add_zero]
  congr 2 <;> congr 1 <;> congr 1 <;> ring

#print axioms scalar_density
#print axioms scalar_response
#print axioms density_factorization
#print axioms response_factorization
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticCooling
