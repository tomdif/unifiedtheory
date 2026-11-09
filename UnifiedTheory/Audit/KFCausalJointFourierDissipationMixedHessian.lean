/- The full Cartesian charged/neutral second-jet contraction reduces
exactly to the mixed density whose neutral integral is a proved square.
The retained charged first derivative is explicit. No charged boundary
identity or uniform estimate is asserted by this pointwise calculation. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedHessian
noncomputable section
open scoped ComplexConjugate
open KFCausalReciprocalWedgeVelocity (radius)
open KFCausalJointFourierDissipationKernel (correlation)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalNeutralQuarticTransportForms (velocity acceleration)
open KFCausalJointFourierDissipationMixedBoundary (mixed)
open KFCausalJointFourierDissipationMixedSquare (reducedDensity)

def diagonal (x : ℝ) (f f₁ f₂ : ℂ) : ℝ :=
  2*potential x*(‖f₁‖^2+(conj f*f₂).re)

def cross (x : ℝ) (f f₁ f₂ f₁₂ : ℂ) : ℝ :=
  2*potential x*((conj f₁*f₂).re+(conj f*f₁₂).re)

def contraction (u v Y c η L x : ℝ) (p q f g k C Cg H : ℂ) : ℝ :=
  Y/4*(diagonal x f (2*(u:ℂ)*p*C)
      (2*p*C+4*(u:ℂ)^2*p^2*H)+
    diagonal x f (2*(v:ℂ)*p*C+velocity η L*g)
      (2*p*C+4*(v:ℂ)^2*p^2*H+4*(v:ℂ)*p*velocity η L*Cg+velocity η L^2*k))+
  (u^2+v^2)*Y*diagonal x f (q*C) (q^2*H)-
  c*Y*u*cross x f (2*(u:ℂ)*p*C) (q*C) (2*(u:ℂ)*p*q*H)-
  c*Y*v*cross x f (2*(v:ℂ)*p*C+velocity η L*g) (q*C)
    (2*(v:ℂ)*p*q*H+q*velocity η L*Cg)

theorem geometric_symbol (α : ℝ) (r : ℂ) (hR : radius r ≠ 0) :
    ((α:ℂ)*r^2/2)^2+((α:ℂ)*(conj r)^2/2)^2-
      2*(correlation r:ℂ)*((α:ℂ)*r^2/2)*((α:ℂ)*(conj r)^2/2) = 0 := by
  have h := KFCausalJointFourierDissipationKernel.holomorphic_symbol_zero r hR
  linear_combination (α:ℂ)^2/4*h

theorem geometric_gram (α : ℝ) (r C : ℂ) (hR : radius r ≠ 0) :
    ‖((α:ℂ)*r^2/2)*C‖^2+‖((α:ℂ)*(conj r)^2/2)*C‖^2-
      2*correlation r*(conj (((α:ℂ)*r^2/2)*C)*(((α:ℂ)*(conj r)^2/2)*C)).re =
      2*‖(((α:ℂ)*r^2/2)-(correlation r:ℂ)*((α:ℂ)*(conj r)^2/2))*C‖^2 := by
  unfold correlation KFCausalReciprocalGaussianCoordinates.area radius at *
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.div_ofNat_re,Complex.div_ofNat_im]
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  field_simp
  ring

theorem contraction_reduction (u v Y c η L x : ℝ) (p q f g k C Cg H : ℂ)
    (hs : p^2+q^2-2*(c:ℂ)*p*q = 0)
    (hg : ‖p*C‖^2+‖q*C‖^2-2*c*(conj (p*C)*(q*C)).re =
      2*‖(p-(c:ℂ)*q)*C‖^2) :
    contraction u v Y c η L x p q f g k C Cg H =
      Y*(2*potential x*(conj f*(p*C)).re)+
      reducedDensity u v Y η L x f g k ((p-(c:ℂ)*q)*C) ((p-(c:ℂ)*q)*Cg) := by
  have hh := KFCausalJointFourierDissipationKernel.holomorphic_hessian_identity
    c p q f C H hs
  rw [hg] at hh
  unfold contraction diagonal cross reducedDensity mixed acceleration velocity
  simp only [Complex.sq_norm,Complex.normSq_apply] at hh ⊢
  simp only [Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,pow_two] at hh ⊢
  linear_combination Y*(u^2+v^2)*potential x*hh

theorem actual_contraction_reduction (u v Y η L x α : ℝ) (r f g k C Cg H : ℂ)
    (hR : radius r ≠ 0) :
    let p := (α:ℂ)*r^2/2
    let q := (α:ℂ)*(conj r)^2/2
    let d := p-(correlation r:ℂ)*q
    contraction u v Y (correlation r) η L x p q f g k C Cg H =
      Y*(2*potential x*(conj f*(p*C)).re)+
      reducedDensity u v Y η L x f g k (d*C) (d*Cg) :=
  contraction_reduction u v Y (correlation r) η L x _ _ f g k C Cg H
    (geometric_symbol α r hR) (geometric_gram α r C hR)

#print axioms geometric_symbol
#print axioms geometric_gram
#print axioms contraction_reduction
#print axioms actual_contraction_reduction
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedHessian
