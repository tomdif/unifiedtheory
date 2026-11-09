/- The charged cooling vector is the divergence of a positive
quadratic diffusion matrix plus positive radial dilation. Its complex
symbol annihilates the holomorphic second derivative. This is an exact
algebraic identity; no boundary trace or integration by parts is assumed. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationKernel
noncomputable section
open scoped ComplexConjugate
open KFCausalNeutralPlaneClockGeometry (denominator)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeVelocity (radius shrink)
open KFCausalJointClockCoolingCoercivity (leftCooling rightCooling coefficient)

def correlation (r : ℂ) : ℝ :=
  ((area r)^2-(2*r.re*r.im)^2)/(radius r)^2

def radialRate (t : ℝ) (r : ℂ) : ℝ :=
  2*t*r.re^2/denominator (1-t) t r

def diffusionForm (r : ℂ) (X Y ξ η : ℝ) : ℝ :=
  X*Y*(ξ^2+η^2-2*correlation r*ξ*η)

theorem radius_identity (r : ℂ) :
    (area r)^2+(2*r.re*r.im)^2 = (radius r)^2 := by
  unfold area radius
  ring

theorem correlation_bounds (r : ℂ) (hR : radius r ≠ 0) :
    -1 ≤ correlation r ∧ correlation r ≤ 1 := by
  have h := radius_identity r
  have hp : 0 < (radius r)^2 := sq_pos_of_ne_zero hR
  unfold correlation
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (area r)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (2*r.re*r.im)]

theorem diffusion_positive (r : ℂ) (hR : radius r ≠ 0)
    (X Y ξ η : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ diffusionForm r X Y ξ η := by
  have h := correlation_bounds r hR
  have he : ξ^2+η^2-2*correlation r*ξ*η =
      (1-correlation r)/2*(ξ+η)^2+(1+correlation r)/2*(ξ-η)^2 := by ring
  unfold diffusionForm
  apply mul_nonneg (mul_nonneg hX hY)
  rw [he]
  have h1 : 0 ≤ (1-correlation r)/2 := by linarith [h.2]
  have h2 : 0 ≤ (1+correlation r)/2 := by linarith [h.1]
  positivity

theorem diffusion_boundary_left (r : ℂ) (Y ξ η : ℝ) :
    diffusionForm r 0 Y ξ η = 0 := by simp [diffusionForm]

theorem diffusion_boundary_right (r : ℂ) (X ξ η : ℝ) :
    diffusionForm r X 0 ξ η = 0 := by simp [diffusionForm]

theorem left_cooling_divergence (t : ℝ) (r : ℂ) (X Y : ℝ)
    (hA : area r ≠ 0) (hR : radius r ≠ 0)
    (hD : denominator (1-t) t r ≠ 0) :
    leftCooling t r X Y =
      shrink t r*(Y-correlation r*X)+radialRate t r*X := by
  unfold leftCooling coefficient shrink correlation radialRate
  unfold area radius at *
  field_simp
  ring

theorem right_cooling_divergence (t : ℝ) (r : ℂ) (X Y : ℝ)
    (hA : area r ≠ 0) (hR : radius r ≠ 0)
    (hD : denominator (1-t) t r ≠ 0) :
    rightCooling t r X Y =
      shrink t r*(X-correlation r*Y)+radialRate t r*Y := by
  exact left_cooling_divergence t r Y X hA hR hD

theorem holomorphic_symbol_zero (r : ℂ) (hR : radius r ≠ 0) :
    (r^2)^2+((conj r)^2)^2-
      2*(correlation r:ℂ)*(r^2*(conj r)^2) = 0 := by
  have hc : (correlation r:ℂ)*((radius r:ℂ)^2) =
      ((area r:ℂ)^2-(2*(r.re:ℂ)*(r.im:ℂ))^2) := by
    have hRc : (radius r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
    unfold correlation
    push_cast
    field_simp
  have he : r^2*(conj r)^2 = (radius r:ℂ)^2 := by
    unfold radius
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  rw [he]
  have he2 : (r^2)^2+((conj r)^2)^2 =
      2*((area r:ℂ)^2-(2*(r.re:ℂ)*(r.im:ℂ))^2) := by
    unfold area
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  rw [he2]
  linear_combination -2*hc

theorem complex_diffusion_positive (c : ℝ) (hc : -1 ≤ c ∧ c ≤ 1) (u v : ℂ) :
    0 ≤ ‖u‖^2+‖v‖^2-2*c*(conj u*v).re := by
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  have h1 : 0 ≤ (1-c)/2 := by linarith [hc.2]
  have h2 : 0 ≤ (1+c)/2 := by linarith [hc.1]
  have he : u.re^2+u.im^2+(v.re^2+v.im^2)-2*c*(u.re*v.re- -u.im*v.im) =
      (1-c)/2*((u.re+v.re)^2+(u.im+v.im)^2)+
      (1+c)/2*((u.re-v.re)^2+(u.im-v.im)^2) := by ring
  simp only [← sq] at *
  rw [he]
  positivity

theorem holomorphic_hessian_identity (c : ℝ) (z w f g h : ℂ)
    (hzw : z^2+w^2-2*(c:ℂ)*z*w = 0) :
    (2*‖z*g‖^2+2*(conj f*(z^2*h)).re)+
      (2*‖w*g‖^2+2*(conj f*(w^2*h)).re)-
      2*c*(2*(conj (z*g)*(w*g)).re+2*(conj f*(z*w*h)).re) =
      2*(‖z*g‖^2+‖w*g‖^2-2*c*(conj (z*g)*(w*g)).re) := by
  have he := congrArg Complex.re (congrArg (fun q : ℂ => conj f*(q*h)) hzw)
  simp only [sub_mul,add_mul,mul_sub,mul_add,Complex.sub_re,Complex.add_re,zero_mul,mul_zero,
    Complex.zero_re] at he
  have hec : (conj f*(2*(c:ℂ)*z*w*h)).re = 2*c*(conj f*(z*w*h)).re := by
    rw [show conj f*(2*(c:ℂ)*z*w*h) = ((2*c:ℝ):ℂ)*(conj f*(z*w*h)) by push_cast; ring]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hec] at he
  linarith

theorem holomorphic_hessian_nonnegative (r f g h : ℂ) (hR : radius r ≠ 0) :
    0 ≤ (2*‖r^2*g‖^2+2*(conj f*((r^2)^2*h)).re)+
      (2*‖(conj r)^2*g‖^2+2*(conj f*(((conj r)^2)^2*h)).re)-
      2*correlation r*(2*(conj (r^2*g)*((conj r)^2*g)).re+
        2*(conj f*(r^2*(conj r)^2*h)).re) := by
  rw [holomorphic_hessian_identity (correlation r) (r^2) ((conj r)^2) f g h
    (by simpa only [mul_assoc] using holomorphic_symbol_zero r hR)]
  exact mul_nonneg (by norm_num) (complex_diffusion_positive _ (correlation_bounds r hR) _ _)

#print axioms radius_identity
#print axioms correlation_bounds
#print axioms diffusion_positive
#print axioms diffusion_boundary_left
#print axioms diffusion_boundary_right
#print axioms left_cooling_divergence
#print axioms right_cooling_divergence
#print axioms holomorphic_symbol_zero
#print axioms complex_diffusion_positive
#print axioms holomorphic_hessian_identity
#print axioms holomorphic_hessian_nonnegative
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationKernel
