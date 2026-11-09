/- The dilation jet is the actual derivative of the charged coordinate
path u(t)=(1+t*l)u, v(t)=(1+t*l)v, Y(t)=(1+2*t*l)Y.
This establishes its meaning as a directional derivative; the integral
of its charged divergence is a separate obligation. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationPath
noncomputable section
open KFCausalReciprocalWedgeGeometry (chart gamma)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalJointFourierDilationJet (dilationCoefficients)
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralFourierResponseSplit (response)
open KFCausalChargedPairCoordinates (fieldSlope)
open scoped ComplexConjugate

def dilationChart (α : ℝ) (r : ℂ) (ell u v Y t : ℝ) : ℂ :=
  chart α r ((1+t*ell)^2*(u^2+v^2)) ((1+2*t*ell)*Y)

theorem chart_zero (α : ℝ) (r : ℂ) (ell u v Y : ℝ) :
    dilationChart α r ell u v Y 0 = chart α r (u^2+v^2) Y := by
  simp [dilationChart]

theorem chart_coordinates (α : ℝ) (r : ℂ) (ell u v Y t : ℝ) :
    dilationChart α r ell u v Y t =
      chart α r (((1+t*ell)*u)^2+((1+t*ell)*v)^2) ((1+2*t*ell)*Y) := by
  unfold dilationChart
  congr 1
  ring

theorem chart_derivative (α : ℝ) (r : ℂ) (ell u v Y : ℝ) :
    HasDerivAt (dilationChart α r ell u v Y)
      (((2*ell:ℝ):ℂ)*chart α r (u^2+v^2) Y) 0 := by
  have h := ((hasDerivAt_id (0:ℝ)).mul_const ell).const_add 1
  have hx := ((h.pow 2).mul_const (u^2+v^2)).ofReal_comp.const_mul (gamma α r)
  have hy := ((((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ell).const_add 1).mul_const Y
  have hd := hx.add (hy.ofReal_comp.const_mul (conj (gamma α r)))
  convert hd using 1
  dsimp
  unfold chart
  push_cast
  ring

theorem coefficients_derivative (n : ℕ) (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r : ℂ) (ell u v Y : ℝ) (i : Fin n) :
    HasDerivAt (fun t => coefficients n w c (dilationChart α r ell u v Y t) i)
      (dilationCoefficients n α w c r ell u v Y i) 0 := by
  have hd := KFCausalNeutralFourierMovingJet.coefficients_derivative n w c
    (dilationChart α r ell u v Y) _ 0 (chart_derivative α r ell u v Y) i
  rw [chart_zero] at hd
  convert hd using 1
  unfold dilationCoefficients
  ring

theorem square_derivative (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (ell u v Y x : ℝ) (j : ℕ) :
    HasDerivAt (fun t => ‖fieldLine n β b (coefficients n w c (dilationChart α r ell u v Y t)) P j
      ((1+t*ell)*(fieldSlope r*v)) ((1+t*ell)*(2*r.im*v)) x‖^2)
      (response n β b (coefficients n w c (chart α r (u^2+v^2) Y))
        (dilationCoefficients n α w c r ell u v Y) P j (fieldSlope r*v) (2*r.im*v)
        (ell*(fieldSlope r*v)) (ell*(2*r.im*v)) x) 0 := by
  have h : HasDerivAt (fun t : ℝ => 1+t*ell) ell 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const ell).const_add 1
  have hd := KFCausalNeutralFourierMovingJet.square_derivative n β b P
    (fun t => coefficients n w c (dilationChart α r ell u v Y t))
    (dilationCoefficients n α w c r ell u v Y)
    (fun t => (1+t*ell)*(fieldSlope r*v)) (fun t => (1+t*ell)*(2*r.im*v))
    (ell*(fieldSlope r*v)) (ell*(2*r.im*v)) 0 x j
    (coefficients_derivative n α w c r ell u v Y) (h.mul_const _) (h.mul_const _)
  simpa only [chart_zero,zero_mul,add_zero,one_mul] using hd

#print axioms chart_zero
#print axioms chart_coordinates
#print axioms chart_derivative
#print axioms coefficients_derivative
#print axioms square_derivative
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationPath
