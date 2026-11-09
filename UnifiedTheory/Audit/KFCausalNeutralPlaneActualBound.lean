/- Degree-independent pointwise derivative control for the actual
clock-dependent centered marginal. The coefficient is finite at each
clock point; a bound uniform in clock position is not asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
import UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination

def actualDensity (α β ε y s : ℝ) (P : Polynomial ℂ) (x z : ℝ) : ℝ :=
  density (prefactor α (scale ε y s)) β (planeWidth α β (scale ε y s))
    (fieldSlope (scale ε y s)) P x z

def score (α ε y s : ℝ) : ℝ :=
  deriv (fun t => prefactor α (scale ε y t)) s / prefactor α (scale ε y s) +
    (deriv (fun t => fieldSlope (scale ε y t)) s)^2 /
      widthSlope α ε (Real.exp s) (scale ε y s)

theorem prefactor_differentiableAt (α : ℝ) (r : ℝ → ℂ) (s : ℝ)
    (hr : DifferentiableAt ℝ r s) (hα : 0 < α)
    (hA : 0 < (r s).re^2-(r s).im^2) (hb : (r s).im ≠ 0) :
    DifferentiableAt ℝ (fun t => prefactor α (r t)) s := by
  have ha : DifferentiableAt ℝ (fun t => (r t).re) s :=
    Complex.reCLM.differentiableAt.comp s hr
  have hi : DifferentiableAt ℝ (fun t => (r t).im) s :=
    Complex.imCLM.differentiableAt.comp s hr
  have harea := (ha.pow 2).sub (hi.pow 2)
  have hga := (differentiableAt_const Real.pi).div (harea.const_mul α) (by positivity)
  have hga2 := (differentiableAt_const Real.pi).div (harea.const_mul (2*α)) (by positivity)
  have hs := hga.sqrt (by dsimp; positivity)
  have hs2 := hga2.sqrt (by dsimp; positivity)
  have hj := (differentiableAt_const 1).div ((hi.abs hb).const_mul 4) (by positivity)
  exact (hj.mul (hs2.pow 2)).mul hs

theorem fieldSlope_differentiableAt (r : ℝ → ℂ) (s : ℝ)
    (hr : DifferentiableAt ℝ r s) (hb : (r s).im ≠ 0) :
    DifferentiableAt ℝ (fun t => fieldSlope (r t)) s := by
  have ha : DifferentiableAt ℝ (fun t => (r t).re) s :=
    Complex.reCLM.differentiableAt.comp s hr
  have hi : DifferentiableAt ℝ (fun t => (r t).im) s :=
    Complex.imCLM.differentiableAt.comp s hr
  exact ((differentiableAt_const 3).sub (ha.const_mul 2)).div (hi.const_mul 2)
    (by positivity)

theorem actualDensity_derivative (α β ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (P : Polynomial ℂ) (x z : ℝ) :
    HasDerivAt (fun t => actualDensity α β ε y t P x z)
      (derivativeDensity (prefactor α (scale ε y s))
        (deriv (fun t => prefactor α (scale ε y t)) s) β
        (planeWidth α β (scale ε y s)) (widthSlope α ε (Real.exp s) (scale ε y s))
        (fieldSlope (scale ε y s)) (deriv (fun t => fieldSlope (scale ε y t)) s) P x z) s := by
  have hr := (scale_velocity ε y s hε hy).differentiableAt
  have hb := scale_im_ne_zero ε y s hε hy hy0
  exact density_derivative _ _ _ _ _ _ β s
    (prefactor_differentiableAt α _ s hr hα (scale_square_re_positive ε y s hε hy) hb).hasDerivAt
    (actual_width_derivative α β ε y s hε hy hy0)
    (fieldSlope_differentiableAt _ s hr hb).hasDerivAt P x z

theorem actualDensity_derivative_bound (α β ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (P : Polynomial ℂ) (x z : ℝ) :
    deriv (fun t => actualDensity α β ε y t P x z) s ≤
      score α ε y s * actualDensity α β ε y s P x z := by
  rw [(actualDensity_derivative α β ε y s hα hε hy hy0 P x z).deriv]
  exact derivativeDensity_bound _ _ _ _ _ _ _
    (prefactor_positive α _ hα (scale_square_re_positive ε y s hε hy)
      (scale_im_ne_zero ε y s hε hy hy0))
    (actual_widthSlope_positive α ε y s hα hε hy hy0) P x z

theorem actualDensity_nonnegative (α β ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (P : Polynomial ℂ) (x z : ℝ) :
    0 ≤ actualDensity α β ε y s P x z :=
  density_nonnegative _ _ _ _
    (prefactor_positive α _ hα (scale_square_re_positive ε y s hε hy)
      (scale_im_ne_zero ε y s hε hy hy0)).le P x z

#print axioms prefactor_differentiableAt
#print axioms fieldSlope_differentiableAt
#print axioms actualDensity_derivative
#print axioms actualDensity_derivative_bound
#print axioms actualDensity_nonnegative
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
