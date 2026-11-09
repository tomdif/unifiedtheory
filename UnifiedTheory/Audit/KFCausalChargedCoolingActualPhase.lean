/- The phase parameters in the positive cooling kernels are derived
from the actual complex clock scale, with principal arguments in the
required strict strip. -/
import UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargedCoolingActualPhase
noncomputable section
open KFCausalClockFloorRelativeShift (scale)

def angle (r : ℂ) : ℝ := 2*r.arg
def radius (α : ℝ) (r : ℂ) : ℝ := (α/2)*‖r‖^2
def slopeRadius (α : ℝ) (r : ℂ) : ℝ := α*‖r‖

theorem square_arg (r : ℂ) (hr : |r.im| < r.re) : (r^2).arg = angle r := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
  have hn : r ≠ 0 := by intro hz; rw [hz] at ha; norm_num at ha
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have he := Complex.arg_mul hn hn (show r.arg+r.arg ∈ Set.Ioc (-Real.pi) Real.pi by
    constructor <;> linarith [hb.1,hb.2])
  simpa only [pow_two,angle,two_mul] using he

theorem angle_strip (r : ℂ) (hr : |r.im| < r.re) : |angle r| < Real.pi/2 := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
  have hs : 0 < (r^2).re := by
    simp only [pow_two,Complex.mul_re]
    nlinarith [sq_abs r.im,
      mul_pos (sub_pos.mpr hr) (add_pos_of_pos_of_nonneg ha (abs_nonneg r.im))]
  rw [← square_arg r hr]
  exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs)

theorem radii_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re) :
    0 < radius α r ∧ 0 < slopeRadius α r := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg _) hr
  have hn : r ≠ 0 := by intro hz; rw [hz] at ha; norm_num at ha
  have hp : 0 < ‖r‖ := norm_pos_iff.mpr hn
  unfold radius slopeRadius
  constructor <;> positivity

theorem gamma_polar (α : ℝ) (r : ℂ) :
    (α:ℂ)*r^2/2 = (radius α r:ℂ)*Complex.exp ((angle r:ℂ)*Complex.I) := by
  have he := Complex.norm_mul_exp_arg_mul_I r
  have ha : (angle r:ℂ)*Complex.I = (r.arg:ℂ)*Complex.I+(r.arg:ℂ)*Complex.I := by
    unfold angle
    push_cast
    ring
  rw [ha,Complex.exp_add]
  unfold radius
  push_cast
  calc
    (α:ℂ)*r^2/2 = (α:ℂ)/2*((‖r‖:ℂ)*Complex.exp ((r.arg:ℂ)*Complex.I))^2 := by rw [he]; ring
    _ = _ := by ring

theorem slope_polar (α : ℝ) (r : ℂ) :
    (α:ℂ)*r = (slopeRadius α r:ℂ)*Complex.exp ((angle r:ℂ)*Complex.I/2) := by
  have ha : (angle r:ℂ)*Complex.I/2 = (r.arg:ℂ)*Complex.I := by
    unfold angle
    push_cast
    ring
  rw [ha]
  unfold slopeRadius
  push_cast
  rw [mul_assoc,Complex.norm_mul_exp_arg_mul_I]

theorem phase_parameters (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re) :
    |angle r| < Real.pi/2 ∧ 0 < radius α r ∧ 0 < slopeRadius α r ∧
      (α:ℂ)*r^2/2 = (radius α r:ℂ)*Complex.exp ((angle r:ℂ)*Complex.I) ∧
      (α:ℂ)*r = (slopeRadius α r:ℂ)*Complex.exp ((angle r:ℂ)*Complex.I/2) :=
  ⟨angle_strip r hr,(radii_positive α r hα hr).1,(radii_positive α r hα hr).2,
    gamma_polar α r,slope_polar α r⟩

theorem actual_sector (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    |(scale ε y s).im| < (scale ε y s).re := by
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hs := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  nlinarith [sq_abs (scale ε y s).im,abs_nonneg (scale ε y s).im]

theorem actual_phase_parameters (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    |angle (scale ε y s)| < Real.pi/2 ∧ 0 < radius α (scale ε y s) ∧
      0 < slopeRadius α (scale ε y s) ∧
      (α:ℂ)*(scale ε y s)^2/2 = (radius α (scale ε y s):ℂ)*
        Complex.exp ((angle (scale ε y s):ℂ)*Complex.I) ∧
      (α:ℂ)*(scale ε y s) = (slopeRadius α (scale ε y s):ℂ)*
        Complex.exp ((angle (scale ε y s):ℂ)*Complex.I/2) :=
  phase_parameters α _ hα (actual_sector ε y s hε hy)

#print axioms square_arg
#print axioms angle_strip
#print axioms radii_positive
#print axioms gamma_polar
#print axioms slope_polar
#print axioms phase_parameters
#print axioms actual_sector
#print axioms actual_phase_parameters
end
end UnifiedTheory.Audit.KFCausalChargedCoolingActualPhase
