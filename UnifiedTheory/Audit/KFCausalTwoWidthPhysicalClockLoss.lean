/- The two-width field-absorption loss is uniformly controlled along the
actual physical clock. This scalar estimate does not assert an exchange
of derivatives and the full spatial response integral. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalTwoWidthPhysicalClockLoss
noncomputable section
open KFCausalJointFourierDissipationClock
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction fraction_bounds)

def loss (α m t : ℝ) (r : ℂ) : ℝ :=
  -4*imaginaryRate t r+
    4*(t*normalizedFieldJet t r)^2/(α*r.re*(t*normalizedRealCooling t r)*m)

theorem scalar_loss_bound (α m a d ell k : ℝ) (hα : 0 < α) (hm : 0 < m)
    (ha : 1/2 ≤ a) (hd : 1/8 ≤ d) (hl : -12 ≤ ell) (hk : k^2 ≤ 1296) :
    -4*ell+4*k^2/(α*a*d*m) ≤ 48+82944/(α*m) := by
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  have had : 1/16 ≤ a*d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hd)]
  have hden : α*m/16 ≤ α*a*d*m := by
    have h := mul_le_mul_of_nonneg_left had (mul_pos hα hm).le
    nlinarith only [h]
  have hden0 : 0 < α*a*d*m := by positivity
  have hq : 4*k^2/(α*a*d*m) ≤ 82944/(α*m) := by
    calc
      _ ≤ 5184/(α*a*d*m) := div_le_div_of_nonneg_right (by linarith) hden0.le
      _ ≤ 5184/(α*m/16) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by ring
  linarith

theorem loss_normalized (α m t : ℝ) (r : ℂ) (ht : t ≠ 0) :
    loss α m t r = t*(-4*normalizedDilation t r+
      4*(normalizedFieldJet t r)^2/(α*r.re*normalizedRealCooling t r*m)) := by
  unfold loss
  rw [dilation_identity]
  field_simp

theorem loss_zero (α m : ℝ) (r : ℂ) : loss α m 0 r = 0 := by
  simp [loss,imaginaryRate]

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem physical_loss_bound (α m t : ℝ) (hα : 0 < α) (hm : 0 < m)
    (ht : t ∈ Set.Icc 0 1) :
    loss α m t r ≤ (48+82944/(α*m))*t := by
  by_cases ht0 : t=0
  · simp [ht0,loss_zero]
  rw [loss_normalized α m t r ht0]
  have h := scalar_loss_bound α m (r).re (normalizedRealCooling t r)
    (normalizedDilation t r) (normalizedFieldJet t r) hα hm
    (real_coordinate_bounds ε y s hε hy).1
    (real_cooling_bounds ε y s hε hy t ht).1
    (dilation_bounds ε y s hε hy t ht).1
    (field_jet_square_bound ε y s hε hy t ht)
  simpa only [mul_comm t] using mul_le_mul_of_nonneg_left h ht.1

theorem physical_loss_width_uniform (α m t : ℝ) (hα : 0 < α) (hm : 1 ≤ m)
    (ht : t ∈ Set.Icc 0 1) :
    loss α m t r ≤ (48+82944/α)*t := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have h := physical_loss_bound ε y s hε hy α m t hα hm0 ht
  have hden : α ≤ α*m := by nlinarith
  have hq := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 82944) hα hden
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith :
    48+82944/(α*m) ≤ 48+82944/α) ht.1)

theorem actual_loss_bound (α m : ℝ) (hα : 0 < α) (hm : 1 ≤ m) :
    loss α m (fraction ε s) r ≤ (48+82944/α)*fraction ε s := by
  have ht := fraction_bounds ε s hε
  exact physical_loss_width_uniform ε y s hε hy α m (fraction ε s) hα hm ⟨ht.1.le,ht.2.le⟩

#print axioms scalar_loss_bound
#print axioms loss_normalized
#print axioms loss_zero
#print axioms physical_loss_bound
#print axioms physical_loss_width_uniform
#print axioms actual_loss_bound
end
end UnifiedTheory.Audit.KFCausalTwoWidthPhysicalClockLoss
