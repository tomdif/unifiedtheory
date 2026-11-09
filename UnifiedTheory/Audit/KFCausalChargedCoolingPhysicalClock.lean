/- The actual clock cooling rate acts dissipatively on every fixed-v charged Gram form. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingDerivative
import UnifiedTheory.Audit.KFCausalJointFourierDissipationClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalClock
noncomputable section
open Matrix
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingDerivative KFCausalChargedCoolingFixedV
open KFCausalChargedCoolingActualPhase
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalJointClockCoolingCoercivity (imaginaryRate)

def coolingRate (ε y s : ℝ) : ℝ :=
  (deriv (scale ε y) s).re-imaginaryRate (fraction ε s) (scale ε y s)*(scale ε y s).re

theorem coolingRate_positive (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    0 < coolingRate ε y s := by
  unfold coolingRate
  rw [(actual_normalized_velocity ε y s hε hy).deriv]
  exact KFCausalJointFourierDissipationClock.actual_real_cooling_positive ε y s hε hy

variable {n : Type*} [Fintype n]

theorem rate_form_derivative (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v δ : ℝ) (c : n → ℂ) :
    HasDerivAt (fun t : ℝ => form ((α:ℂ)*(r+((δ*t:ℝ):ℂ))^2/2) w v c)
      (δ • (-(star c ⬝ᵥ ((fun i j => KFCausalChargedCoolingFixedV.dissipation
        ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j) v) *ᵥ c)))) 0 := by
  have h := (actual_form_derivative α r hα hr w hw v c).scomp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_mul δ) (by simp)
  simpa only [Function.comp_def,id_eq,mul_one] using h

theorem rate_form_derivative_nonpositive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (v δ : ℝ) (hδ : 0 ≤ δ) (c : n → ℂ) :
    (deriv (fun t : ℝ => form ((α:ℂ)*(r+((δ*t:ℝ):ℂ))^2/2) w v c) 0).re ≤ 0 := by
  rw [(rate_form_derivative α r hα hr w hw v δ c).deriv]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,zero_mul,sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos hδ
    (neg_nonpos.mpr (actual_dissipation_form_nonnegative α r hα hr w hw v c))

theorem physical_form_derivative_nonpositive (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    (deriv (fun t : ℝ => form ((α:ℂ)*
      (scale ε y s+((coolingRate ε y s*t:ℝ):ℂ))^2/2) w v c) 0).re ≤ 0 :=
  rate_form_derivative_nonpositive α _ hα (actual_sector ε y s hε hy) w hw v _
    (coolingRate_positive ε y s hε hy).le c

/-- The conjugated scale gives the original atom norm orientation. -/
theorem physical_conjugate_form_derivative_nonpositive (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) (c : n → ℂ) :
    (deriv (fun t : ℝ => form ((α:ℂ)*
      (starRingEnd ℂ (scale ε y s)+((coolingRate ε y s*t:ℝ):ℂ))^2/2) w v c) 0).re ≤ 0 := by
  apply rate_form_derivative_nonpositive α _ hα _ w hw v _
    (coolingRate_positive ε y s hε hy).le c
  simpa only [Complex.conj_re,Complex.conj_im,abs_neg] using actual_sector ε y s hε hy

#print axioms coolingRate_positive
#print axioms rate_form_derivative
#print axioms rate_form_derivative_nonpositive
#print axioms physical_form_derivative_nonpositive
#print axioms physical_conjugate_form_derivative_nonpositive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalClock
