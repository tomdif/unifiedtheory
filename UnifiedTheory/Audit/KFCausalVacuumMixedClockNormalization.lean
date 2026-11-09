/- Exact cancellation of the physical clock half-weight and the shifted
two-dimensional Gaussian Fourier normalization in a vacuum-square output.
This scalar identity applies to either paired Fourier convention; their
remaining transverse quadratics must still be identified separately. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalVacuumMixedClockNormalization
noncomputable section
open KFCausalClockFloorRelativeShift (inverse relative scale argument)
open KFCausalClockFloorShearBounds (complexScale complexScale_square)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorFullGaussian (clockFactor)

def inverseHalf (ε s : ℝ) : ℂ := (Real.sqrt (Real.exp s+ε):ℂ)⁻¹

def normalizedClock (ε a p y s : ℝ) : ℂ :=
  Complex.exp (-inverse ε y s)*clockPhase p (inverse ε y s)*clockFactor a (argument ε y s)

theorem scale_square (ε y s : ℝ) :
    (scale ε y s)^2=Complex.exp (inverse ε y s-(s:ℂ)) :=
  complexScale_square _

theorem exp_clock_cancel (ε y s : ℝ) :
    (Real.exp (-s):ℂ)/(scale ε y s)^2=Complex.exp (-inverse ε y s) := by
  rw [scale_square,Complex.ofReal_exp,div_eq_mul_inv,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem clock_normalization (ε a p y s : ℝ) (hε : 0 < ε) :
    inverseHalf ε s*clockAmplitude ε a p y s/(scale ε y s)^2 = normalizedClock ε a p y s := by
  have hs : (Real.sqrt (Real.exp s+ε):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold inverseHalf clockAmplitude KFCausalClockFloorChargeTrialBridge.amplitude normalizedClock
  rw [Complex.ofReal_mul]
  calc
    _ = ((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*(Real.sqrt (Real.exp s+ε):ℂ))*
        ((Real.exp (-s):ℂ)/(scale ε y s)^2)*
        clockPhase p (inverse ε y s)*clockFactor a (argument ε y s) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hs,one_mul,exp_clock_cancel]

theorem fourier_normalization (ε a p y s α : ℝ) (hε : 0 < ε) :
    inverseHalf ε s*clockAmplitude ε a p y s*((Real.pi:ℂ)/((α:ℂ)*(scale ε y s)^2)) =
      ((Real.pi:ℂ)/(α:ℂ))*normalizedClock ε a p y s := by
  calc
    _ = ((Real.pi:ℂ)/(α:ℂ))*
        (inverseHalf ε s*clockAmplitude ε a p y s/(scale ε y s)^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [clock_normalization ε a p y s hε]

theorem narrow_fourier_normalization (ε a p y s α w : ℝ) (hε : 0 < ε) :
    inverseHalf ε s*clockAmplitude ε a p y s*
        (((Real.pi:ℂ)/((α:ℂ)*(scale ε y s)^2))*(w:ℂ)) =
      (((Real.pi:ℂ)*(w:ℂ))/(α:ℂ))*normalizedClock ε a p y s := by
  rw [← mul_assoc,fourier_normalization ε a p y s α hε]
  ring

#print axioms scale_square
#print axioms exp_clock_cancel
#print axioms clock_normalization
#print axioms fourier_normalization
#print axioms narrow_fourier_normalization
end
end UnifiedTheory.Audit.KFCausalVacuumMixedClockNormalization
