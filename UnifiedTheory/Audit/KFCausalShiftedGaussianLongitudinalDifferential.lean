/- The actual shifted Gaussian's longitudinal differential. The coordinate
density terms cancel; the remaining terms are its clock moment and a
bounded inverse-clock multiplier times its transverse Gaussian slope. -/
import UnifiedTheory.Audit.KFCausalRelativeGaussianClockDerivative
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
import UnifiedTheory.Audit.KFCausalClockFloorComplexDefectDerivative
import UnifiedTheory.Audit.KFCausalRadialStripGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (complexClock complexClock_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (amplitude)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (amplitudeLogSlope amplitude_derivative rate rate_identity)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile slope)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential)

def inverseClock (ε y s : ℝ) : ℂ := (complexClock ε (argument ε y s))⁻¹
def amplitudeSlope (ε a p y s : ℝ) : ℂ :=
  (amplitudeLogSlope ε s:ℂ)+(p:ℂ)*Complex.I*((Real.exp s+ε:ℝ):ℂ)*inverseClock ε y s-
    2*(a:ℂ)*argument ε y s*((Real.exp s+ε:ℝ):ℂ)

theorem inverseClock_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (inverseClock ε y) := by
  apply Continuous.inv₀
  · exact ((inverse_smooth ε y hε hy).continuous.cexp).add continuous_const
  · intro s
    exact complexClock_ne_zero ε hε _ (argument_mem ε y s hε hy)

theorem inverseClock_bound (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ‖inverseClock ε y s‖ ≤ 1/ε := by
  have hd := KFCausalClockFloorComplexDefectDerivative.inverse_derivative ε hε _ (argument_mem ε y s hε hy)
  unfold inverseClock
  rw [← hd.deriv]
  apply KFCausalRadialStripGeometry.inverse_derivative_bound ε hε
  simpa [argument] using hy

theorem argument_derivative (ε y s : ℝ) :
    HasDerivAt (argument ε y) ((Real.exp s+ε:ℝ):ℂ) s :=
  (chart_derivative ε s).ofReal_comp.add_const ((y:ℂ)*Complex.I)

theorem inverse_derivative (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (inverse ε y) (((Real.exp s+ε:ℝ):ℂ)*inverseClock ε y s) s := by
  simpa only [Function.comp_def,smul_eq_mul] using
    (KFCausalClockFloorComplexDefectDerivative.inverse_derivative ε hε _
      (argument_mem ε y s hε hy)).scomp s (argument_derivative ε y s)

theorem scale_derivative (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (scale ε y)
      ((((Real.exp s+ε:ℝ):ℂ)*inverseClock ε y s-1)*scale ε y s/2) s := by
  have hd := (((inverse_derivative ε y s hε hy).sub (hasDerivAt_id s).ofReal_comp).div_const 2).cexp
  convert hd using 1
  simp only [Pi.sub_apply,id_eq,Complex.ofReal_one]
  unfold scale KFCausalClockFloorShearBounds.complexScale relative
  ring

theorem clockAmplitude_derivative (ε a p y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (clockAmplitude ε a p y)
      (amplitudeSlope ε a p y s*clockAmplitude ε a p y s) s := by
  have hp := ((inverse_derivative ε y s hε hy).const_mul ((p:ℂ)*Complex.I)).cexp
  have hg := (((argument_derivative ε y s).pow 2).const_mul (-(a:ℂ))).cexp
  have hd := ((amplitude_derivative ε s hε).ofReal_comp.mul hp).mul hg
  convert hd using 1
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Complex.ofReal_mul,Pi.mul_apply,Pi.pow_apply]
  unfold amplitudeSlope clockAmplitude clockPhase clockFactor
  ring

theorem density_cancellation (ε a p y s : ℝ) (hε : 0 < ε) :
    (rate ε s:ℂ)+((Real.exp s+ε:ℝ):ℂ)⁻¹*amplitudeSlope ε a p y s =
      (p:ℂ)*Complex.I*inverseClock ε y s-2*(a:ℂ)*argument ε y s := by
  have hc : ((Real.exp s+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [← rate_identity ε s hε]
  simp only [amplitudeSlope,Complex.ofReal_div,Complex.ofReal_neg]
  field_simp
  ring

theorem profile_differential (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    differential ε (profile (clockAmplitude ε a p y) (scale ε y) α β b) x =
      ((p:ℂ)*Complex.I*inverseClock ε y x.1-2*(a:ℂ)*argument ε y x.1)*
        profile (clockAmplitude ε a p y) (scale ε y) α β b x+
      inverseClock ε y x.1*(slope (scale ε y) α β b x*
        profile (clockAmplitude ε a p y) (scale ε y) α β b x) := by
  have he := KFCausalRelativeGaussianClockDerivative.longitudinal_differential ε _ _
    (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy) α β b x
    (amplitudeSlope ε a p y x.1) (((Real.exp x.1+ε:ℝ):ℂ)*inverseClock ε y x.1-1)
    (clockAmplitude_derivative ε a p y x.1 hε hy) (scale_derivative ε y x.1 hε hy)
  simp only [← Complex.ofReal_add] at he
  rw [he,density_cancellation ε a p y x.1 hε]
  have hc : ((Real.exp x.1+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [sub_add_cancel,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

#print axioms inverseClock_continuous
#print axioms inverseClock_bound
#print axioms argument_derivative
#print axioms inverse_derivative
#print axioms scale_derivative
#print axioms clockAmplitude_derivative
#print axioms density_cancellation
#print axioms profile_differential
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
