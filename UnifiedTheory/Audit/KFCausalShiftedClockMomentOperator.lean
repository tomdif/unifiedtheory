/- Bounded clock operators representing the inverse shifted clock and a
Gaussian-damped clock moment. The moment of the actual shifted state is
obtained from the same state family with half the clock Gaussian width. -/
import UnifiedTheory.Audit.KFCausalGaussianClockMoment
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
import UnifiedTheory.Audit.KFCausalBoundedClockCharge
import UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument argument_smooth scale)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude gaussianState_profile)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState shiftedOutput)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
open UnifiedTheory.Audit.KFCausalGaussianClockMoment (bound bound_positive moment_bound profile_factor)
open UnifiedTheory.Audit.KFCausalBoundedClockCharge (multiplier multiplier_coe)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

def inverseOperator (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  multiplier (inverseClock ε y) (inverseClock_continuous ε y hε hy).measurable
    (1/ε) (by positivity) (fun s => inverseClock_bound ε y s hε hy)

theorem inverseOperator_coe (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    inverseOperator ε y hε hy f =ᵐ[volume] fun x => inverseClock ε y x.1*f x :=
  multiplier_coe _ _ _ _ _ f

def momentMultiplier (ε a y s : ℝ) : ℂ := argument ε y s*clockFactor (a/2) (argument ε y s)

theorem momentMultiplier_continuous (ε a y : ℝ) : Continuous (momentMultiplier ε a y) := by
  unfold momentMultiplier clockFactor
  exact (argument_smooth ε y).continuous.mul
    ((continuous_const.mul ((argument_smooth ε y).continuous.pow 2)).cexp)

def momentOperator (ε a y : ℝ) (ha : 0 < a) : Hilbert →L[ℂ] Hilbert :=
  multiplier (momentMultiplier ε a y) (momentMultiplier_continuous ε a y).measurable
    (bound a y) (bound_positive a y ha).le (fun s => moment_bound a (chart ε s) y ha)

theorem momentOperator_coe (ε a y : ℝ) (ha : 0 < a) (f : Hilbert) :
    momentOperator ε a y ha f =ᵐ[volume] fun x => momentMultiplier ε a y x.1*f x :=
  multiplier_coe _ _ _ _ _ f

theorem gaussian_moment_coe (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) :
    momentOperator ε a y ha (gaussianState ε (a/2) α β p b y hε (by positivity) hα hβ hw hy)
      =ᵐ[volume] fun x => argument ε y x.1*profile (clockAmplitude ε a p y) (scale ε y) α β b x := by
  filter_upwards [momentOperator_coe ε a y ha
      (gaussianState ε (a/2) α β p b y hε (by positivity) hα hβ hw hy),
    gaussianState_profile ε (a/2) α β p y b hε (by positivity) hα hβ hw hy] with x hm hf
  rw [hm,hf,profile_factor ε a α β p y b x]
  simp only [momentMultiplier,mul_assoc]

def shiftedMoment (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) : Hilbert :=
  momentOperator ε a (-h/2) ha (shiftedOutput ε (a/2) h hε (by positivity) hh hb k)

theorem shiftedMoment_orbit_continuous (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    Continuous (fun θ => shiftedMoment ε a h hε ha hh hb (parameter θ k)) :=
  (momentOperator ε a (-h/2) ha).continuous.comp
    (KFCausalClockFloorCoherentShiftedOrbit.shiftedOutput_orbit_continuous ε (a/2) h hε
      (by positivity) hh hb k)

theorem shiftedMoment_orbit_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    MemLp (fun θ => shiftedMoment ε a h hε ha hh hb (parameter (2*Real.pi*θ) k)) 2
      KFCausalUnitIntervalOrbit.angleMeasure :=
  KFCausalClockFloorCoherentOrbitContinuity.continuous_angle_memLp _
    ((shiftedMoment_orbit_continuous ε a h hε ha hh hb k).comp (continuous_const.mul continuous_id))

#print axioms inverseOperator_coe
#print axioms momentMultiplier_continuous
#print axioms momentOperator_coe
#print axioms gaussian_moment_coe
#print axioms shiftedMoment_orbit_continuous
#print axioms shiftedMoment_orbit_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
