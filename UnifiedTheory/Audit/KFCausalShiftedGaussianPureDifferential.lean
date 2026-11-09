/- The actual pure-clock differential of a shifted Gaussian retains the
half-density correction. Its transverse coefficient has polynomial growth. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianRadialMoments
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianPureDifferential
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open KFCausalRelativeGaussianDifferential (profile slope position direction)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)

def realInverse (ε s : ℝ) : ℂ := ((Real.exp s+ε:ℝ):ℂ)⁻¹

theorem realInverse_controlled (ε : ℝ) (hε : 0 < ε) : Controlled (fun x => realInverse ε x.1) := by
  have hc : Continuous (realInverse ε) := by
    unfold realInverse
    fun_prop (disch := intro s; exact Complex.ofReal_ne_zero.mpr (by positivity))
  apply controlled_clock _ hc (1/ε) (by positivity)
  intro s
  simp only [realInverse,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < Real.exp s+ε by positivity)]
  simpa only [one_div] using one_div_le_one_div_of_le hε
    (show ε ≤ Real.exp s+ε by linarith [Real.exp_pos s])

theorem inverseClock_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Controlled (fun x => inverseClock ε y x.1) :=
  controlled_clock _ (KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy)
    (1/ε) (by positivity) (fun s => KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_bound ε y s hε hy)

theorem scale_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Controlled (fun x => scale ε y x.1) :=
  controlled_clock _ (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).continuous
    (Real.exp (|y|/(2*ε))) (Real.exp_pos _).le
      (fun s => KFCausalClockFloorRelativeShift.scale_bound ε y s hε hy)

theorem position_controlled (r : ℝ → ℂ) (hr : Controlled (fun x => r x.1)) (i : Fin 5) :
    Controlled (fun x => position (r x.1) x.2 i) := by
  by_cases hi : i=4
  · subst i
    exact controlled_add _ _ (controlled_coordinate 4)
      (controlled_mul _ _
        (controlled_mul _ _ (controlled_const 2) (controlled_sub _ _ hr (controlled_const 1)))
        (controlled_add _ _ (controlled_coordinate 2) (controlled_coordinate 3)))
  · simpa only [position,if_neg hi] using controlled_mul _ _ hr (controlled_coordinate i)

theorem direction_controlled (r : ℝ → ℂ) (hr : Controlled (fun x => r x.1)) (i : Fin 5) :
    Controlled (fun x => direction (r x.1) x.2 i) := by
  by_cases hi : i=4
  · subst i
    exact controlled_mul _ _ hr (controlled_add _ _ (controlled_coordinate 2) (controlled_coordinate 3))
  · simpa only [direction,if_neg hi,div_eq_mul_inv] using
      controlled_mul _ _ (controlled_mul _ _ hr (controlled_coordinate i)) (controlled_const (2:ℂ)⁻¹)

theorem slope_controlled (r : ℝ → ℂ) (hr : Controlled (fun x => r x.1)) (α β : ℝ) (b : Fin 5 → ℂ) :
    Controlled (slope r α β b) := by
  apply controlled_sum Finset.univ
  intro i _
  exact controlled_mul _ _ (controlled_sub _ _ (controlled_const (b i))
    (controlled_mul _ _ (controlled_const (2*(KFCausalPhysicalGaussianMoments.widths α β i:ℂ)))
      (position_controlled r hr i))) (direction_controlled r hr i)

theorem pure_differential (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    KFCausalClockFloorPureClockDerivative.differential ε
      (profile (clockAmplitude ε a p y) (scale ε y) α β b) x =
      ((p:ℂ)*Complex.I*inverseClock ε y x.1-2*(a:ℂ)*KFCausalClockFloorRelativeShift.argument ε y x.1-
        realInverse ε x.1)*profile (clockAmplitude ε a p y) (scale ε y) α β b x+
      (inverseClock ε y x.1-realInverse ε x.1)*
        (slope (scale ε y) α β b x*profile (clockAmplitude ε a p y) (scale ε y) α β b x) := by
  let F := profile (clockAmplitude ε a p y) (scale ε y) α β b
  have hs := KFCausalRelativeGaussianDifferential.profile_shear _ _ (clockAmplitude_smooth ε a p y hε hy)
    (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy) α β b x
  have he := KFCausalClockFloorPureClockDerivative.longitudinal_split ε F x
  change KFCausalClockFloorDifferentialMomentum.differential ε F x =
    KFCausalClockFloorPureClockDerivative.differential ε F x+realInverse ε x.1*
      KFCausalClockFloorCanonicalReconstruction.shearDerivative F x at he
  rw [KFCausalShiftedGaussianLongitudinalDifferential.profile_differential ε a α β p y b hε hy,hs] at he
  change KFCausalClockFloorPureClockDerivative.differential ε F x = _
  linear_combination -he

#print axioms realInverse_controlled
#print axioms inverseClock_controlled
#print axioms scale_controlled
#print axioms position_controlled
#print axioms direction_controlled
#print axioms slope_controlled
#print axioms pure_differential
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianPureDifferential
