/- An explicit flat SU(2) orbit fixed by the center seam. Its full physical
contrast vanishes, so the earlier pointwise positive rate floor does not
hold for the actual contrast moment. No uniform neighborhood mass follows. -/
import UnifiedTheory.Clay.YangMills.WilsonContrastMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist WilsonCenterContrast
open WilsonContrastMoment
open scoped Quaternion

def axisI : Q := ⟨(⟨0,1,0,0⟩ : ℍ), by
  constructor
  · rw [Quaternion.star_mul_self]
    norm_num [Quaternion.normSq_def]
  · rw [Quaternion.self_mul_star]
    norm_num [Quaternion.normSq_def]⟩

def axisJ : Q := ⟨(⟨0,0,1,0⟩ : ℍ), by
  constructor
  · rw [Quaternion.star_mul_self]
    norm_num [Quaternion.normSq_def]
  · rw [Quaternion.self_mul_star]
    norm_num [Quaternion.normSq_def]⟩

theorem conjugate_axis : axisJ * axisI * axisJ⁻¹ = -axisI := by
  apply Subtype.ext
  change (axisJ : ℍ) * (axisI : ℍ) * star (axisJ : ℍ) = -(axisI : ℍ)
  ext <;> norm_num [axisI, axisJ]

variable (n : ℕ) [NeZero n]

def fixed (i : Fin 3) : Slice n := WilsonWindingLoop.seam n i axisI

omit [NeZero n] in
theorem fixed_flat (i : Fin 3) (x : SpatialVertex n) (j k : Fin 3) :
    spatialHolonomy (fixed n i) x j k = 1 := WilsonWindingLoop.seam_flat n i axisI x j k

omit [NeZero n] in
theorem fixed_twist_gauge (i : Fin 3) :
    twist n i (fixed n i) = gaugeSlice (fun _ => axisJ) (fixed n i) := by
  funext e
  simp only [twist_apply, fixed, WilsonWindingLoop.seam, gaugeSlice]
  split_ifs <;> simp [conjugate_axis]

theorem contrast_zero (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (v : Slice n) :
    contrast n i β hβ (fixed n i) v = 0 := by
  rw [contrast, fixed_twist_gauge, WilsonPhysicalResponse.full_transition_gauge_left,
    sub_self, zero_div]

theorem moment_zero (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    moment n i β hβ (fixed n i) = 0 := by
  change (∫ v, _ ∂WilsonSlabOperator.measure n) = 0
  simp only [contrast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    MeasureTheory.integral_zero]

/-- The zero-moment region has genuine positive-ground-measure neighborhoods at finite cutoff. -/
theorem small_moment_positive (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0 < ε) :
    0 < WilsonGroundHeatBath.groundLaw n β hβ {u : Slice n | moment n i β hβ u < ε} := by
  letI := WilsonGroundVarianceBudget.ground_openPos n β hβ
  exact (isOpen_lt (moment n i β hβ).continuous continuous_const).measure_pos
    (WilsonGroundHeatBath.groundLaw n β hβ)
    ⟨fixed n i, by simpa only [Set.mem_setOf_eq, moment_zero] using hε⟩

/-- This refutes the old pointwise profile floor for the actual moment, not a global-rate floor. -/
theorem moment_below_base (i : Fin 3) (β : ℝ) (hβ : 0 < β) :
    moment n i β hβ.le (fixed n i) < WilsonSeamRateFloor.baseRate n β := by
  rw [moment_zero]
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hs : 1 < WilsonSeamRateFloor.baseScale n β :=
    Real.one_lt_exp_iff.mpr (by positivity)
  unfold WilsonSeamRateFloor.baseRate
  exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos (by linarith))

end
end UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit
