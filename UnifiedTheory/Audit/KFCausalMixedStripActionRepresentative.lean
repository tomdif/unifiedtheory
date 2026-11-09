/- The actual mixed-coordinate representative of a bounded strip action
at every horizontal line, including the half-step line. -/
import UnifiedTheory.Audit.KFCausalMixedStripTailAttachment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalMixedStripActionRepresentative
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint Block split split_preserves_volume)
open KFCausalEuclideanConfiguration (Space)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalPairedModeCoordinates (modeIsometry mode_preserves_volume)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalMixedStripTailAttachment (family tailPoint)
open KFCausalMixedStripExponentialGraph (action action_coe unitary_straightening_coe)

variable (ε : ℝ) (hε : 0 < ε) (G : ℂ → Joint 2 4 → ℂ) (d M : ℝ)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace =>
    family G ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖family G q z‖ ≤ M)
  (hG : ∀ q x, G q (tailPoint (tail x)) = G q (modeIsometry x))

include hG in
theorem action_clockMixed (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    clockMixed ε hε (action ε hε (family G) d M hC hM hB y hy f) =ᵐ[volume]
      fun x => G ((x.2 0:ℂ)+(y:ℂ)*Complex.I) ((split 2 4).symm x)*
        (clockMixed ε hε f) x := by
  have he : ∀ᵐ x : Space ∂volume,
      (clockMixed ε hε (action ε hε (family G) d M hC hM hB y hy f))
        (split 2 4 (modeIsometry x)) =
      G (((split 2 4 (modeIsometry x)).2 0:ℂ)+(y:ℂ)*Complex.I)
        (modeIsometry x)*(clockMixed ε hε f) (split 2 4 (modeIsometry x)) := by
    filter_upwards [action_coe ε hε (family G) d M hC hM hB y hy f,
      unitary_straightening_coe ε hε f,
      unitary_straightening_coe ε hε
        (action ε hε (family G) d M hC hM hB y hy f)] with x ha hf hg
    rw [hg,hf] at ha
    change _ = G ((x 0:ℂ)+(y:ℂ)*Complex.I) (tailPoint (tail x))*_ at ha
    rw [hG] at ha
    exact ha
  have hmode : MeasurePreserving modeIsometry.toMeasurableEquiv := mode_preserves_volume
  have hp := (hmode.symm.comp
    (split_preserves_volume 2 4).symm).quasiMeasurePreserving.ae he
  have heq (z : Joint 2 4) : modeIsometry (modeIsometry.toMeasurableEquiv.symm z)=z :=
    modeIsometry.apply_symm_apply z
  simpa only [Function.comp_apply,heq,LinearIsometryEquiv.apply_symm_apply,
    MeasurableEquiv.apply_symm_apply] using hp

#print axioms action_clockMixed
end
end UnifiedTheory.Audit.KFCausalMixedStripActionRepresentative
