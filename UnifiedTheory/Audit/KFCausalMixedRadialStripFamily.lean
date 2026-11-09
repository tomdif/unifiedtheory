/- The actual radial strip multiplier expressed in the Euclidean clock
and five transverse coordinates required by the natural exponential graph
theorem. Analyticity, joint slice continuity and all bounds are derived. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace tail)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block split)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale modeIsometry)
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip (multiplier factor grouped)
open UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip (heatFactor)
open UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase (localized phase)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (mix complexScale)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (neutral)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset inverse_line_continuous)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (stripBound)

def mixedTail (z : TailSpace) : Block 2 × Block 4 :=
  (WithLp.toLp 2 ![0,scale*(z 2-z 3)],WithLp.toLp 2 ![0,0,scale*(z 2+z 3),z 4])

def family (ε h δ v : ℝ) (q : ℂ) (z : TailSpace) : ℂ := multiplier ε h δ v q (mixedTail z)

theorem family_analytic (ε h δ v : ℝ) (hε : 0 < ε) (z : TailSpace) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : AnalyticAt ℂ (fun q => family ε h δ v q z) q :=
  KFCausalClockFloorMixedRadialStrip.multiplier_analytic ε h δ v hε q (third_strip_subset ε hε q hq) _

theorem family_line_continuous (ε h δ v : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (fun w : ℝ × TailSpace => family ε h δ v ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2) := by
  have hi := (inverse_line_continuous ε y hε hy).comp (continuous_fst (Y := TailSpace))
  dsimp [family,multiplier,factor,heatFactor,localized,phase,neutral,complexScale,mix,grouped,mixedTail]
  fun_prop

theorem family_bound (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) (z : TailSpace) : ‖family ε h δ v q z‖ ≤ stripBound ε δ v := by
  apply (KFCausalClockFloorMixedRadialStrip.multiplier_bound ε h δ v hε hδ q hq _).trans
  apply Real.exp_le_exp.mpr
  have hs := pow_le_pow_left₀ (abs_nonneg _) hq 2
  rw [sq_abs] at hs
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg v)) (by positivity)

theorem family_symbol (ε h δ v y : ℝ) (x : Space) :
    KFCausalStripFamilyExponentialGraph.symbol (family ε h δ v) y x =
      multiplier ε h δ v ((x 0:ℂ)+(y:ℂ)*Complex.I) (split 2 4 (modeIsometry x)) := rfl

theorem family_slice_bound (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) (x : Space) :
    ‖KFCausalStripFamilyExponentialGraph.symbol (family ε h δ v) y x‖ ≤
      Real.exp (v^2*y^2/(2*δ*ε^2)) := by
  rw [family_symbol]
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
    KFCausalClockFloorMixedRadialStrip.multiplier_bound ε h δ v hε hδ
      ((x 0:ℂ)+(y:ℂ)*Complex.I) (by simpa using hy) (split 2 4 (modeIsometry x))

#print axioms family_analytic
#print axioms family_line_continuous
#print axioms family_bound
#print axioms family_symbol
#print axioms family_slice_bound

end
end UnifiedTheory.Audit.KFCausalMixedRadialStripFamily
