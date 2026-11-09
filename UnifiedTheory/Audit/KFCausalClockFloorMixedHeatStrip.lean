/- The actual transformed heat multiplier has a bounded analytic
continuation to the clock strip. The real-slice identification is proved
from the physical whole-L2 coordinate theorem. This alone does not assert
preservation of the longitudinal exponential graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols
import UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block split)
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorMixedChart (mixedMap)
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadial (clockMixed heat_transformed)
open UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols (heat_symbol)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (heat heatSymbol)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)

def heatFactor (δ p : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-2*δ:ℝ)*Complex.exp (-z)*(p:ℂ)^2)

theorem heatFactor_analytic (δ p : ℝ) (z : ℂ) : AnalyticAt ℂ (heatFactor δ p) z := by
  unfold heatFactor
  fun_prop

theorem heatFactor_norm (δ p : ℝ) (z : ℂ) :
    ‖heatFactor δ p z‖ = Real.exp (-2*δ*(Complex.exp (-z)).re*p^2) := by
  rw [heatFactor,Complex.norm_exp]
  congr 1
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]

theorem heatFactor_bound (δ p : ℝ) (hδ : 0 ≤ δ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    ‖heatFactor δ p z‖ ≤ 1 := by
  have he : 0 ≤ (Complex.exp (-z)).re := by
    rw [Complex.exp_re,Complex.neg_im,Real.cos_neg]
    exact mul_nonneg (Real.exp_pos _).le (by linarith [cos_lower_third z.im hz])
  rw [heatFactor_norm]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) he) (sq_nonneg p)

theorem heatFactor_real (δ p s : ℝ) :
    heatFactor δ p (s:ℂ) = (Real.exp (-2*δ*Real.exp (-s)*p^2):ℂ) := by
  simp only [heatFactor,← Complex.ofReal_neg,← Complex.ofReal_exp,
    ← Complex.ofReal_pow,← Complex.ofReal_mul]

def multiplier (ε δ p : ℝ) (q : ℂ) : ℂ := heatFactor δ p (complexInverse ε q)

theorem multiplier_analytic (ε δ p : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (multiplier ε δ p) q :=
  (heatFactor_analytic δ p _).comp (complexInverse_analytic ε hε q hq)

theorem multiplier_bound (ε δ p : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : ‖multiplier ε δ p q‖ ≤ 1 :=
  heatFactor_bound δ p hδ _ (inverse_im_third_strip ε hε q hq)

theorem multiplier_real (ε h δ : ℝ) (hε : 0 < ε) (x : Block 2 × Block 4) :
    multiplier ε δ (momentumScale h*x.1 1) (x.2 0:ℂ) =
      heatSymbol h δ ((split 2 4).symm (mixedMap ε hε x)) := by
  rw [multiplier,complexInverse_real ε hε,heatFactor_real,heat_symbol]
  rfl

theorem heat_transformed_analytic (ε h δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    clockMixed ε hε (heat h δ hδ f) =ᵐ[volume] fun x =>
      multiplier ε δ (momentumScale h*x.1 1) (x.2 0:ℂ)*(clockMixed ε hε f) x := by
  simpa only [multiplier_real ε h δ hε] using heat_transformed ε hε h δ hδ f

#print axioms heatFactor_analytic
#print axioms heatFactor_norm
#print axioms heatFactor_bound
#print axioms heatFactor_real
#print axioms multiplier_analytic
#print axioms multiplier_bound
#print axioms multiplier_real
#print axioms heat_transformed_analytic

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip
