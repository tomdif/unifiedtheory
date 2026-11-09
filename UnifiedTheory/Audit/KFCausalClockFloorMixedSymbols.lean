/- Explicit real symbols for the actual heat factor and radial test in
clock-straightened mixed coordinates. Frequencies retain the physical
2*pi*hbar normalization, and the clock is the inverse chart value. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart (backward changeClock flow)
open UnifiedTheory.Audit.KFCausalClockFloorMixedChart
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)

variable (ε : ℝ) (hε : 0 < ε)

theorem dilation_square (y : Block 4) : (dilation ε hε y)^2 = Real.exp (clockInverse ε hε y) := by
  rw [dilation,pow_two,← Real.exp_add]
  congr 1
  ring

theorem inverse_dilation_square (y : Block 4) : ((dilation ε hε y)⁻¹)^2 = Real.exp (-clockInverse ε hε y) := by
  rw [dilation,← Real.exp_neg,pow_two,← Real.exp_add]
  congr 1
  ring

theorem heat_symbol (h δ : ℝ) (x : Block 2 × Block 4) :
    heatSymbol h δ ((split 2 4).symm (mixedMap ε hε x)) =
      (Real.exp (-2*δ*Real.exp (-clockInverse ε hε x.2)*(momentumScale h*x.1 1)^2):ℂ) := by
  change (Real.exp (-2*δ*(momentumScale h*((dilation ε hε x.2)⁻¹*x.1 1))^2):ℂ) = _
  rw [show -2*δ*(momentumScale h*((dilation ε hε x.2)⁻¹*x.1 1))^2 =
    -2*δ*((dilation ε hε x.2)⁻¹)^2*(momentumScale h*x.1 1)^2 by ring,
    inverse_dilation_square]

theorem radial_symbol (h δ v : ℝ) (x : Block 2 × Block 4) :
    symbol h δ v ((split 2 4).symm (mixedMap ε hε x)) =
      (Real.exp (-2*δ*(Real.exp (-clockInverse ε hε x.2)*(momentumScale h*x.1 1)^2+
        Real.exp (clockInverse ε hε x.2)*(x.2 2)^2)):ℂ)*
      scalar (v*(x.2 3+4*scale*(dilation ε hε x.2-1)*x.2 2)) := by
  change (Real.exp (-2*δ*((momentumScale h*((dilation ε hε x.2)⁻¹*x.1 1))^2+
    (dilation ε hε x.2*x.2 2)^2)):ℂ)*
    scalar (v*(x.2 3+4*scale*(dilation ε hε x.2-1)*x.2 2)) = _
  rw [show (momentumScale h*((dilation ε hε x.2)⁻¹*x.1 1))^2+
    (dilation ε hε x.2*x.2 2)^2 =
    ((dilation ε hε x.2)⁻¹)^2*(momentumScale h*x.1 1)^2+(dilation ε hε x.2)^2*(x.2 2)^2 by ring,
    inverse_dilation_square,dilation_square]

#print axioms dilation_square
#print axioms inverse_dilation_square
#print axioms heat_symbol
#print axioms radial_symbol

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols
