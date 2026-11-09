/- A clock-coordinate-independent O(abs(hbar)) bound for the actual
relative complex scale. Restricting to small hbar gives an explicit bound
instead of a fixed-hbar source estimate. -/
import UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedUniformShift
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
open UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale)

def scaleBound (ε : ℝ) : ℝ := 1/(2*ε)

theorem scaleBound_positive (ε : ℝ) (hε : 0 < ε) : 0 < scaleBound ε := by
  unfold scaleBound
  positivity

theorem relativeScale_bound (ε q h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) :
    ‖relativeScale ε q h-1‖ ≤ scaleBound ε*|h| := by
  have hd := inverseShift_difference_bound ε q h hε hb
  have hn : ‖(inverseShift ε q h-inverseShift ε q 0)/2‖ ≤ |h|/(4*ε) := by
    rw [norm_div,show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    exact (div_le_div_of_nonneg_right hd (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hs : |h|/(4*ε) ≤ 1 := (div_le_one (by positivity)).mpr hsmall
  have he := Complex.norm_exp_sub_one_le (hn.trans hs)
  change ‖Complex.exp ((inverseShift ε q h-inverseShift ε q 0)/2)-1‖ ≤ _
  apply he.trans
  calc
    2*‖(inverseShift ε q h-inverseShift ε q 0)/2‖ ≤ 2*(|h|/(4*ε)) := by linarith
    _ = scaleBound ε*|h| := by unfold scaleBound; ring

theorem scaledDeviation_bound (ε q h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) :
    ‖scaledDeviation ε q h‖ ≤ scaleBound ε*scale h := by
  rw [scaledDeviation,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ scale h from Real.sqrt_nonneg _)]
  have ht := div_le_div_of_nonneg_right (relativeScale_bound ε q h hε hb hsmall)
    (show 0 ≤ scale h from Real.sqrt_nonneg _)
  simpa only [mul_div_assoc,scale,Real.div_sqrt] using ht

theorem relativeScale_slope_bound (ε q h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (hsmall : |h| ≤ 4*ε) :
    ‖(h:ℂ)⁻¹*(relativeScale ε q h-1)‖ ≤ scaleBound ε := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs]
  have ht := mul_le_mul_of_nonneg_left (relativeScale_bound ε q h hε hb hsmall)
    (inv_nonneg.mpr (abs_nonneg h))
  exact ht.trans_eq (by field_simp [abs_ne_zero.mpr hh])

theorem small_coefficient (ε h : ℝ) (hε : 0 < ε) (hsmall : |h| ≤ ε/2) :
    4*(scaleBound ε)^2*|h|^2 ≤ 1/4 := by
  have he : 4*(scaleBound ε)^2*|h|^2 = (|h|/ε)^2 := by unfold scaleBound; ring
  rw [he]
  have hb : |h|/ε ≤ 1/2 := (div_le_iff₀ hε).mpr (by linarith)
  have hn : 0 ≤ |h|/ε := by positivity
  nlinarith

#print axioms scaleBound_positive
#print axioms relativeScale_bound
#print axioms scaledDeviation_bound
#print axioms relativeScale_slope_bound
#print axioms small_coefficient

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedUniformShift
