/- Radius and shear estimates for the actual clock-straightened radial
multiplier. These supply the hypotheses of the dyadic cancellation
estimate from the existing analytic inverse, without a state-tail or
negative-clock-momentum assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip
import UnifiedTheory.Audit.KFCausalDyadicOscillatoryHeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalRadialStripGeometry
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (complexScale complexScale_norm_square)
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds (cos_lower_third)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)

def radius (p s : ℝ) (z : ℂ) : ℂ := Complex.exp (-z)*(p:ℂ)^2+Complex.exp z*(s:ℂ)^2
def radiusSlope (p s : ℝ) (z : ℂ) : ℂ := -Complex.exp (-z)*(p:ℂ)^2+Complex.exp z*(s:ℂ)^2
def shear (s : ℝ) (z : ℂ) : ℂ := (scale:ℂ)*complexScale z*(s:ℂ)
def phase (s r : ℝ) (z : ℂ) : ℂ := ((r-4*scale*s:ℝ):ℂ)+4*shear s z

theorem radius_re (p s : ℝ) (z : ℂ) :
    (radius p s z).re = (Real.exp (-z.re)*p^2+Real.exp z.re*s^2)*Real.cos z.im := by
  simp only [radius,Complex.add_re,Complex.mul_re,← Complex.ofReal_pow,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.exp_re,
    Complex.neg_re,Complex.neg_im,Real.cos_neg]
  ring

theorem radius_lower (p s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    (Real.exp (-z.re)*p^2+Real.exp z.re*s^2)/2 ≤ (radius p s z).re := by
  rw [radius_re]
  have hc := mul_le_mul_of_nonneg_left (cos_lower_third z.im hz)
    (show 0 ≤ Real.exp (-z.re)*p^2+Real.exp z.re*s^2 by positivity)
  linarith

theorem radius_nonneg (p s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    0 ≤ (radius p s z).re := (by positivity :
      0 ≤ (Real.exp (-z.re)*p^2+Real.exp z.re*s^2)/2).trans (radius_lower p s z hz)

theorem radius_derivative (p s : ℝ) (z : ℂ) : HasDerivAt (radius p s) (radiusSlope p s z) z := by
  simpa only [radius,radiusSlope,mul_neg_one] using
    (((hasDerivAt_id z).neg.cexp).mul_const ((p:ℂ)^2)).add ((Complex.hasDerivAt_exp z).mul_const ((s:ℂ)^2))

theorem radius_slope_bound (p s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    ‖radiusSlope p s z‖ ≤ 2*(radius p s z).re := by
  have hn : ‖radiusSlope p s z‖ ≤ Real.exp (-z.re)*p^2+Real.exp z.re*s^2 := by
    apply (norm_add_le _ _).trans_eq
    simp only [norm_mul,norm_neg,Complex.norm_exp,Complex.neg_re,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
  linarith [radius_lower p s z hz]

theorem shear_square (s : ℝ) (z : ℂ) : ‖shear s z‖^2 = Real.exp z.re*s^2/2 := by
  rw [shear,norm_mul,norm_mul,mul_pow,mul_pow,complexScale_norm_square,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.norm_real,Real.norm_eq_abs,sq_abs,scale_square]
  ring

theorem shear_bound (p s : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    ‖shear s z‖ ≤ Real.sqrt (radius p s z).re := by
  have hs := Real.sq_sqrt (radius_nonneg p s z hz)
  have hq := shear_square s z
  have he := radius_lower p s z hz
  nlinarith [norm_nonneg (shear s z),Real.sqrt_nonneg (radius p s z).re,
    mul_nonneg (Real.exp_pos (-z.re)).le (sq_nonneg p)]

theorem phase_im_bound (p s r : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    |(phase s r z).im| ≤ 4*Real.sqrt (radius p s z).re := by
  have hi := (Complex.abs_im_le_norm (shear s z)).trans (shear_bound p s z hz)
  have he : (phase s r z).im = 4*(shear s z).im := by simp [phase,Complex.mul_im]
  rw [he,abs_mul]
  norm_num
  linarith

theorem phase_derivative (s r : ℝ) (z : ℂ) : HasDerivAt (phase s r) (2*shear s z) z := by
  have hs : HasDerivAt (shear s) (shear s z/2) z := by
    convert ((((hasDerivAt_id z).div_const 2).cexp).const_mul (scale:ℂ)).mul_const (s:ℂ) using 1
    dsimp [shear,complexScale]
    ring
  convert (hs.const_mul 4).const_add ((r-4*scale*s:ℝ):ℂ) using 1
  dsimp [phase]
  ring

theorem factor_packet (δ v p s r : ℝ) (z : ℂ) :
    KFCausalClockFloorMixedRadialStrip.factor δ v p s r z =
      KFCausalDyadicOscillatoryHeat.packet δ v (radius p s z) (phase s r z) := by
  unfold KFCausalClockFloorMixedRadialStrip.factor KFCausalClockFloorMixedHeatStrip.heatFactor
    KFCausalNeutralPositionStripPhase.localized KFCausalNeutralPositionStripPhase.phase
    KFCausalClockFloorCoherentBounds.neutral
  rw [KFCausalClockFloorMixedRadialStrip.grouped_mix]
  change Complex.exp _*(Complex.exp _*Complex.exp ((v:ℂ)*Complex.I*
    ((r:ℂ)+2*(complexScale z-1)*((2*scale*s:ℝ):ℂ)))) = _
  rw [← Complex.exp_add,← Complex.exp_add]
  unfold KFCausalDyadicOscillatoryHeat.packet
  congr 1
  dsimp [radius,phase,shear]
  push_cast
  ring_nf
  rw [show (scale:ℂ)^2 = 1/2 by rw [← Complex.ofReal_pow,scale_square]; norm_num]
  ring

theorem inverse_derivative_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : ‖deriv (complexInverse ε) q‖ ≤ 1/ε := by
  have ht : q ∈ targetStrip ε := by change |q.im| ≤ Real.pi*ε/2; nlinarith [Real.pi_pos]
  have hn : ∀ᶠ x : ℂ in 𝓝 q, |x.im| < Real.pi*ε/2 :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds
      (by nlinarith [Real.pi_pos] : |q.im| < Real.pi*ε/2)
  apply norm_deriv_le_of_lip' (by positivity)
  filter_upwards [hn] with x hx
  exact (complexInverse_norm_bound ε hε x q (show x ∈ targetStrip ε from hx.le) ht).trans_eq (by ring)

#print axioms radius_re
#print axioms radius_lower
#print axioms radius_nonneg
#print axioms radius_derivative
#print axioms radius_slope_bound
#print axioms shear_square
#print axioms shear_bound
#print axioms phase_im_bound
#print axioms phase_derivative
#print axioms factor_packet
#print axioms inverse_derivative_bound

end
end UnifiedTheory.Audit.KFCausalRadialStripGeometry
