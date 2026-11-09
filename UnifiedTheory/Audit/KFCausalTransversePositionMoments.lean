/- Full shear bounds for transverse position moments in straightened
coordinates, and Schwartz packet square moments. -/
import UnifiedTheory.Audit.KFCausalTransverseFlowBounds
import UnifiedTheory.Audit.KFCausalClockTrialWeights
import UnifiedTheory.Audit.KFCausalSchwartzTransversePacket

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransversePositionMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseFlowBounds
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket

theorem phase_exp_le_clock (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    Real.exp (phase ε ((chartIso ε hε).symm q)) ≤ clock ε hε q := by
  apply Real.exp_le_exp.mpr
  change (chartIso ε hε).symm q-ε*Real.exp (-((chartIso ε hε).symm q)) ≤ (chartIso ε hε).symm q
  have hp := mul_nonneg hε.le (Real.exp_pos (-((chartIso ε hε).symm q))).le
  linarith

theorem flow_position_fourth_bound (ε : ℝ) (hε : 0 < ε) (q : ℝ) (x : Transverse) :
    ‖flow (phase ε ((chartIso ε hε).symm q)) x‖^4 ≤
      5000*(1+(clock ε hε q)^2)*‖x‖^4 := by
  have hs := flow_norm_square_bound (-phase ε ((chartIso ε hε).symm q)) x
  simp only [neg_neg] at hs
  have h₂ : ‖flow (phase ε ((chartIso ε hε).symm q)) x‖^2 ≤
      50*(1+clock ε hε q)*‖x‖^2 := by
    apply hs.trans
    gcongr
    exact phase_exp_le_clock ε hε q
  have h₄ := pow_le_pow_left₀ (sq_nonneg _) h₂ 2
  have hb : (1+clock ε hε q)^2 ≤ 2*(1+(clock ε hε q)^2) := by
    nlinarith [sq_nonneg (clock ε hε q-1)]
  nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ 2500*‖x‖^4 by positivity)]

def pulledField (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (z : Configuration) : ℝ :=
  l (((coordinateHomeomorph ε hε).symm z).2)

theorem pulledField_continuous (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) :
    Continuous (pulledField ε hε l) :=
  l.continuous.comp (continuous_snd.comp (coordinateHomeomorph ε hε).symm.continuous)

theorem pulledField_fourth_bound (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (z : Configuration) :
    (pulledField ε hε l z)^4 ≤ (5000*‖l‖^4)*(1+(clock ε hε z.1)^2)*‖z.2‖^4 := by
  have hl := pow_le_pow_left₀ (norm_nonneg _) (l.le_opNorm (((coordinateHomeomorph ε hε).symm z).2)) 4
  have hf := mul_le_mul_of_nonneg_left (flow_position_fourth_bound ε hε z.1 z.2) (pow_nonneg (norm_nonneg l) 4)
  rw [mul_pow,Real.norm_eq_abs] at hl
  have he (r : ℝ) : |r|^4=r^4 := by nlinarith only [sq_abs r]
  rw [he] at hl
  change (pulledField ε hε l z)^4 ≤ ‖l‖^4*‖flow (phase ε ((chartIso ε hε).symm z.1)) z.2‖^4 at hl
  nlinarith

theorem packet_square_moment (ψ : SchwartzMap TailSpace ℂ) (k : ℕ) :
    Integrable (fun x : Transverse => ‖x‖^k*‖unflattenSchwartz ψ x‖^2) := by
  have hi := ((unflattenSchwartz ψ).integrable_pow_mul volume k).const_mul
    (SchwartzMap.seminorm ℝ 0 0 (unflattenSchwartz ψ))
  apply hi.mono' ((continuous_norm.pow k).mul ((unflattenSchwartz ψ).continuous.norm.pow 2)).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right
    (SchwartzMap.norm_le_seminorm ℝ (unflattenSchwartz ψ) x) (norm_nonneg (unflattenSchwartz ψ x))
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg x) k)
  nlinarith

#print axioms phase_exp_le_clock
#print axioms flow_position_fourth_bound
#print axioms pulledField_continuous
#print axioms pulledField_fourth_bound
#print axioms packet_square_moment

end
end UnifiedTheory.Audit.KFCausalTransversePositionMoments
