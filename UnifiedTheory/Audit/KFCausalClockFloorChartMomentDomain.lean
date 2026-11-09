/- A genuine propagated class on which the unbounded chart expectation
exists: finite energy and an initial inverse-gap moment. The evolved
chart moment is derived, rather than made a hypothesis on the trajectory. -/
import UnifiedTheory.Audit.KFCausalClockFloorInverseGapMoment
import UnifiedTheory.Audit.KFCausalClockFloorUnboundedClockEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier (gap_positive gap_upper)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)

theorem absolute_clock_bound (ε s : ℝ) (hε : 0 < ε) :
    |chart ε s| ≤ (1+ε)*clock ε s+2*(1-(defect ε s)^2)⁻¹ := by
  have hp := gap_positive ε hε s
  have hg := (le_div_iff₀ hε).mp (gap_upper ε hε s)
  have he : ε*Real.exp (-s) ≤ 2*(1-(defect ε s)^2)⁻¹ := by
    rw [Real.exp_neg]
    change ε/Real.exp s ≤ 2/(1-(defect ε s)^2)
    exact (div_le_div_iff₀ (Real.exp_pos s) hp).mpr (by nlinarith only [hg])
  have hs : |s| ≤ Real.exp s+Real.exp (-s) := by
    by_cases hz : 0 ≤ s
    · rw [abs_of_nonneg hz]
      linarith [Real.add_one_le_exp s,Real.exp_pos (-s)]
    · rw [abs_of_neg (lt_of_not_ge hz)]
      linarith [Real.add_one_le_exp (-s),Real.exp_pos s]
  have ha := abs_add_le (Real.exp s) (ε*s)
  rw [abs_of_pos (Real.exp_pos s),abs_mul,abs_of_pos hε] at ha
  have hm := mul_le_mul_of_nonneg_left hs hε.le
  unfold chart clock
  nlinarith only [ha,hm,he,mul_nonneg (by linarith : 0 ≤ 1+ε) hε.le]

def density (ε : ℝ) (f : Hilbert) (x : Configuration) : ℝ := chart ε x.1*‖f x‖^2
def moment (ε : ℝ) (f : Hilbert) : ℝ := ∫ x, density ε f x

theorem integrable_of_moments (ε : ℝ) (hε : 0 < ε) (f : Hilbert)
    (hc : Integrable (fun x : Configuration => clock ε x.1*‖f x‖^2))
    (hl : Integrable (KFCausalClockFloorInverseGapMoment.density ε f)) :
    Integrable (density ε f) := by
  have hmeas : AEStronglyMeasurable (density ε f) volume :=
    ((KFCausalRegularizedLongitudinalChart.chart_continuous ε).comp continuous_fst).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).norm.pow 2)
  apply ((hc.const_mul (1+ε)).add (hl.const_mul 2)).mono' hmeas
  filter_upwards [] with x
  change ‖chart ε x.1*‖f x‖^2‖ ≤ _
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f x‖)]
  have he := mul_le_mul_of_nonneg_right (absolute_clock_bound ε x.1 hε) (sq_nonneg ‖f x‖)
  simpa only [KFCausalClockFloorInverseGapMoment.density,add_mul,mul_assoc] using he

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k

theorem chart_integrable_after (s t : ℝ) (hst : s ≤ t) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    Integrable (density ε (U s t (J w))) :=
  integrable_of_moments ε hε _
    (KFCausalClockFloorUnboundedClockEhrenfest.clockMoment_integrable ε hε h hne hh m g k s t w)
    (KFCausalClockFloorInverseGapMoment.moment_integrable_after ε hε h hne hh m g k s t hst (J w) hw).1

#print axioms absolute_clock_bound
#print axioms integrable_of_moments
#print axioms chart_integrable_after
end
end UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain
