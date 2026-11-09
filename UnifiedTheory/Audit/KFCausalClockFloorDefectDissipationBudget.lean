/- A time-independent classical-response dissipation budget along the
actual quantum propagator. Its long-time averages tend to zero and it
becomes arbitrarily small at late times. This does not identify the
limiting clock-defect expectation as zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit
import UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutput)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "𝒲" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "D" => defectOperator ε hε
local notation "R" => exactRate ε hε h hne hh m g k

def expectation (s t : ℝ) (w : 𝒲) : ℝ := (inner ℂ (U s t (J w)) (D (U s t (J w)))).re
def dissipation (s t : ℝ) (w : 𝒲) : ℝ := -classicalRate ε hε h hne hh m g k s t w
def average (s a T : ℝ) (w : 𝒲) : ℝ := (∫ t in a..a+T, dissipation ε hε h hne hh m g k s t w)/T

theorem expectation_nonnegative (s t : ℝ) (w : 𝒲) : 0 ≤ expectation ε hε h hne hh m g k s t w :=
  KFCausalClockFloorStrictQuantumLimit.expectation_nonnegative ε hε _

theorem dissipation_nonnegative (s t : ℝ) (w : 𝒲) : 0 ≤ dissipation ε hε h hne hh m g k s t w :=
  neg_nonneg.mpr (averaged_classical_nonpositive ε hε (evolvingOutput ε hε h hne hh m g k s t w))

theorem dissipation_continuous (s : ℝ) (w : 𝒲) : Continuous (fun t => dissipation ε hε h hne hh m g k s t w) := by
  have hp : Continuous (fun t => (t,F s t w)) :=
    continuous_id.prodMk (formFlow_continuous ε hε h hne hh m g k s w)
  have ho := (KFCausalClockFloorClockReferenceRate.output_continuous ε hε h hne hh m g k).comp
    (f := fun t => (t,F s t w)) hp
  have he : Continuous (fun t => evolvingOutput ε hε h hne hh m g k s t w) := by
    simpa only [KFCausalClockFloorClockReferenceRate.output_actual,evolvingOutput] using ho
  have hc := Complex.continuous_re.comp
    (he.inner (𝕜 := ℂ) (((classicalOutput ε hε).compLpL 2 angleMeasure).continuous.comp he))
  exact hc.neg

theorem dissipation_rate_bound (s t : ℝ) (w : 𝒲) :
    (1/32)*dissipation ε hε h hne hh m g k s t w ≤ -R s t w := by
  have hb := averaged_coercivity ε hε h hne hh (evolvingOutput ε hε h hne hh m g k s t w)
  simpa only [dissipation,exactRate,classicalRate,mul_neg] using neg_le_neg hb

theorem interval_budget (s a b : ℝ) (hab : a ≤ b) (w : 𝒲) :
    (∫ t in a..b, dissipation ε hε h hne hh m g k s t w) ≤
      32*(expectation ε hε h hne hh m g k s a w-expectation ε hε h hne hh m g k s b w) := by
  have hc := dissipation_continuous ε hε h hne hh m g k s w
  have hr := exactRate_continuous ε hε h hne hh m g k s w
  calc
    _ ≤ ∫ t in a..b, (-32)*R s t w :=
      intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable a b)
        ((continuous_const.mul hr).intervalIntegrable a b)
        (fun t _ => by linarith [dissipation_rate_bound ε hε h hne hh m g k s t w])
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,expectation_integral]
      unfold expectation
      ring

theorem forward_budget (s a b : ℝ) (hab : a ≤ b) (w : 𝒲) :
    (∫ t in a..b, dissipation ε hε h hne hh m g k s t w) ≤
      32*expectation ε hε h hne hh m g k s a w := by
  have hi := interval_budget ε hε h hne hh m g k s a b hab w
  have hp := expectation_nonnegative ε hε h hne hh m g k s b w
  linarith

theorem average_bounds (s a T : ℝ) (hT : 0 < T) (w : 𝒲) :
    0 ≤ average ε hε h hne hh m g k s a T w ∧
      average ε hε h hne hh m g k s a T w ≤ (32*expectation ε hε h hne hh m g k s a w)/T := by
  refine ⟨div_nonneg ?_ hT.le,?_⟩
  · exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun t => dissipation_nonnegative ε hε h hne hh m g k s t w)
  · exact div_le_div_of_nonneg_right (forward_budget ε hε h hne hh m g k s a (a+T) (by linarith) w) hT.le

theorem average_tendsto_zero (s a : ℝ) (w : 𝒲) :
    Tendsto (fun T => average ε hε h hne hh m g k s a T w) atTop (𝓝 0) := by
  apply squeeze_zero' ((eventually_gt_atTop (0:ℝ)).mono (fun T hT => (average_bounds ε hε h hne hh m g k s a T hT w).1))
    ((eventually_gt_atTop (0:ℝ)).mono (fun T hT => (average_bounds ε hε h hne hh m g k s a T hT w).2))
  exact tendsto_id.const_div_atTop _

theorem arbitrarily_late_small (s a η : ℝ) (hη : 0 < η) (w : 𝒲) :
    ∃ t : ℝ, a ≤ t ∧ dissipation ε hε h hne hh m g k s t w < η := by
  by_contra hn
  have hl (t : ℝ) (ht : a ≤ t) : η ≤ dissipation ε hε h hne hh m g k s t w := by
    by_contra hlt
    exact hn ⟨t,ht,lt_of_not_ge hlt⟩
  have hb : ∀ᶠ T : ℝ in atTop, η ≤ average ε hε h hne hh m g k s a T w := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hi := intervalIntegral.integral_mono_on (μ := volume) (a := a) (b := a+T) (by linarith)
      (intervalIntegrable_const (c := η))
      ((dissipation_continuous ε hε h hne hh m g k s w).intervalIntegrable a (a+T))
      (fun t ht => hl t ht.1)
    apply (le_div_iff₀ hT).mpr
    simpa only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul,mul_comm] using hi
  have hz := ge_of_tendsto (average_tendsto_zero ε hε h hne hh m g k s a w) hb
  exact hη.not_ge hz

#print axioms expectation_nonnegative
#print axioms dissipation_nonnegative
#print axioms dissipation_continuous
#print axioms dissipation_rate_bound
#print axioms interval_budget
#print axioms forward_budget
#print axioms average_bounds
#print axioms average_tendsto_zero
#print axioms arbitrarily_late_small
end
end UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget
