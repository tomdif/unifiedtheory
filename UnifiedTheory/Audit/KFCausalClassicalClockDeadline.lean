/- Explicit error bounds and a finite tolerance deadline for the actual
full classical flow. The positive-floor bracket is not exactly canonical
at finite time; its proved error can be made arbitrarily small. -/
import UnifiedTheory.Audit.KFCausalClassicalClockGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalClockDeadline
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalClockGrowth
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q p)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def errorBound (ε κ : ℝ) (x : TimePhase) (t : ℝ) : ℝ :=
  ε*Real.exp (-Real.log (envelope ε κ x t)/65538)

def deadline (ε κ : ℝ) (x : TimePhase) (η : ℝ) : ℝ :=
  (2/3)*Real.log (1+Real.exp (65538*Real.log (ε/η))/growth ε κ x)

theorem envelope_positive (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) : 0 < envelope ε κ x t := by
  have hg := growth_positive ε κ hε hκ x
  have he : 1 ≤ Real.exp (3*t/2) := Real.one_le_exp_iff.mpr (by positivity)
  have hb := boost_positive ε (q (.inr 0) x.2)
  unfold envelope
  nlinarith only [hb,mul_nonneg hg.le (sub_nonneg.mpr he)]

theorem errorBound_positive (ε κ : ℝ) (hε : 0 < ε) (x : TimePhase) (t : ℝ) :
    0 < errorBound ε κ x t := mul_pos hε (Real.exp_pos _)

theorem errorBound_le_initial (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    errorBound ε κ x t ≤ defect ε (q (.inr 0) x.2) := by
  have hg := growth_positive ε κ hε hκ x
  have he : 1 ≤ Real.exp (3*t/2) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : boost ε (q (.inr 0) x.2) ≤ envelope ε κ x t := by
    unfold envelope
    nlinarith only [mul_nonneg hg.le (sub_nonneg.mpr he)]
  have hl := Real.log_le_log (boost_positive ε (q (.inr 0) x.2)) hb
  rw [boost,Real.log_exp] at hl
  have hc := clock_positive ε (q (.inr 0) x.2) hε.le
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (show -Real.log (envelope ε κ x t)/65538 ≤ -Real.log (clock ε (q (.inr 0) x.2)) by
      linarith only [hl])) hε.le
  simpa only [errorBound,defect,Real.exp_neg,Real.exp_log hc,div_eq_mul_inv] using hh

theorem deadline_positive (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (η : ℝ) : 0 < deadline ε κ x η := by
  have hg := growth_positive ε κ hε hκ x
  have hr := div_pos (Real.exp_pos (65538*Real.log (ε/η))) hg
  unfold deadline
  exact mul_pos (by norm_num) (Real.log_pos (by linarith only [hr]))

theorem deadline_exponential (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (η : ℝ) :
    Real.exp (3*deadline ε κ x η/2) = 1+Real.exp (65538*Real.log (ε/η))/growth ε κ x := by
  have hg := growth_positive ε κ hε hκ x
  have hp : 0 < 1+Real.exp (65538*Real.log (ε/η))/growth ε κ x := by positivity
  unfold deadline
  rw [show 3*((2/3)*Real.log (1+Real.exp (65538*Real.log (ε/η))/growth ε κ x))/2 =
    Real.log (1+Real.exp (65538*Real.log (ε/η))/growth ε κ x) by ring]
  exact Real.exp_log hp

theorem target_le_envelope (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (η t : ℝ) (ht : deadline ε κ x η ≤ t) :
    Real.exp (65538*Real.log (ε/η)) ≤ envelope ε κ x t := by
  have hg := growth_positive ε κ hε hκ x
  have he := Real.exp_le_exp.mpr (show 3*deadline ε κ x η/2 ≤ 3*t/2 by linarith only [ht])
  rw [deadline_exponential ε κ hε hκ x η] at he
  have hd := (div_le_iff₀ hg).mp
    (show Real.exp (65538*Real.log (ε/η))/growth ε κ x ≤ Real.exp (3*t/2)-1 by linarith only [he])
  have hb := boost_positive ε (q (.inr 0) x.2)
  unfold envelope
  nlinarith only [hd,hb]

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem evolve_defect_bound (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    defect ε (q (.inr 0) (Φ t x).2) ≤ errorBound ε κ x t := by
  have hl := Real.log_le_log (envelope_positive ε κ hε hκ x t ht)
    (evolve_boost_lower ε m g κ hε hm hg hκ x t ht)
  rw [boost,Real.log_exp] at hl
  have hc := clock_positive ε (q (.inr 0) (Φ t x).2) hε.le
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (show -Real.log (clock ε (q (.inr 0) (Φ t x).2)) ≤ -Real.log (envelope ε κ x t)/65538 by
      linarith only [hl])) hε.le
  simpa only [errorBound,defect,Real.exp_neg,Real.exp_log hc,div_eq_mul_inv] using hh

theorem evolve_defect_le_of_deadline (x : TimePhase) (η : ℝ) (hη : 0 < η)
    (t : ℝ) (ht : deadline ε κ x η ≤ t) : defect ε (q (.inr 0) (Φ t x).2) ≤ η := by
  have ht0 := (deadline_positive ε κ hε hκ x η).le.trans ht
  have he := (target_le_envelope ε κ hε hκ x η t ht).trans
    (evolve_boost_lower ε m g κ hε hm hg hκ x t ht0)
  have hl := Real.exp_le_exp.mp he
  change 65538*Real.log (ε/η) ≤ 65538*Real.log (clock ε (q (.inr 0) (Φ t x).2)) at hl
  have hlog : Real.log (ε/η) ≤ Real.log (clock ε (q (.inr 0) (Φ t x).2)) := by linarith only [hl]
  have hc := clock_positive ε (q (.inr 0) (Φ t x).2) hε.le
  have hdiv := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hε hη),Real.exp_log hc] at hdiv
  have hmul := (div_le_iff₀ hη).mp hdiv
  unfold defect
  exact (div_le_iff₀ hc).mpr (by nlinarith only [hmul])

theorem evolve_bracket_error_bound (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) :
    |bracket (longitudinal ε) (fun s _ => clock ε s)
      (q (.inr 0) (Φ t x).2) (p (.inr 0) (Φ t x).2)+1| ≤ errorBound ε κ x t := by
  rw [bracket_clock_error _ _ _ hε.le,abs_of_pos (defect_positive _ _ hε)]
  exact evolve_defect_bound ε m g κ hε hm hg hκ x t ht

theorem evolve_bracket_error_le_of_deadline (x : TimePhase) (η : ℝ) (hη : 0 < η)
    (t : ℝ) (ht : deadline ε κ x η ≤ t) :
    |bracket (longitudinal ε) (fun s _ => clock ε s)
      (q (.inr 0) (Φ t x).2) (p (.inr 0) (Φ t x).2)+1| ≤ η := by
  rw [bracket_clock_error _ _ _ hε.le,abs_of_pos (defect_positive _ _ hε)]
  exact evolve_defect_le_of_deadline ε m g κ hε hm hg hκ x η hη t ht

#print axioms envelope_positive
#print axioms errorBound_positive
#print axioms errorBound_le_initial
#print axioms deadline_positive
#print axioms deadline_exponential
#print axioms target_le_envelope
#print axioms evolve_defect_bound
#print axioms evolve_defect_le_of_deadline
#print axioms evolve_bracket_error_bound
#print axioms evolve_bracket_error_le_of_deadline
end
end UnifiedTheory.Audit.KFCausalClassicalClockDeadline
