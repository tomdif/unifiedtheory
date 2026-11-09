/- The quantitative classical clock bound integrated over the actual
transported laws. For the identified initial law the bound is an explicit
one-dimensional initial-clock integral, with no evolved state in it. -/
import UnifiedTheory.Audit.KFCausalClassicalClockDeadline
import UnifiedTheory.Audit.KFCausalClassicalMatterEvolvedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalClockMeanBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase)
open UnifiedTheory.Audit.KFCausalClassicalClockGrowth
open UnifiedTheory.Audit.KFCausalClassicalClockDeadline
open UnifiedTheory.Audit.KFCausalClassicalExplicitTiltControl (adjusted)
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterLaw
open UnifiedTheory.Audit.KFCausalClassicalMatterInitialLaw
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolvedLaw
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q p)
open UnifiedTheory.Audit.KFCausalClassicalVacuumClockComponents (clockShift clockShift_clock)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw clockLaw_probability)

theorem errorBound_continuous (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (t : ℝ) (ht : 0 ≤ t) :
    Continuous (fun x : TimePhase => errorBound ε κ x t) := by
  have hc : Continuous (fun x : TimePhase => clock ε (q (.inr 0) x.2)) := by unfold clock; fun_prop
  have hl := hc.log (fun x => (clock_positive ε (q (.inr 0) x.2) hε.le).ne')
  have ha : Continuous (fun x : TimePhase => adjusted ε x.2) := by
    unfold adjusted
    exact (((p (.inr 0)).continuous.comp continuous_snd).div hc
      (fun x => (clock_positive ε (q (.inr 0) x.2) hε.le).ne')).add (continuous_const.mul hl)
  have hr : Continuous (fun x : TimePhase => response ε (q (.inr 0) x.2)) := by
    unfold response
    exact (Real.continuous_exp.comp ((q (.inr 0)).continuous.comp continuous_snd)).div hc
      (fun x => (clock_positive ε (q (.inr 0) x.2) hε.le).ne')
  have hg : Continuous (growth ε κ) := by unfold growth; fun_prop
  have hb : Continuous (fun x : TimePhase => boost ε (q (.inr 0) x.2)) := by unfold boost; fun_prop
  have he : Continuous (fun x : TimePhase => envelope ε κ x t) := by unfold envelope; fun_prop
  have heLog := he.log (fun x => (envelope_positive ε κ hε hκ x t ht).ne')
  unfold errorBound
  fun_prop

theorem errorBound_le_one (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x : TimePhase) (t : ℝ) (ht : 0 ≤ t) : errorBound ε κ x t ≤ 1 :=
  (errorBound_le_initial ε κ hε hκ x t ht).trans (clockDefect_bounds ε hε x).2

theorem errorBound_integrable (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (μ : Measure TimePhase) [IsFiniteMeasure μ] (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => errorBound ε κ x t) μ := by
  apply (integrable_const (1:ℝ)).mono' (errorBound_continuous ε κ hε hκ t ht).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (errorBound_positive ε κ hε x t)]
  exact errorBound_le_one ε κ hε hκ x t ht

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem transported_defect_le_budget (μ : Measure TimePhase) [IsFiniteMeasure μ] (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, clockDefect ε x ∂transport ε m g κ hε hm hg hκ μ t) ≤ ∫ x, errorBound ε κ x t ∂μ := by
  rw [transport_integral ε m g κ hε hm hg hκ μ t _ (clockDefect_continuous ε hε)]
  have hi : Integrable (fun x => clockDefect ε (Φ t x)) μ := by
    apply (integrable_const (1:ℝ)).mono' ((clockDefect_continuous ε hε).comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ t)).aestronglyMeasurable
    filter_upwards [] with x
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_nonneg (clockDefect_bounds ε hε (Φ t x)).1]
    exact (clockDefect_bounds ε hε (Φ t x)).2
  exact integral_mono hi (errorBound_integrable ε κ hε hκ μ t ht)
    (fun x => evolve_defect_bound ε m g κ hε hm hg hκ x t ht)

def initialBudget (ε a κ τ t : ℝ) : ℝ :=
  ∫ s, errorBound ε κ (τ,clockShift s 0 (0:Phase)) t ∂clockLaw ε a

theorem evolvedLaw_defect_le_initialBudget (a τ : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x, clockDefect ε x ∂evolvedLaw ε a m g κ τ hε hm hg hκ t) ≤ initialBudget ε a κ τ t := by
  letI := initialLaw_probability ε a τ hε ha
  have he := transported_defect_le_budget ε m g κ hε hm hg hκ (initialLaw ε a τ) t ht
  have hc : Continuous (fun s : ℝ => (τ,clockShift s 0 (0:Phase))) := by unfold clockShift; fun_prop
  rw [initialLaw_axis,integral_map hc.measurable.aemeasurable
    (errorBound_continuous ε κ hε hκ t ht).aestronglyMeasurable] at he
  simpa only [evolvedLaw,initialBudget,initialLaw_axis] using he

theorem initialBudget_nonnegative (ε a κ τ t : ℝ) (hε : 0 < ε) :
    0 ≤ initialBudget ε a κ τ t := integral_nonneg (fun _ => (errorBound_positive ε κ hε _ t).le)

theorem initialBudget_le_one (ε a κ τ : ℝ) (hε : 0 < ε) (ha : 0 < a) (hκ : 0 < κ)
    (t : ℝ) (ht : 0 ≤ t) : initialBudget ε a κ τ t ≤ 1 := by
  letI := clockLaw_probability ε a hε ha
  have hc : Continuous (fun s : ℝ => (τ,clockShift s 0 (0:Phase))) := by unfold clockShift; fun_prop
  have hi : Integrable (fun s => errorBound ε κ (τ,clockShift s 0 (0:Phase)) t) (clockLaw ε a) := by
    apply (integrable_const (1:ℝ)).mono'
      ((errorBound_continuous ε κ hε hκ t ht).comp hc).aestronglyMeasurable
    filter_upwards [] with s
    simp only [Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_pos (errorBound_positive ε κ hε _ t)]
    exact errorBound_le_one ε κ hε hκ _ t ht
  have he := integral_mono hi (integrable_const (1:ℝ))
    (fun s => errorBound_le_one ε κ hε hκ (τ,clockShift s 0 (0:Phase)) t ht)
  simpa only [initialBudget,integral_const,probReal_univ,smul_eq_mul,one_mul] using he

theorem axis_errorBound_eq (ε κ τ s t : ℝ) :
    errorBound ε κ (τ,clockShift s 0 (0:Phase)) t =
      ε*Real.exp (-Real.log (boost ε s+
        (43692*κ*response ε s*Real.exp (2*τ+65536*Real.log (clock ε s)))*(Real.exp (3*t/2)-1))/65538) := by
  simp only [errorBound,envelope,growth,adjusted,(clockShift_clock s 0 (0:Phase)).1,
    (clockShift_clock s 0 (0:Phase)).2,map_zero,zero_add,add_zero,zero_div]

#print axioms errorBound_continuous
#print axioms errorBound_le_one
#print axioms errorBound_integrable
#print axioms transported_defect_le_budget
#print axioms evolvedLaw_defect_le_initialBudget
#print axioms initialBudget_nonnegative
#print axioms initialBudget_le_one
#print axioms axis_errorBound_eq
end
end UnifiedTheory.Audit.KFCausalClassicalClockMeanBound
