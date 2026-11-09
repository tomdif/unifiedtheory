/- Probability laws transported by the constructed continuous matter flow.
The mean classical clock defect tends to zero for every finite initial law;
this is not yet a transport theorem for quantum states. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterFlow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterLaw
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q)
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterFlow
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem evolve_continuous_initial (t : ℝ) : Continuous (Φ t) :=
  (evolve_continuous ε m g κ hε hm hg hκ).comp (continuous_const.prodMk continuous_id)

def transport (μ : Measure TimePhase) (t : ℝ) : Measure TimePhase := μ.map (Φ t)

theorem transport_probability (μ : Measure TimePhase) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (transport ε m g κ hε hm hg hκ μ t) :=
  Measure.isProbabilityMeasure_map (evolve_continuous_initial ε m g κ hε hm hg hκ t).measurable.aemeasurable

theorem transport_zero (μ : Measure TimePhase) :
    transport ε m g κ hε hm hg hκ μ 0 = μ := by
  change μ.map (fun x => Φ 0 x) = μ
  simp only [evolve_zero,Measure.map_id']

theorem transport_add (μ : Measure TimePhase) (s t : ℝ) :
    transport ε m g κ hε hm hg hκ μ (s+t) =
      transport ε m g κ hε hm hg hκ (transport ε m g κ hε hm hg hκ μ t) s := by
  unfold transport
  rw [Measure.map_map (evolve_continuous_initial ε m g κ hε hm hg hκ s).measurable
    (evolve_continuous_initial ε m g κ hε hm hg hκ t).measurable]
  congr 1
  funext x
  exact evolve_add ε m g κ hε hm hg hκ s t x

theorem transport_integral (μ : Measure TimePhase) (t : ℝ) (f : TimePhase → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂transport ε m g κ hε hm hg hκ μ t) = ∫ x, f (Φ t x) ∂μ :=
  integral_map (evolve_continuous_initial ε m g κ hε hm hg hκ t).measurable.aemeasurable hf.aestronglyMeasurable

def clockDefect (x : TimePhase) : ℝ := defect ε (q (.inr 0) x.2)

include hε in
theorem clockDefect_continuous : Continuous (clockDefect ε) := by
  have hc : Continuous (fun x : TimePhase => clock ε (q (.inr 0) x.2)) := by unfold clock; fun_prop
  exact continuous_const.div hc (fun x => (clock_positive ε _ hε.le).ne')

include hε in
theorem clockDefect_bounds (x : TimePhase) : 0 ≤ clockDefect ε x ∧ clockDefect ε x ≤ 1 := by
  have hp := defect_positive ε (q (.inr 0) x.2) hε
  have hr := (response_bounds ε (q (.inr 0) x.2) hε).1
  have he := response_add_defect ε (q (.inr 0) x.2) hε.le
  exact ⟨hp.le,by change defect ε _ ≤ 1; linarith⟩

theorem transported_defect_tendsto_zero (μ : Measure TimePhase) [IsFiniteMeasure μ] :
    Tendsto (fun t => ∫ x, clockDefect ε x ∂transport ε m g κ hε hm hg hκ μ t)
      atTop (𝓝 0) := by
  simp_rw [transport_integral ε m g κ hε hm hg hκ μ _ _ (clockDefect_continuous ε hε)]
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := (atTop : Filter ℝ))
    (F := fun t x => clockDefect ε (Φ t x)) (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (Eventually.of_forall (fun t => ((clockDefect_continuous ε hε).comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ t)).aestronglyMeasurable))
    (Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (clockDefect_bounds ε hε (Φ t x)).1]
      exact (clockDefect_bounds ε hε (Φ t x)).2)))
    (integrable_const 1)
    (Eventually.of_forall (fun x => (evolve_recovery ε m g κ hε hm hg hκ x).2))
  simpa only [integral_zero] using h

theorem transported_bounded_test_continuous (μ : Measure TimePhase) [IsFiniteMeasure μ]
    (f : TimePhase → ℝ) (hf : Continuous f) (M : ℝ) (hb : ∀ x, ‖f x‖ ≤ M) :
    Continuous (fun t => ∫ x, f x ∂transport ε m g κ hε hm hg hκ μ t) := by
  simp_rw [transport_integral ε m g κ hε hm hg hκ μ _ f hf]
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall (fun u => (hf.comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ u)).aestronglyMeasurable))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => hb _)))
    (integrable_const M)
    (Eventually.of_forall (fun x => (hf.comp
      (evolve_continuous_time ε m g κ hε hm hg hκ x)).tendsto t))

#print axioms evolve_continuous_initial
#print axioms transport_probability
#print axioms transport_zero
#print axioms transport_add
#print axioms transport_integral
#print axioms clockDefect_continuous
#print axioms clockDefect_bounds
#print axioms transported_defect_tendsto_zero
#print axioms transported_bounded_test_continuous

end
end UnifiedTheory.Audit.KFCausalClassicalMatterLaw

