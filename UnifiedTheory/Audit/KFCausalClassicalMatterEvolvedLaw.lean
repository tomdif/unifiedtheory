/- The full classical transport target for the already identified physical
quantum initial law. It solves Liouville and recovers the clock in mean.
The positive-time quantum characteristic convergence to it remains open. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterInitialLaw
import UnifiedTheory.Audit.KFCausalClassicalMatterLiouville

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterEvolvedLaw
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterLaw
open UnifiedTheory.Audit.KFCausalClassicalMatterInitialLaw
open UnifiedTheory.Audit.KFCausalClassicalMatterLiouville
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)

theorem phaseTest_norm (r u : ℝ) (ξ η : Transverse) (x : TimePhase) :
    ‖phaseTest r u ξ η x‖ = 1 := by
  simp [phaseTest,classicalPhase,Complex.norm_exp]

variable (ε a m g κ τ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

def evolvedLaw (t : ℝ) : Measure TimePhase :=
  transport ε m g κ hε hm hg hκ (initialLaw ε a τ) t

theorem evolvedLaw_probability (ha : 0 < a) (t : ℝ) :
    IsProbabilityMeasure (evolvedLaw ε a m g κ τ hε hm hg hκ t) := by
  letI := initialLaw_probability ε a τ hε ha
  exact transport_probability ε m g κ hε hm hg hκ (initialLaw ε a τ) t

theorem evolvedLaw_zero : evolvedLaw ε a m g κ τ hε hm hg hκ 0 = initialLaw ε a τ :=
  transport_zero ε m g κ hε hm hg hκ (initialLaw ε a τ)

theorem evolvedLaw_recovery (ha : 0 < a) :
    Tendsto (fun t => ∫ x, clockDefect ε x ∂evolvedLaw ε a m g κ τ hε hm hg hκ t)
      atTop (𝓝 0) := by
  letI := initialLaw_probability ε a τ hε ha
  exact transported_defect_tendsto_zero ε m g κ hε hm hg hκ (initialLaw ε a τ)

theorem evolvedLaw_liouville (ha : 0 < a) (f : TimePhase → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (fun u => ∫ x, f x ∂evolvedLaw ε a m g κ τ hε hm hg hκ u)
      (∫ x, generator ε m g κ f x ∂evolvedLaw ε a m g κ τ hε hm hg hκ t) t := by
  letI := initialLaw_probability ε a τ hε ha
  exact transport_liouville ε m g κ hε hm hg hκ (initialLaw ε a τ) f hf hs t

def characteristic (r u : ℝ) (ξ η : Transverse) (t : ℝ) : ℂ :=
  ∫ x, phaseTest r u ξ η x ∂evolvedLaw ε a m g κ τ hε hm hg hκ t

theorem characteristic_integral (r u : ℝ) (ξ η : Transverse) (t : ℝ) :
    characteristic ε a m g κ τ hε hm hg hκ r u ξ η t =
      ∫ x, phaseTest r u ξ η (Φ t x) ∂initialLaw ε a τ :=
  integral_map (evolve_continuous_initial ε m g κ hε hm hg hκ t).measurable.aemeasurable
    (phaseTest_continuous r u ξ η).aestronglyMeasurable

theorem characteristic_continuous (ha : 0 < a) (r u : ℝ) (ξ η : Transverse) :
    Continuous (characteristic ε a m g κ τ hε hm hg hκ r u ξ η) := by
  letI := initialLaw_probability ε a τ hε ha
  change Continuous (fun t => characteristic ε a m g κ τ hε hm hg hκ r u ξ η t)
  simp_rw [characteristic_integral]
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    (Eventually.of_forall (fun s => ((phaseTest_continuous r u ξ η).comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ s)).aestronglyMeasurable))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => (phaseTest_norm r u ξ η _).le)))
    (integrable_const 1)
    (Eventually.of_forall (fun x => ((phaseTest_continuous r u ξ η).comp
      (evolve_continuous_time ε m g κ hε hm hg hκ x)).tendsto t))

theorem characteristic_zero (r u : ℝ) (ξ η : Transverse) :
    characteristic ε a m g κ τ hε hm hg hκ r u ξ η 0 =
      ∫ z, classicalPhase r u ξ η z ∂classicalLaw ε a := by
  rw [characteristic,evolvedLaw_zero,initialLaw_test]

#print axioms phaseTest_norm
#print axioms evolvedLaw_probability
#print axioms evolvedLaw_zero
#print axioms evolvedLaw_recovery
#print axioms evolvedLaw_liouville
#print axioms characteristic_integral
#print axioms characteristic_continuous
#print axioms characteristic_zero

end
end UnifiedTheory.Audit.KFCausalClassicalMatterEvolvedLaw
