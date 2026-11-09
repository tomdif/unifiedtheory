/- Net force observables have a joint limit as the probability-sequence
index and the positive resolvent scale independently tend to infinity. -/
import UnifiedTheory.Audit.KFCausalNeutralFullSequenceForceConvergence
import Mathlib.Order.Filter.AtTopBot.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralJointForceLimit
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce (forceWindow)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (IntervalBalance)
open UnifiedTheory.Audit.KFCausalNeutralFullSequenceForceConvergence

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (ν : ℝ → ProbabilityMeasure ℝ)
  (hchar : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h n) hε ha (hne n) (hh n)
    m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
  (J : Force) (hJ : IntervalBalance ν J) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)

include hz hchar hJ hm hg hk

theorem spacetime_joint_limit (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun z : ℕ × Ioi (0 : ℝ) =>
      (forceWindow ε a (h z.1) hε ha (hne z.1) (hh z.1) m g k s p z.2.1 z.2.2 b c).evaluate q.toBCF)
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter (Ioi (0 : ℝ))))
        (𝓝 ((J.window b c).evaluate q.toBCF)) := by
  apply tendsto_of_seq_tendsto
  intro z ht
  have hn := tendsto_fst.comp ht
  have hr := tendsto_Ioi_atTop.mp (tendsto_snd.comp ht)
  exact spacetime_converges ε a hε ha m g k s p
    (fun n => h (z n).1) (fun n => hne (z n).1) (fun n => hh (z n).1)
    (hz.comp hn) ν (fun w => (hchar w).comp hn) J hJ hm hg hk
    (fun n => (z n).2.1) (fun n => (z n).2.2) hr b c hbc q

theorem momentum_joint_limit (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ,ℂ)) :
    Tendsto (fun z : ℕ × Ioi (0 : ℝ) =>
      (forceInterval ε a (h z.1) hε ha (hne z.1) (hh z.1) m g k s p z.2.1 z.2.2 b c).evaluate q.toBCF)
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter (Ioi (0 : ℝ))))
        (𝓝 ((J.interval b c).evaluate q.toBCF)) := by
  apply tendsto_of_seq_tendsto
  intro z ht
  have hn := tendsto_fst.comp ht
  have hr := tendsto_Ioi_atTop.mp (tendsto_snd.comp ht)
  exact momentum_converges ε a hε ha m g k s p
    (fun n => h (z n).1) (fun n => hne (z n).1) (fun n => hh (z n).1)
    (hz.comp hn) ν (fun w => (hchar w).comp hn) J hJ hm hg hk
    (fun n => (z n).2.1) (fun n => (z n).2.2) hr b c hbc q

#print axioms spacetime_joint_limit
#print axioms momentum_joint_limit
end
end UnifiedTheory.Audit.KFCausalNeutralJointForceLimit
