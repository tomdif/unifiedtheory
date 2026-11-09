/- For a fixed probability curve, the interval balance determines the
whole spacetime net force. Its positive decomposition need not be unique. -/
import UnifiedTheory.Audit.KFCausalNetForceUniqueness
import UnifiedTheory.Audit.KFCausalSpacetimeMeasureSeparation
import UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalGlobalNetForceUniqueness
noncomputable section
open MeasureTheory Set SchwartzMap BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalNetForceUniqueness
open UnifiedTheory.Audit.KFCausalSpacetimeMeasureSeparation

open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (IntervalBalance)

def NetEquivalent (J K : Force) : Prop :=
  J.positive+K.negative = K.positive+J.negative

theorem interval_equivalent (ν : ℝ → ProbabilityMeasure ℝ) (J K : Force)
    (hJ : IntervalBalance ν J) (hK : IntervalBalance ν K)
    (a b : ℝ) (hab : a ≤ b) : Equivalent (J.interval a b) (K.interval a b) :=
  equivalent_of_same_balance _ _ _ _ (hJ a b hab) (hK a b hab)

theorem momentumSection_apply (μ : Measure (ℝ × ℝ)) (a b : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    ((μ.restrict (Icc a b ×ˢ univ)).map Prod.snd) A = μ (Icc a b ×ˢ A) := by
  rw [Measure.map_apply measurable_snd hA,Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,and_true]
  exact and_comm

theorem net_equivalent_of_same_curve (ν : ℝ → ProbabilityMeasure ℝ) (J K : Force)
    (hJ : IntervalBalance ν J) (hK : IntervalBalance ν K) : NetEquivalent J K := by
  apply ext_of_finite_windows
  · intro a b
    rw [Measure.restrict_add]
    infer_instance
  · intro a b
    rw [Measure.restrict_add]
    infer_instance
  · intro a b hab A hA
    have he := congrArg (fun μ : Measure ℝ => μ A) (interval_equivalent ν J K hJ hK a b hab)
    change (J.interval a b).positive A+(K.interval a b).negative A =
      (K.interval a b).positive A+(J.interval a b).negative A at he
    simp only [Force.interval,Force.window,momentumSection_apply _ _ _ A hA] at he
    exact he

theorem window_net_equivalent (J K : Force) (h : NetEquivalent J K) (a b : ℝ) :
    (J.window a b).positive+(K.window a b).negative =
      (K.window a b).positive+(J.window a b).negative := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ.restrict (Icc a b ×ˢ univ)) h
  simpa only [Measure.restrict_add] using he

theorem window_evaluate_eq (J K : Force) (h : NetEquivalent J K) (a b : ℝ)
    (q : (ℝ × ℝ) →ᵇ ℂ) : (J.window a b).evaluate q = (K.window a b).evaluate q := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => ∫ z, q z ∂μ) (window_net_equivalent J K h a b)
  dsimp only at he
  rw [integral_add_measure (q.integrable (J.window a b).positive) (q.integrable (K.window a b).negative),
    integral_add_measure (q.integrable (K.window a b).positive) (q.integrable (J.window a b).negative)] at he
  unfold Pair.evaluate
  linear_combination he/2

theorem same_curve_same_force_action (ν : ℝ → ProbabilityMeasure ℝ) (J K : Force)
    (hJ : IntervalBalance ν J) (hK : IntervalBalance ν K) (a b : ℝ)
    (q : (ℝ × ℝ) →ᵇ ℂ) : (J.window a b).evaluate q = (K.window a b).evaluate q :=
  window_evaluate_eq J K (net_equivalent_of_same_curve ν J K hJ hK) a b q

#print axioms interval_equivalent
#print axioms momentumSection_apply
#print axioms net_equivalent_of_same_curve
#print axioms window_net_equivalent
#print axioms window_evaluate_eq
#print axioms same_curve_same_force_action
end
end UnifiedTheory.Audit.KFCausalGlobalNetForceUniqueness
