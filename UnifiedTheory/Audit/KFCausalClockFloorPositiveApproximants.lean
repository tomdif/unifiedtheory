/- The actual evolved states admit positive phase-space probability
approximants with the previously constructed limiting characteristics,
on the same subsequence as the global clock path and balance. Existence
of a weak limit measure and classical transport remain separate. -/
import UnifiedTheory.Audit.KFCausalWindowedApproximation
import UnifiedTheory.Audit.KFCausalClockFloorJointClockCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveApproximants
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
open UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (law phase)
open UnifiedTheory.Audit.KFCausalSemiclassicalWindow (unitWindow)
open UnifiedTheory.Audit.KFCausalWindowedApproximation

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem joint_positive_subsequence {K : Type*} [Countable K]
    (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (t : K → ℝ) (ht : ∀ k, s ≤ t k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℝ,
      Continuous f ∧ (∀ u, f u ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ u, Tendsto (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p u)
        atTop (𝓝 (f u))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn
        (fun n => clockExpectation ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p) f atTop S) ∧
      (∀ T r u : ℝ, |r-s| ≤ T → |u-s| ≤ T →
        |f u-f r| ≤ speedConstant ε a m g κ s T p*|u-r|) ∧
      (∀ r u : ℝ, Tendsto (fun n => ∫ v in r..u,
        comparisonRate ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p v)
        atTop (𝓝 (f u-f r))) ∧
      ∃ χ : K → ClassicalKernel,
        (∀ k z, Tendsto (fun n => characteristic volume (h (φ n))
          (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
          (encode z)) atTop (𝓝 ((χ k).value z))) ∧
        (∀ k n, IsProbabilityMeasure (law (h (φ n))
          (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k)) (unitWindow 6 n))) ∧
        (∀ k z, Tendsto (fun n => ∫ x, phase (encode z) x ∂law (h (φ n))
          (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k)) (unitWindow 6 n))
          atTop (𝓝 ((χ k).value z))) := by
  obtain ⟨ψ,hψ,f,hf,hbounds,hpoint,huniform,hlip,hbalance,χ,hχ,_⟩ :=
    KFCausalClockFloorJointClockCharacteristics.joint_subsequence
      ε a hε ha m g κ s p hm hg hκ h hh hb hz t ht
  obtain ⟨σ,hσ,hprob,herror⟩ := exists_state_uniform_approximation
    (fun n => h (ψ n)) (hz.comp hψ.tendsto_atTop)
  refine ⟨fun n => ψ (σ n),hψ.comp hσ,f,hf,hbounds,?_,?_,hlip,?_,χ,?_,?_,?_⟩
  · intro u
    exact (hpoint u).comp hσ.tendsto_atTop
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact hσ.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (huniform S hS) η hη)
  · intro r u
    exact (hbalance r u).comp hσ.tendsto_atTop
  · intro k z
    exact (hχ k z).comp hσ.tendsto_atTop
  · intro k n
    exact hprob n _ (evolvedState_norm ε a (h (ψ (σ n))) hε ha (hh (ψ (σ n))) (hb (ψ (σ n))) m g κ s p (t k))
  · intro k z
    have he := error_tendsto (fun n => h (ψ n)) σ herror
      (fun n => evolvedState ε a (h (ψ (σ n))) hε ha (hh (ψ (σ n))) (hb (ψ (σ n))) m g κ s p (t k))
      (fun n => evolvedState_norm ε a (h (ψ (σ n))) hε ha (hh (ψ (σ n))) (hb (ψ (σ n))) m g κ s p (t k)) (encode z)
    have hc := (hχ k z).comp hσ.tendsto_atTop
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using he.add hc

#print axioms joint_positive_subsequence

end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveApproximants
