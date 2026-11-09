/- One semiclassical subsequence carries the global clock path and all
characteristic kernels at any prescribed countable set of future times.
The clock balance retains quantum comparison outputs; it is not yet an
identified classical phase-space transport law. -/
import UnifiedTheory.Audit.KFCausalClockFloorGlobalClockLimit
import UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorJointClockCharacteristics
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow
open UnifiedTheory.Audit.KFCausalClockFloorGlobalClockLimit
open UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem joint_subsequence {K : Type*} [Countable K]
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
        (∀ k S, IsCompact S → TendstoUniformlyOn
          (fun n z => characteristic volume (h (φ n))
            (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
            (encode z)) (χ k).value atTop S) := by
  obtain ⟨ψ,hψ,f,hf,hbounds,hpoint,huniform,hlip,hbalance⟩ :=
    clock_global_balance ε a hε ha m g κ s p hm hg hκ h hh hb hz
  obtain ⟨σ,hσ,χ,hχ,hχuniform⟩ := fixed_times_common_limit
    ε a hε ha m g κ s p hm hg hκ (fun n => h (ψ n)) (fun n => hh (ψ n))
      (fun n => hb (ψ n)) (hz.comp hψ.tendsto_atTop) t ht
  refine ⟨fun n => ψ (σ n),hψ.comp hσ,f,hf,hbounds,?_,?_,hlip,?_,χ,hχ,hχuniform⟩
  · intro u
    exact (hpoint u).comp hσ.tendsto_atTop
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff] at ⊢
    intro η hη
    exact hσ.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (huniform S hS) η hη)
  · intro r u
    exact (hbalance r u).comp hσ.tendsto_atTop

#print axioms joint_subsequence

end
end UnifiedTheory.Audit.KFCausalClockFloorJointClockCharacteristics
