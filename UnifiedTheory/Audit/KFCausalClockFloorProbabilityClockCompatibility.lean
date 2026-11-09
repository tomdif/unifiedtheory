/- The global clock path is the clock-defect mean of the represented
ten-dimensional probabilities at every selected future time. The actual
clock Born laws converge to their clock marginals. No classical transport
identification is assumed or claimed. -/
import UnifiedTheory.Audit.KFCausalClockFloorProbabilityLimit
import UnifiedTheory.Audit.KFCausalClockMarginalWeakLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorProbabilityClockCompatibility
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
open UnifiedTheory.Audit.KFCausalSemiclassicalWindow (unitWindow unitWindow_norm)
open UnifiedTheory.Audit.KFCausalTenPhaseProjection
open UnifiedTheory.Audit.KFCausalTenProbabilityLimit

open UnifiedTheory.Audit.KFCausalClockFloorProbabilityLimit (snapshot)
open UnifiedTheory.Audit.KFCausalClockMarginalIdentification (clockProjection marginal)
open UnifiedTheory.Audit.KFCausalClockMarginalWeakLimit (bornProbability)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem joint_probability_clock_compatible {K : Type*} [Countable K]
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
        ∃ ν : K → ProbabilityMeasure TenSpace,
          (∀ k z, charFun (ν k : Measure TenSpace) (coefficientVector z) = (χ k).value z) ∧
          (∀ k, IsTightMeasureSet (Set.range (fun n =>
            (snapshot ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p n (t k) : Measure TenSpace)))) ∧
          (∀ k, Tendsto (fun n => snapshot ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p n (t k))
            atTop (𝓝 (ν k))) ∧
          (∀ k, Tendsto (fun n => bornProbability
            (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
            (evolvedState_norm ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k)))
            atTop (𝓝 (marginal (ν k)))) ∧
          (∀ k, (∫ x, defect ε (clockProjection x) ∂(ν k : Measure TenSpace)) = f (t k)) := by
  obtain ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip,hbalance,χ,hχ,ν,hν,htight,hweak⟩ :=
    KFCausalClockFloorProbabilityLimit.joint_probability_subsequence
      ε a hε ha m g κ s p hm hg hκ h hh hb hz t ht
  refine ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip,hbalance,χ,hχ,ν,hν,htight,hweak,?_,?_⟩
  · intro k
    exact KFCausalClockMarginalWeakLimit.born_weak_limit (fun n => h (φ n))
      (fun n => evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
      (fun n => evolvedState_norm ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
      (χ k) (ν k) (hν k) (hχ k)
  · intro k
    have hm := KFCausalClockMarginalWeakLimit.defect_mean_limit ε hε (fun n => h (φ n))
      (fun n => evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
      (fun n => evolvedState_norm ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
      (χ k) (ν k) (hν k) (hχ k)
    exact tendsto_nhds_unique hm (hpoint (t k))

#print axioms joint_probability_clock_compatible

end
end UnifiedTheory.Audit.KFCausalClockFloorProbabilityClockCompatibility
