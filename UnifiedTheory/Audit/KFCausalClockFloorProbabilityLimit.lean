/- Actual positive ten-coordinate probability measures now converge on
the same subsequence as the global clock path. Tightness, representing
probabilities and weak convergence are derived rather than assumed.
Clock compatibility and a classical evolution equation remain separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveApproximants
import UnifiedTheory.Audit.KFCausalTenProbabilityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorProbabilityLimit
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

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def snapshot (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (m g κ s : ℝ) (p : Configuration) (n : ℕ) (u : ℝ) : ProbabilityMeasure TenSpace :=
  projectedProbability
    (law h (evolvedState ε a h hε ha hh hb m g κ s p u) (unitWindow 6 n))
    (KFCausalPhysicalWindowedLaw.law_probability _ _ _
      (evolvedState_norm ε a h hε ha hh hb m g κ s p u) (unitWindow_norm 6 n))

theorem snapshot_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (n : ℕ) (u : ℝ) (z : TenSpace) :
    charFun (snapshot ε a h hε ha hh hb m g κ s p n u : Measure TenSpace) z =
      ∫ x, phase (encode (coefficients z)) x
        ∂law h (evolvedState ε a h hε ha hh hb m g κ s p u) (unitWindow 6 n) :=
  projected_characteristic _ z

theorem joint_probability_subsequence {K : Type*} [Countable K]
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
            atTop (𝓝 (ν k))) := by
  classical
  obtain ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip,hbalance,χ,hχ,hprob,hphase⟩ :=
    KFCausalClockFloorPositiveApproximants.joint_positive_subsequence
      ε a hε ha m g κ s p hm hg hκ h hh hb hz t ht
  have hrep (k : K) := tight_and_represented
    (fun n => law (h (φ n))
      (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k)) (unitWindow 6 n))
    (hprob k) (χ k) (hphase k)
  choose ν hν hweak using fun k => (hrep k).2
  exact ⟨φ,hφ,f,hf,hbounds,hpoint,huniform,hlip,hbalance,χ,hχ,ν,hν,
    fun k => (hrep k).1,hweak⟩

#print axioms snapshot_characteristic
#print axioms joint_probability_subsequence

end
end UnifiedTheory.Audit.KFCausalClockFloorProbabilityLimit
