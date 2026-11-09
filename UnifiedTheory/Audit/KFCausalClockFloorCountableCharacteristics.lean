/- A single subsequence of the actual evolved boosted states has positive
continuous characteristic limits at every member of a countable sampling
family. Each member may use its own finite forward window. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenCharacteristicLimit
import UnifiedTheory.Audit.KFCausalCountableCharacteristicCompactness
import UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenCharacteristicLimit

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- This records proved properties of a frequency kernel, not a representing measure. -/
structure ClassicalKernel where
  value : Coefficients → ℂ
  continuous_value : Continuous value
  value_zero : value 0 = 1
  norm_le_one : ∀ z, ‖value z‖ ≤ 1
  value_neg : ∀ z, value (-z) = starRingEnd ℂ (value z)
  positive : ∀ N : ℕ, ∀ z : Fin N → Coefficients, ∀ c : Fin N → ℂ,
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*value (z j-z i)).re ∧
      (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*value (z j-z i)).im = 0

variable {K : Type*} [Countable K]

theorem sampled_common_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : K → ℝ) (t : K → ℕ → ℝ)
    (ht : ∀ k n, t k n ∈ Set.Icc s (s+T k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : K → ClassicalKernel,
      (∀ k z, Tendsto (fun n => characteristic volume (h (φ n))
        (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k (φ n)))
        (encode z)) atTop (𝓝 ((χ k).value z))) ∧
      (∀ k S, IsCompact S → TendstoUniformlyOn
        (fun n z => characteristic volume (h (φ n))
          (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k (φ n)))
          (encode z)) (χ k).value atTop S) := by
  let F : ℕ → K → Coefficients → ℂ := fun n k z => characteristic volume (h n)
    (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t k n)) (encode z)
  have hF (n : ℕ) (k : K) (z : Coefficients) : ‖F n k z‖ ≤ 1 := by
    simpa only [F,evolvedState_norm,one_pow] using
      KFCausalCanonicalWeylAlgebra.characteristic_bound volume (h n)
        (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t k n)) (encode z)
  have he (k : K) := sampled_equicontinuity ε a hε ha m g κ s p hm hg hκ h hh hb hz (T k) (t k) (ht k)
  obtain ⟨φ,hφ,c,hc,hlim,hbound⟩ :=
    KFCausalCountableCharacteristicCompactness.exists_common_continuous_subsequence F hF he
  let f : K → ℕ → Hilbert := fun k n =>
    evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k (φ n))
  have hf (k : K) (n : ℕ) : ‖f k n‖ = 1 :=
    evolvedState_norm ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k (φ n))
  have hz' : Tendsto (fun n => h (φ n)) atTop (𝓝 0) := hz.comp hφ.tendsto_atTop
  let χ : K → ClassicalKernel := fun k =>
    ⟨c k, hc k,
      KFCausalEncodedCharacteristicLimit.limit_zero volume encode (fun n => h (φ n)) (f k) (hf k) (c k) (hlim k),
      hbound k,
      KFCausalEncodedCharacteristicLimit.limit_conjugate volume encode (fun n => h (φ n)) hz' (f k) (hf k) (c k) (hlim k),
      KFCausalEncodedCharacteristicLimit.limit_positive_kernel volume encode (fun n => h (φ n)) hz' (f k) (hf k) (c k) (hlim k)⟩
  refine ⟨φ,hφ,χ,hlim,?_⟩
  intro k S hS
  exact KFCausalCharacteristicCompactUniformity.compact_uniform_convergence
    (fun n z => F n k z) (he k) φ hφ (c k) (hlim k) S hS

theorem fixed_times_common_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (t : K → ℝ) (ht : ∀ k, s ≤ t k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : K → ClassicalKernel,
      (∀ k z, Tendsto (fun n => characteristic volume (h (φ n))
        (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
        (encode z)) atTop (𝓝 ((χ k).value z))) ∧
      (∀ k S, IsCompact S → TendstoUniformlyOn
        (fun n z => characteristic volume (h (φ n))
          (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t k))
          (encode z)) (χ k).value atTop S) := by
  exact sampled_common_limit ε a hε ha m g κ s p hm hg hκ h hh hb hz
    (fun k => t k-s) (fun k _ => t k) (fun k _ => ⟨ht k, by linarith⟩)

#print axioms sampled_common_limit
#print axioms fixed_times_common_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorCountableCharacteristics
