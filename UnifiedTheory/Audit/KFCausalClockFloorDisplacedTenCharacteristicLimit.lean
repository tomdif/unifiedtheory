/- Existence, continuity and classical positivity of subsequential limits
of actual evolved canonical characteristics on the controlled ten-dimensional
frequency family. Sampling times may vary within a fixed forward window.
This does not identify a time-dependent classical evolution. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenTestControl
import UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates
import UnifiedTheory.Audit.KFCausalEncodedCharacteristicCompactness
import UnifiedTheory.Audit.KFCausalEncodedCharacteristicLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenCharacteristicLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem evolved_encoded_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ z : Coefficients, ‖z‖ ≤ ρ →
      let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
      ‖operator volume (h n) (encode z) f-f‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := KFCausalClockFloorDisplacedTenTestControl.evolved_simultaneous_uniform
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht z hz' => ?_⟩
  apply hN n hn t ht z.1 z.2
  · intro i
    exact (norm_le_pi_norm z.1 i).trans ((norm_fst_le z).trans hz')
  · intro i
    exact (norm_le_pi_norm z.2 i).trans ((norm_snd_le z).trans hz')

theorem sampled_equicontinuity (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    EventuallyLocallyEquicontinuous (fun n z => characteristic volume (h n)
      (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t n)) (encode z)) := by
  apply KFCausalEncodedCharacteristicCompactness.equicontinuity volume encode h hz
    (fun n => evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t n))
    (fun n => evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p (t n))
  intro δ hδ
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_encoded_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  exact ⟨ρ,hρ,N,fun n hn z hz' => hN n hn (t n) (ht n) z hz'⟩

theorem sampled_continuous_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : Coefficients → ℂ, Continuous χ ∧
      (∀ z, Tendsto (fun n => characteristic volume (h (φ n))
        (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t (φ n)))
        (encode z)) atTop (𝓝 (χ z))) ∧ ∀ z, ‖χ z‖ ≤ 1 := by
  apply exists_continuous_subsequence
    (fun n z => characteristic volume (h n)
      (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t n)) (encode z))
  · intro n z
    simpa only [evolvedState_norm,one_pow] using
      KFCausalCanonicalWeylAlgebra.characteristic_bound volume (h n)
        (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p (t n)) (encode z)
  · exact sampled_equicontinuity ε a hε ha m g κ s p hm hg hκ h hh hb hz T t ht

theorem sampled_classical_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : Coefficients → ℂ,
      Continuous χ ∧ χ 0 = 1 ∧ (∀ z, ‖χ z‖ ≤ 1) ∧
      (∀ z, χ (-z) = starRingEnd ℂ (χ z)) ∧
      (∀ N : ℕ, ∀ z : Fin N → Coefficients, ∀ c : Fin N → ℂ,
        0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).re ∧
          (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).im = 0) ∧
      (∀ z, Tendsto (fun n => characteristic volume (h (φ n))
        (evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t (φ n)))
        (encode z)) atTop (𝓝 (χ z))) := by
  obtain ⟨φ,hφ,χ,hχ,hc,hbound⟩ := sampled_continuous_limit
    ε a hε ha m g κ s p hm hg hκ h hh hb hz T t ht
  let f : ℕ → Hilbert := fun n =>
    evolvedState ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t (φ n))
  have hf (n : ℕ) : ‖f n‖ = 1 :=
    evolvedState_norm ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s p (t (φ n))
  have hz' : Tendsto (fun n => h (φ n)) atTop (𝓝 0) := hz.comp hφ.tendsto_atTop
  refine ⟨φ,hφ,χ,hχ,?_,hbound,?_,?_,hc⟩
  · exact KFCausalEncodedCharacteristicLimit.limit_zero volume encode (fun n => h (φ n)) f hf χ hc
  · exact KFCausalEncodedCharacteristicLimit.limit_conjugate volume encode (fun n => h (φ n)) hz' f hf χ hc
  · exact KFCausalEncodedCharacteristicLimit.limit_positive_kernel volume encode (fun n => h (φ n)) hz' f hf χ hc

#print axioms evolved_encoded_uniform
#print axioms sampled_equicontinuity
#print axioms sampled_continuous_limit
#print axioms sampled_classical_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenCharacteristicLimit
