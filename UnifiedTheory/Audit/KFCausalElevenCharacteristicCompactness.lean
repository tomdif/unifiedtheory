/- Actual evolved canonical tests are controlled on eleven independent
directions. Sampling times may vary in a bounded forward window. -/
import UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedTenCharacteristicLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenCharacteristicCompactness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode displacement_bound)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "ψ" => fun n t => evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t
include hm hg hk hz

theorem evolved_encoded_uniform (T η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ z : Coefficients, ‖z‖ ≤ ρ → ‖operator volume (h n) (encode z) (ψ n t)-ψ n t‖ < η := by
  obtain ⟨r,hr,N,hN⟩ := KFCausalClockFloorDisplacedTenCharacteristicLimit.evolved_encoded_uniform
    ε a hε ha m g k s p hm hg hk h hne hh hz T (η/2) (by positivity)
  obtain ⟨r',hr',M,hM⟩ := KFCausalNeutralPositionFrequencyControl.phase_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T (η/2) (by positivity)
  refine ⟨min r r',lt_min hr hr',max N M,?_⟩
  intro n hn t ht z hzn
  have htime : |t-s| ≤ T := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hten := hN n ((le_max_left N M).trans hn) t ht z.1
    ((norm_fst_le z).trans (hzn.trans (min_le_left r r')))
  have hpos := hM n ((le_max_right N M).trans hn) t z.2 htime
    ((norm_snd_le z).trans (hzn.trans (min_le_right r r')))
  exact (displacement_bound (h n) z (ψ n t)).trans_lt (by linarith)

theorem sampled_equicontinuity (T : ℝ) (t : ℕ → ℝ) (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    EventuallyLocallyEquicontinuous (fun n z => characteristic volume (h n) (ψ n (t n)) (encode z)) := by
  apply KFCausalEncodedCharacteristicCompactness.equicontinuity volume encode h hz (fun n => ψ n (t n))
    (fun n => evolvedState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p (t n))
  intro η hη
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_encoded_uniform ε a hε ha m g k s p hm hg hk h hne hh hz T η hη
  exact ⟨ρ,hρ,N,fun n hn z hzn => hN n hn (t n) (ht n) z hzn⟩

theorem sampled_continuous_limit (T : ℝ) (t : ℕ → ℝ) (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : Coefficients → ℂ, Continuous χ ∧
      (∀ z, Tendsto (fun n => characteristic volume (h (φ n)) (ψ (φ n) (t (φ n))) (encode z))
        atTop (𝓝 (χ z))) ∧ ∀ z, ‖χ z‖ ≤ 1 := by
  apply exists_continuous_subsequence
    (fun n z => characteristic volume (h n) (ψ n (t n)) (encode z))
  · intro n z
    simpa only [evolvedState_norm,one_pow] using
      KFCausalCanonicalWeylAlgebra.characteristic_bound volume (h n) (ψ n (t n)) (encode z)
  · exact sampled_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz T t ht

theorem sampled_classical_limit (T : ℝ) (t : ℕ → ℝ) (ht : ∀ n, t n ∈ Set.Icc s (s+T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : Coefficients → ℂ,
      Continuous χ ∧ χ 0 = 1 ∧ (∀ z, ‖χ z‖ ≤ 1) ∧
      (∀ z, χ (-z) = starRingEnd ℂ (χ z)) ∧
      (∀ N : ℕ, ∀ z : Fin N → Coefficients, ∀ c : Fin N → ℂ,
        0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).re ∧
          (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).im = 0) ∧
      (∀ z, Tendsto (fun n => characteristic volume (h (φ n)) (ψ (φ n) (t (φ n))) (encode z))
        atTop (𝓝 (χ z))) := by
  obtain ⟨φ,hφ,χ,hχ,hc,hbound⟩ := sampled_continuous_limit
    ε a hε ha m g k s p hm hg hk h hne hh hz T t ht
  have hf (n : ℕ) : ‖ψ (φ n) (t (φ n))‖ = 1 :=
    evolvedState_norm ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p (t (φ n))
  have hz' := hz.comp hφ.tendsto_atTop
  refine ⟨φ,hφ,χ,hχ,?_,hbound,?_,?_,hc⟩
  · exact KFCausalEncodedCharacteristicLimit.limit_zero volume encode (fun n => h (φ n))
      (fun n => ψ (φ n) (t (φ n))) hf χ hc
  · exact KFCausalEncodedCharacteristicLimit.limit_conjugate volume encode (fun n => h (φ n)) hz'
      (fun n => ψ (φ n) (t (φ n))) hf χ hc
  · exact KFCausalEncodedCharacteristicLimit.limit_positive_kernel volume encode (fun n => h (φ n)) hz'
      (fun n => ψ (φ n) (t (φ n))) hf χ hc

#print axioms evolved_encoded_uniform
#print axioms sampled_equicontinuity
#print axioms sampled_continuous_limit
#print axioms sampled_classical_limit

end
end UnifiedTheory.Audit.KFCausalElevenCharacteristicCompactness
