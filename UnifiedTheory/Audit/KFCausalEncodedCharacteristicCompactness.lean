/- Derived near-identity Weyl control gives continuous subsequential limits
on a separable linear family of frequencies. -/
import UnifiedTheory.Audit.KFCausalCanonicalCharacteristicIncrement
import UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalEncodedCharacteristicCompactness
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalCanonicalCharacteristicIncrement
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem equicontinuity (L : V →L[ℝ] Frequency (X := X))
    (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Lp ℂ 2 μ) (hf : ∀ n, ‖f n‖ = 1)
    (hs : ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ d : V, ‖d‖ ≤ ρ → ‖operator μ (h n) (L d) (f n)-f n‖ < η) :
    EventuallyLocallyEquicontinuous (fun n x => characteristic μ (h n) (f n) (L x)) := by
  intro x η hη
  obtain ⟨ρ, hρ, N, hN⟩ := hs (η / 2) (by positivity)
  have hp : Tendsto (fun n => |h n| * (‖L‖ * ‖(L x).2‖)) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul_const (‖L‖ * ‖(L x).2‖)
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_order.mp hp).2 (η / 2) (by positivity))
  refine ⟨min ρ 1, lt_min hρ zero_lt_one, max N M, ?_⟩
  intro n hn y hy
  have hd : ‖y-x‖ < min ρ 1 := by simpa only [dist_eq_norm] using hy
  have hdρ := (hd.trans_le (min_le_left ρ 1)).le
  have hd1 := (hd.trans_le (min_le_right ρ 1)).le
  have ht := hN n ((le_max_left N M).trans hn) (y-x) hdρ
  have hp' := hM n ((le_max_right N M).trans hn)
  have hb := mul_le_mul_of_nonneg_left (encoded_pairing_bound L x (y-x) hd1) (abs_nonneg (h n))
  have hi := characteristic_increment μ (h n) (f n) (hf n) (L x) (L (y-x))
  have hsum : L x+L (y-x) = L y := by rw [map_sub]; abel
  rw [hsum] at hi
  rw [dist_eq_norm]
  exact hi.trans_lt (lt_of_le_of_lt (add_le_add (le_refl _) hb)
    (by linarith))

theorem exists_continuous_limit [SeparableSpace V]
    (L : V →L[ℝ] Frequency (X := X))
    (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0))
    (f : ℕ → Lp ℂ 2 μ) (hf : ∀ n, ‖f n‖ = 1)
    (hs : ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ d : V, ‖d‖ ≤ ρ → ‖operator μ (h n) (L d) (f n)-f n‖ < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : V → ℂ, Continuous χ ∧
      (∀ x, Tendsto (fun n => characteristic μ (h (φ n)) (f (φ n)) (L x)) atTop (𝓝 (χ x))) ∧
      ∀ x, ‖χ x‖ ≤ 1 := by
  apply exists_continuous_subsequence (fun n x => characteristic μ (h n) (f n) (L x))
  · intro n x
    simpa only [hf,one_pow] using characteristic_bound μ (h n) (f n) (L x)
  · exact equicontinuity μ L h hz f hf hs

#print axioms equicontinuity
#print axioms exists_continuous_limit

end
end UnifiedTheory.Audit.KFCausalEncodedCharacteristicCompactness
