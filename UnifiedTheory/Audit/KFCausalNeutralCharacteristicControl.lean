/- Neutral momentum tests have exact additive frequencies and no ordering
phase error. Existing physical tails give a frequency modulus uniform in time. -/
import UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumTestControl
import UnifiedTheory.Audit.KFCausalCanonicalCharacteristicIncrement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralCharacteristicControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (vector)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator characteristic)
open UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta (physicalDirection)
open UnifiedTheory.Audit.KFCausalComplementaryMomentumTests (momentumTest)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem frequency_add (v w : ℝ) : frequency (v+w) = frequency v+frequency w := by
  apply Prod.ext
  · simp [frequency]
  · apply Prod.ext
    · simp [frequency,vector]
    · funext i
      fin_cases i <;> simp [frequency,vector]

theorem frequency_zero : frequency 0 = 0 := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [frequency,vector]

theorem frequency_momentum (v : ℝ) : frequency v = (0,(0,v • physicalDirection 2)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp [frequency,vector,physicalDirection]

theorem characteristic_zero (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    characteristic volume h f (frequency 0) = 1 := by
  simp only [frequency_zero,characteristic,KFCausalCanonicalWeylAlgebra.operator_zero,
    inner_self_eq_norm_sq_to_K,hf]
  norm_num

theorem characteristic_increment (h v w : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (frequency v)-characteristic volume h f (frequency w)‖ ≤
      ‖momentumTest h (v-w) 2 f-f‖ := by
  have hi := KFCausalCanonicalCharacteristicIncrement.characteristic_increment volume h f hf
    (frequency w) (frequency (v-w))
  have hs : frequency w+frequency (v-w) = frequency v := by
    rw [← frequency_add]
    congr 1
    ring
  rw [hs] at hi
  have hz : (frequency (v-w)).1 (frequency w).2 = 0 := rfl
  rw [hz] at hi
  simpa only [abs_zero,mul_zero,add_zero,frequency_momentum,momentumTest] using hi

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hm hg hk hz

theorem frequency_window (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t v w : ℝ,
      |t-s| ≤ T → |v-w| ≤ ρ →
      ‖KFCausalDisplacedNeutralDynamics.characteristic ε a (h n) hε ha (hne n) (hh n) m g k s p v t-
        KFCausalDisplacedNeutralDynamics.characteristic ε a (h n) hε ha (hne n) (hh n) m g k s p w t‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := KFCausalClockFloorDisplacedMomentumTestControl.evolved_momentumTest_uniform
    ε a hε ha m g k s p hm hg hk h hne hh hz T δ hδ
  refine ⟨ρ,hρ,N,?_⟩
  intro n hn t v w ht hv
  exact (characteristic_increment (h n) v w _
    (evolvedState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p t)).trans_lt
      (hN n hn t ht 2 (v-w) hv)

#print axioms frequency_add
#print axioms frequency_zero
#print axioms frequency_momentum
#print axioms characteristic_zero
#print axioms characteristic_increment
#print axioms frequency_window
end
end UnifiedTheory.Audit.KFCausalNeutralCharacteristicControl
