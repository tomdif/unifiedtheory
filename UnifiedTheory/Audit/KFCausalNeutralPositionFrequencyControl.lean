/- Actual neutral-position tails give frequency equicontinuity and
uniform small-frequency displacement of the physical phase operator.
No unweighted position moment or clock-momentum bound is assumed. -/
import UnifiedTheory.Audit.KFCausalProbabilityFrequencyTail
import UnifiedTheory.Audit.KFCausalNeutralPositionWindowTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionFrequencyControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic (bare)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (law law_characteristic snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)

theorem phase_displacement_square (v : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖action v f-f‖^2 ≤ 2*‖1-charFun (law f) v‖ := by
  rw [law_characteristic,norm_sub_rev,@norm_sub_sq ℂ, (action v).norm_map,hf]
  have hn := Complex.re_le_norm (1-inner ℂ f (action v f))
  simp only [Complex.sub_re,Complex.one_re] at hn
  change 1^2-2*(inner ℂ f (action v f)).re+1^2 ≤ _
  linarith

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "μ" => fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem frequency_window (T η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t v w : ℝ,
      |t-s| ≤ T → |v-w| ≤ ρ →
      ‖bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t-
        bare ε a (h n) hε ha (hne n) (hh n) m g k s p w t‖ < η := by
  simpa only [snapshot_characteristic] using
    KFCausalProbabilityFrequencyTail.frequency_window μ s T
      (KFCausalNeutralPositionWindowTightness.position_tail_window ε a hε ha m g k s p
        hm hg hk h hne hh hz T) η hη

theorem phase_window (T η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t v : ℝ,
      |t-s| ≤ T → |v| ≤ ρ →
      ‖action v (evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t)-
        evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t‖ < η := by
  obtain ⟨ρ,hρ,N,hN⟩ := KFCausalProbabilityFrequencyTail.frequency_window μ s T
    (KFCausalNeutralPositionWindowTightness.position_tail_window ε a hε ha m g k s p
      hm hg hk h hne hh hz T) (η^2/4) (by positivity)
  refine ⟨ρ,hρ,N,?_⟩
  intro n hn t v ht hv
  have hc := hN n hn t v 0 ht (by simpa only [sub_zero] using hv)
  have hs := phase_displacement_square v
    (evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t)
    (evolvedState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p t)
  have he : (μ n t : Measure ℝ) = law (evolvedState ε a (h n) hε ha (hne n) (hh n) m g k s p t) := rfl
  simp only [charFun_zero,probReal_univ,Complex.ofReal_one,norm_sub_rev] at hc
  rw [he] at hc
  nlinarith

#print axioms phase_displacement_square
#print axioms frequency_window
#print axioms phase_window

end
end UnifiedTheory.Audit.KFCausalNeutralPositionFrequencyControl
