/- The actual evolved log-clock Born laws are probability measures and are
eventually uniformly tight on every finite forward window in the small-hbar
family. This controls one marginal, without identifying a classical flow. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLeftTail
import UnifiedTheory.Audit.KFCausalClockPositionLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLeftTail (evolved_clock_left_tail)
open UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass
open UnifiedTheory.Audit.KFCausalClockPositionLaw

def evolvedClockLaw (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) : Measure ℝ :=
  clockPositionLaw (evolvedState ε a h hε ha hh hb m g κ s p t)

theorem evolvedClockLaw_probability (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) :
    IsProbabilityMeasure (evolvedClockLaw ε a h hε ha hh hb m g κ s p t) :=
  clockPositionLaw_probability _ (evolvedState_norm ε a h hε ha hh hb m g κ s p t)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η)

include hm hg hκ hz hη

theorem evolved_clock_compact_tail :
    ∃ S R : ℝ, S ≤ 0 ∧ 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      outsideMass S R (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by
  obtain ⟨S,hS,NL,hL⟩ := evolved_clock_left_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (η/2) (by linarith)
  obtain ⟨R,hR,NR,hRtail⟩ := evolved_clock_right_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (η/2) (by linarith)
  refine ⟨S,R,hS,hR,max NL NR,fun n hn t ht => ?_⟩
  have hleft := hL n (le_trans (le_max_left NL NR) hn) t ht
  have hright := hRtail n (le_trans (le_max_right NL NR) hn) t (by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2])
  have hbound := outsideMass_le_tails S R
    (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
  change KFCausalClockFloorClockMomentLaw.leftMass S
    (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η/2 at hleft
  linarith

theorem evolved_clock_law_tight :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      evolvedClockLaw ε a (h n) hε ha (hh n) (hb n) m g κ s p t Kᶜ < ENNReal.ofReal η := by
  obtain ⟨S,R,_,_,N,hN⟩ := evolved_clock_compact_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T η hη
  refine ⟨Set.Icc S R,isCompact_Icc,N,fun n hn t ht => ?_⟩
  rw [evolvedClockLaw,clockPositionLaw_outside]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (outsideMass_nonnegative S R _)).mpr (hN n hn t ht)

#print axioms evolvedClockLaw_probability
#print axioms evolved_clock_compact_tail
#print axioms evolved_clock_law_tight

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTightness
