/- Eventual uniform tightness of the actual four-dimensional charged Born
law on finite time windows. This is not full phase-space tightness or a
positive-time quantum-to-classical identification. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail
import UnifiedTheory.Audit.KFCausalClockFloorChargedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail (evolved_plane_tail)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail planeTail_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorChargedLaw

def evolvedChargedLaw (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) : Measure ChargedSpace :=
  chargedLaw h (evolvedState ε a h hε ha hh hb m g κ s p t)

theorem evolvedChargedLaw_probability (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) :
    IsProbabilityMeasure (evolvedChargedLaw ε a h hε ha hh hb m g κ s p t) :=
  chargedLaw_probability h _ (evolvedState_norm ε a h hε ha hh hb m g κ s p t)

theorem evolved_charged_law_tight (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ K : Set ChargedSpace, IsCompact K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      evolvedChargedLaw ε a (h n) hε ha (hh n) (hb n) m g κ s p t Kᶜ < ENNReal.ofReal η := by
  obtain ⟨R,hR,N,hN⟩ := evolved_plane_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (η/2) (by linarith)
  refine ⟨chargedBox R,chargedBox_compact R,N,fun n hn t ht => ?_⟩
  have h0 := hN n hn t ht 0
  have h1 := hN n hn t ht 1
  have hs : planeTail (h n) R 0 (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)+
      planeTail (h n) R 1 (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by linarith
  exact (chargedLaw_outside_le (h n) R hR.le _).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (planeTail_nonnegative (h n) R 0 _) (planeTail_nonnegative (h n) R 1 _))).mpr hs)

#print axioms evolvedChargedLaw_probability
#print axioms evolved_charged_law_tight

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTightness
