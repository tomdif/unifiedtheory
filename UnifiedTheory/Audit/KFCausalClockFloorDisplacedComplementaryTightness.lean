/- The actual evolved complementary Born laws are probability measures
and are eventually uniformly tight on finite symmetric time windows.
This is a five-dimensional marginal, not full canonical phase space. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail
import UnifiedTheory.Audit.KFCausalClockFloorComplementaryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail (evolved_complementary_tail)
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail (complementaryTail complementaryTail_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryLaw

def evolvedComplementaryLaw (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) : Measure ComplementarySpace :=
  complementaryLaw h (evolvedState ε a h hε ha hh hb m g κ s p t)

theorem evolvedComplementaryLaw_probability (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (t : ℝ) :
    IsProbabilityMeasure (evolvedComplementaryLaw ε a h hε ha hh hb m g κ s p t) :=
  complementaryLaw_probability h _ (evolvedState_norm ε a h hε ha hh hb m g κ s p t)

theorem evolved_complementary_law_tight (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ K : Set ComplementarySpace, IsCompact K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      evolvedComplementaryLaw ε a (h n) hε ha (hh n) (hb n) m g κ s p t Kᶜ < ENNReal.ofReal η := by
  obtain ⟨R,hR,N,hN⟩ := evolved_complementary_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (η/2) (by linarith)
  refine ⟨complementaryBox R,complementaryBox_compact R,N,fun n hn t ht => ?_⟩
  have h0 := hN n hn t ht 0
  have h1 := hN n hn t ht 1
  have hs : complementaryTail (h n) R 0 (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)+
      complementaryTail (h n) R 1 (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by linarith
  exact (complementaryLaw_outside_le (h n) R hR.le _).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg
      (complementaryTail_nonnegative (h n) R 0 _) (complementaryTail_nonnegative (h n) R 1 _))).mpr hs)

#print axioms evolvedComplementaryLaw_probability
#print axioms evolved_complementary_law_tight

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTightness
