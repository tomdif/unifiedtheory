/- Uniform exclusion of escape to minus infinity in the log-clock coordinate,
for the actual evolved canonical boosts on each finite forward time window.
The floor and initial clock width remain fixed. This is one marginal tail
estimate, not identification of a full classical phase-space limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLeftTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentWindow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)

theorem defect_left_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (defect ε) atBot (𝓝 1) := by
  simpa only [zero_add,div_self hε.ne'] using
    (tendsto_const_nhds (x := ε)).div (Real.tendsto_exp_atBot.add_const ε)
      (by simpa only [zero_add] using hε.ne')

theorem exists_left_threshold (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∃ S : ℝ, S ≤ 0 ∧ (1:ℝ)/2 < (defect ε S)^(k+1) := by
  have ht : Tendsto (fun S => (defect ε S)^(k+1)) atBot (𝓝 1) := by
    simpa only [one_pow] using (defect_left_limit ε hε).pow (k+1)
  exact ((eventually_le_atBot (0:ℝ)).and
    (ht.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))).exists

theorem leftMass_nonnegative (S : ℝ) (f : Hilbert) : 0 ≤ leftMass S f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem evolved_clock_left_tail (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ S : ℝ, S ≤ 0 ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      leftMass S (evolution ε hε (h n) (hh n) (hb n) m g κ s t
        (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))) < η := by
  obtain ⟨k,hk⟩ := ((initialMoment_tendsto_zero ε a hε ha).eventually
    (gt_mem_nhds (by linarith : (0:ℝ) < η/4))).exists
  obtain ⟨S,hS,hthreshold⟩ := exists_left_threshold ε hε k
  obtain ⟨N,hN⟩ := clockMoment_uniform_small ε a hε ha m g κ s p k hm hg hκ
    h hh hb hz T (η/4) (by linarith)
  refine ⟨S,hS,N,fun n hn t ht => ?_⟩
  have hmoment := hN n hn t ht
  have hmarkov := leftMass_moment_bound ε hε k S
    (evolution ε hε (h n) (hh n) (hb n) m g κ s t
      (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2)))
  have hhalf := mul_le_mul_of_nonneg_right hthreshold.le (leftMass_nonnegative S
    (evolution ε hε (h n) (hh n) (hb n) m g κ s t
      (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))))
  change moment ε hε k _ < initialMoment ε a k+η/4 at hmoment
  linarith

#print axioms defect_left_limit
#print axioms exists_left_threshold
#print axioms leftMass_nonnegative
#print axioms evolved_clock_left_tail

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLeftTail
