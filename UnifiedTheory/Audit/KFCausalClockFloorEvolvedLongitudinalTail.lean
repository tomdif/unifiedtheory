/- Uniform positive longitudinal spectral tails for the weighted charge orbit
of the actual evolved states. Negative longitudinal momentum and canonical
clock momentum are not controlled by this result. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedLongitudinalTail
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedLongitudinalTail
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedLongitudinalTail
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_nonneg)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (trajectory trajectory_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

theorem evolved_positive_tail (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration) (hκ : 0 < κ) (t R : ℝ) :
    orbitPositiveTail ε hε h hh R (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      ENNReal.ofReal ((Real.exp (-R)/(Real.exp (2*t)*κ))*
        timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t)) := by
  have he := reference_positive_tail ε hε h hh m g κ t R hb hκ
    (trajectory ε a h hε ha hh hb m g κ s p t)
  have hJ := trajectory_embedding ε a h hε ha hh hb m g κ s p t
  exact (congrArg (orbitPositiveTail ε hε h hh R) hJ).symm.trans_le he

theorem evolved_positive_tail_window (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      orbitPositiveTail ε hε (h n) (hh n) R
        (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < ENNReal.ofReal η := by
  let B := Real.exp (2*T)*initialBudget ε a m g κ s p
  let d := Real.exp (2*(s-T))*κ
  have hB : 0 < B := mul_pos (Real.exp_pos _) (initialBudget_positive ε a m g κ s p)
  have hd : 0 < d := mul_pos (Real.exp_pos _) hκ
  have hlim : Tendsto (fun R : ℝ => Real.exp (-R)/d*B) atTop (𝓝 0) := by
    simpa only [zero_div,zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.div_const d).mul_const B
  obtain ⟨R,hR,hsmall⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (hlim.eventually (gt_mem_nhds hη))).exists
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (trajectory_energy_window ε a hε ha m g κ s p hm hg hκ.le h hh hb hz T)
  refine ⟨R,hR,N,fun n hn t ht => ?_⟩
  have hden : d ≤ Real.exp (2*t)*κ := by
    apply mul_le_mul_of_nonneg_right _ hκ.le
    apply Real.exp_le_exp.mpr
    have ht' := (abs_le.mp ht).1
    linarith
  have hc := div_le_div_of_nonneg_left (Real.exp_pos (-R)).le hd hden
  have he := mul_le_mul hc (hN n hn t ht)
    (timeEnergy_nonneg ε hε (h n) (hh n) (hb n) m g κ t _) (div_nonneg (Real.exp_pos (-R)).le hd.le)
  have hsmall' : ENNReal.ofReal (Real.exp (-R)/d*B) < ENNReal.ofReal η :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hsmall
  exact (evolved_positive_tail ε a (h n) hε ha (hh n) (hb n) m g κ s p hκ t R).trans_lt
    ((ENNReal.ofReal_le_ofReal he).trans_lt hsmall')

#print axioms evolved_positive_tail
#print axioms evolved_positive_tail_window

end
end UnifiedTheory.Audit.KFCausalClockFloorEvolvedLongitudinalTail
