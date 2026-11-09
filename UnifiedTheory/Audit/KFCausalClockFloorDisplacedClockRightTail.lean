/- The actual evolved boosted states have finite clock energy at every time.
The proved uniform evolved-energy bound controls the upper log-clock tail
over finite windows, with no charge-zero condition on the states. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound
import UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState boostedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound (reference_clock_graph_bound)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)

def evolvedState (t : ℝ) : Hilbert :=
  evolution ε hε h hh hb m g κ s t (boostedState ε a h hε ha hh (positionFrequency p.1 p.2))

theorem evolvedState_norm (t : ℝ) : ‖evolvedState ε a h hε ha hh hb m g κ s p t‖ = 1 :=
  ((evolution ε hε h hh hb m g κ s t).norm_map _).trans (boostedState_norm ε a h hε ha hh _)

theorem evolved_clock_graph_bound (t : ℝ) : ∃ y : Hilbert,
    (evolvedState ε a h hε ha hh hb m g κ s p t,y) ∈ (clockHalf ε).graph ∧
    ‖y‖^2 ≤ 2*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  obtain ⟨y,hy,he⟩ := reference_clock_graph_bound ε hε h hh m g κ t hb
    (trajectory ε a h hε ha hh hb m g κ s p t)
  rw [trajectory_embedding] at hy
  exact ⟨y,hy,he⟩

theorem evolved_clock_mass_bound (t : ℝ) :
    clockMass ε (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      2*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  obtain ⟨y,hy,he⟩ := evolved_clock_graph_bound ε a h hε ha hh hb m g κ s p t
  rwa [clockMass_eq ε hε _ y hy]

theorem evolved_rightMass_bound (t R : ℝ) :
    Real.exp R*rightMass R (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      2*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  obtain ⟨y,hy,he⟩ := evolved_clock_graph_bound ε a h hε ha hh hb m g κ s p t
  exact (rightMass_clock_bound ε hε R _ y hy).trans he

omit h hh hb in
theorem evolved_clock_right_tail (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      rightMass R (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by
  let B := Real.exp (2*T)*initialBudget ε a m g κ s p
  obtain ⟨R,hR,hlarge⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (Real.tendsto_exp_atTop.eventually (eventually_gt_atTop (2*B/η)))).exists
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T)
  refine ⟨R,hR,N,fun n hn t ht => ?_⟩
  have he := (evolved_rightMass_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t R).trans
    (mul_le_mul_of_nonneg_left (hN n hn t ht) (by norm_num : (0:ℝ) ≤ 2))
  have hl : 2*B < Real.exp R*η := (div_lt_iff₀ hη).mp hlarge
  have hx : Real.exp R*rightMass R (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < Real.exp R*η :=
    he.trans_lt hl
  exact (mul_lt_mul_iff_right₀ (Real.exp_pos R)).mp hx

#print axioms evolvedState_norm
#print axioms evolved_clock_graph_bound
#print axioms evolved_clock_mass_bound
#print axioms evolved_rightMass_bound
#print axioms evolved_clock_right_tail

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail
