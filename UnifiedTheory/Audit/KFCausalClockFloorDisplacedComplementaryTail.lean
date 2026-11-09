/- The actual propagated boosted states have uniformly small tails in
both complementary coordinate groups, including the neutral term, on
finite time windows along each admissible small-hbar sequence. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol (complementaryWeight)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound (reference_clock_graph_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)

theorem reference_complementaryMoment_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ) (i : Fin 2)
    (u : FormSpace ε hε h hh hb m g κ 0) :
    Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical (embedding ε hε h hh hb m g κ 0 u)) x‖^2) ∧
    complementaryMoment ε h i (embedding ε hε h hh hb m g κ 0 u) ≤
      2*timeEnergy ε hε h hh hb m g κ t u := by
  let v := formTransfer ε hε h hh hb m g κ 0 t u
  have hi := (form_complementaryMoment_bound ε hε h hh m g κ t hb i v).1
  have he := (form_complementaryMoment_bound ε hε h hh m g κ t hb i v).2
  have hJ := transfer_embedding ε hε h hh hb m g κ 0 t u
  refine ⟨(congrArg (fun f : Hilbert => Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2)) hJ).mp hi,?_⟩
  exact (congrArg (complementaryMoment ε h i) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun r : ℝ => 2*r) (timeEnergy_actual ε hε h hh hb m g κ t u)))

theorem reference_complementaryTail_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t R : ℝ) (i : Fin 2)
    (u : FormSpace ε hε h hh hb m g κ 0) :
    R*complementaryTail h R i (embedding ε hε h hh hb m g κ 0 u) ≤
      2*timeEnergy ε hε h hh hb m g κ t u := by
  obtain ⟨y,hy,hclock⟩ := reference_clock_graph_bound ε hε h hh m g κ t hb u
  have hcharge := reference_complementaryMoment_bound ε hε h hh hb m g κ t i u
  have he := complementaryTail_bound ε hε h R i _ y hy hcharge.1
  linarith [hcharge.2]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)

theorem evolved_complementaryMoment_bound (t : ℝ) (i : Fin 2) :
    Integrable (fun x => complementaryWeight ε h i x*
      ‖(dualPhysical (evolvedState ε a h hε ha hh hb m g κ s p t)) x‖^2) ∧
    complementaryMoment ε h i (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      2*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  have he := reference_complementaryMoment_bound ε hε h hh hb m g κ t i
    (trajectory ε a h hε ha hh hb m g κ s p t)
  rwa [trajectory_embedding] at he

theorem evolved_complementaryTail_bound (t R : ℝ) (i : Fin 2) :
    R*complementaryTail h R i (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      2*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  have he := reference_complementaryTail_bound ε hε h hh hb m g κ t R i
    (trajectory ε a h hε ha hh hb m g κ s p t)
  rwa [trajectory_embedding] at he

omit h hh hb in
theorem evolved_complementary_tail (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ i : Fin 2,
      complementaryTail (h n) R i (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by
  let B := Real.exp (2*T)*initialBudget ε a m g κ s p
  obtain ⟨R,hR⟩ := exists_gt (max 0 (2*B/η))
  have hR0 : 0 < R := (le_max_left _ _).trans_lt hR
  have hlarge : 2*B/η < R := (le_max_right _ _).trans_lt hR
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T)
  refine ⟨R,hR0,N,fun n hn t ht i => ?_⟩
  have he := (evolved_complementaryTail_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t R i).trans
    (mul_le_mul_of_nonneg_left (hN n hn t ht) (by norm_num : (0:ℝ) ≤ 2))
  have hl : 2*B < R*η := (div_lt_iff₀ hη).mp hlarge
  exact (mul_lt_mul_iff_right₀ hR0).mp (he.trans_lt hl)

#print axioms reference_complementaryMoment_bound
#print axioms reference_complementaryTail_bound
#print axioms evolved_complementaryMoment_bound
#print axioms evolved_complementaryTail_bound
#print axioms evolved_complementary_tail

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedComplementaryTail
