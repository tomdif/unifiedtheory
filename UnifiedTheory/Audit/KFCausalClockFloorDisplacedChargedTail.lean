/- Actual propagated boosted states have uniformly small tails in both
charged mixed planes, eventually along admissible small-hbar sequences
on finite time windows. This uses derived quantum moment bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargedTail
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (chargedWeight)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound (reference_clock_graph_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)

theorem reference_chargedMoment_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t : ℝ) (i : Fin 2)
    (u : FormSpace ε hε h hh hb m g κ 0) :
    Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates (embedding ε hε h hh hb m g κ 0 u)) x‖^2) ∧
    chargedMoment ε h i (embedding ε hε h hh hb m g κ 0 u) ≤
      2*Real.exp (-2*t)*timeEnergy ε hε h hh hb m g κ t u := by
  let v := formTransfer ε hε h hh hb m g κ 0 t u
  have hi := (form_chargedMoment_bound ε hε h hh m g κ t hb i v).1
  have he := (form_chargedMoment_bound ε hε h hh m g κ t hb i v).2
  have hJ := transfer_embedding ε hε h hh hb m g κ 0 t u
  refine ⟨(congrArg (fun f : Hilbert => Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2)) hJ).mp hi,?_⟩
  exact (congrArg (chargedMoment ε h i) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun r : ℝ => 2*Real.exp (-2*t)*r)
      (timeEnergy_actual ε hε h hh hb m g κ t u)))

theorem reference_planeTail_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ t R : ℝ) (i : Fin 2)
    (u : FormSpace ε hε h hh hb m g κ 0) :
    R*planeTail h R i (embedding ε hε h hh hb m g κ 0 u) ≤
      (1+Real.exp (-2*t))*timeEnergy ε hε h hh hb m g κ t u := by
  obtain ⟨y,hy,hclock⟩ := reference_clock_graph_bound ε hε h hh m g κ t hb u
  have hcharge := reference_chargedMoment_bound ε hε h hh hb m g κ t i u
  have he := planeTail_bound ε hε h R i _ y hy hcharge.1
  nlinarith [hcharge.2]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)

theorem evolved_chargedMoment_bound (t : ℝ) (i : Fin 2) :
    Integrable (fun x => chargedWeight ε h i x*
      ‖(chargeCoordinates (evolvedState ε a h hε ha hh hb m g κ s p t)) x‖^2) ∧
    chargedMoment ε h i (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      2*Real.exp (-2*t)*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  have he := reference_chargedMoment_bound ε hε h hh hb m g κ t i
    (trajectory ε a h hε ha hh hb m g κ s p t)
  rwa [trajectory_embedding] at he

theorem evolved_planeTail_bound (t R : ℝ) (i : Fin 2) :
    R*planeTail h R i (evolvedState ε a h hε ha hh hb m g κ s p t) ≤
      (1+Real.exp (-2*t))*timeEnergy ε hε h hh hb m g κ t (trajectory ε a h hε ha hh hb m g κ s p t) := by
  have he := reference_planeTail_bound ε hε h hh hb m g κ t R i
    (trajectory ε a h hε ha hh hb m g κ s p t)
  rwa [trajectory_embedding] at he

omit h hh hb in
theorem evolved_plane_tail (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T → ∀ i : Fin 2,
      planeTail (h n) R i (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t) < η := by
  let B := Real.exp (2*T)*initialBudget ε a m g κ s p
  let D := (1+Real.exp (-2*s+2*T))*B
  obtain ⟨R,hR⟩ := exists_gt (max 0 (D/η))
  have hR0 : 0 < R := (le_max_left _ _).trans_lt hR
  have hlarge : D/η < R := (le_max_right _ _).trans_lt hR
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T)
  refine ⟨R,hR0,N,fun n hn t ht i => ?_⟩
  have htime : -2*t ≤ -2*s+2*T := by
    have ht' := (abs_le.mp ht).1
    linarith
  have he := (evolved_planeTail_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t R i).trans
    (mul_le_mul (add_le_add (le_refl 1) (Real.exp_le_exp.mpr htime)) (hN n hn t ht)
      (timeEnergy_nonneg ε hε (h n) (hh n) (hb n) m g κ t _) (by positivity))
  have hl : D < R*η := (div_lt_iff₀ hη).mp hlarge
  exact (mul_lt_mul_iff_right₀ hR0).mp (he.trans_lt hl)

#print axioms reference_chargedMoment_bound
#print axioms reference_planeTail_bound
#print axioms evolved_chargedMoment_bound
#print axioms evolved_planeTail_bound
#print axioms evolved_plane_tail

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail
