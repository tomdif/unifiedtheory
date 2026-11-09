/- Energy and form-norm bounds, uniform along every admissible small-hbar
sequence on finite time windows, for actual evolved canonical boosts.
The initial bound is derived from the full initial-energy limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialEnergy (boostedEnergy boosted_initial_energy_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (formTransfer)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy transported_form_norm)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)

def initialBudget (ε a m g κ s : ℝ) (p : Configuration) : ℝ :=
  |∫ u, hamiltonian ε m g κ s (0,toPaired p) u p.1 ∂clockLaw ε a|+1

theorem initialBudget_positive (ε a m g κ s : ℝ) (p : Configuration) :
    0 < initialBudget ε a m g κ s p := by unfold initialBudget; positivity

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g κ s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
  (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))

include hm hg hκ hz

theorem referenceState_energy_tendsto :
    Tendsto (fun n => timeEnergy ε hε (h n) (hh n) (hb n) m g κ s
      (referenceState ε a (h n) hε ha (hh n) (hb n) m g κ s p)) atTop
      (𝓝 (∫ u, hamiltonian ε m g κ s (0,toPaired p) u p.1 ∂clockLaw ε a)) := by
  simp_rw [referenceState_energy]
  exact boosted_initial_energy_tendsto ε a hε ha m g κ s p hm hg hκ h hh hb hz

theorem initial_energy_eventually_le :
    ∀ᶠ n in atTop, boostedEnergy ε a (h n) hε ha (hh n) (hb n) m g κ s p ≤ initialBudget ε a m g κ s p := by
  have ht := boosted_initial_energy_tendsto ε a hε ha m g κ s p hm hg hκ h hh hb hz
  have hbgt : (∫ u, hamiltonian ε m g κ s (0,toPaired p) u p.1 ∂clockLaw ε a) < initialBudget ε a m g κ s p := by
    unfold initialBudget
    linarith [le_abs_self (∫ u, hamiltonian ε m g κ s (0,toPaired p) u p.1 ∂clockLaw ε a)]
  exact (ht.eventually (gt_mem_nhds hbgt)).mono (fun _ hn => hn.le)

theorem trajectory_energy_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T →
      timeEnergy ε hε (h n) (hh n) (hb n) m g κ t
        (trajectory ε a (h n) hε ha (hh n) (hb n) m g κ s p t) ≤
          Real.exp (2*T)*initialBudget ε a m g κ s p := by
  filter_upwards [initial_energy_eventually_le ε a hε ha m g κ s p hm hg hκ h hh hb hz] with n hn
  intro t ht
  apply (trajectory_energy_bound ε a (h n) hε ha (hh n) (hb n) m g κ s p t).trans
  exact (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [ht]))
      (initialBudget_positive ε a m g κ s p).le)

theorem trajectory_form_norm_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T →
      ‖formTransfer ε hε (h n) (hh n) (hb n) m g κ 0 t
        (trajectory ε a (h n) hε ha (hh n) (hb n) m g κ s p t)‖^2 ≤
          1+Real.exp (2*T)*initialBudget ε a m g κ s p := by
  filter_upwards [trajectory_energy_window ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
  intro t ht
  rw [transported_form_norm,trajectory_norm,one_pow]
  exact add_le_add le_rfl (hn t ht)

#print axioms initialBudget_positive
#print axioms referenceState_energy_tendsto
#print axioms initial_energy_eventually_le
#print axioms trajectory_energy_window
#print axioms trajectory_form_norm_window

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
