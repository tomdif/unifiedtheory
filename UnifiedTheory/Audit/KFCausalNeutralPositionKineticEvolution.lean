/- Uniform control of the kinetic contribution to neutral-position
response along the actual full quantum evolution. This is a bound on one
part of the form commutator, not a derivative theorem for position tests. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionKineticCommutator
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionKineticEvolution
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph (select)
open UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticCommutator
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)

def physicalState (t : ℝ) : Hilbert :=
  embedding ε hε h hne hh m g k 0 (trajectory ε a h hε ha hne hh m g k s p t)

def kineticOutput (t : ℝ) : OutputSpace :=
  select.compLp (energyOutput ε hε h hne hh m g k t
    (formTransfer ε hε h hne hh m g k 0 t (trajectory ε a h hε ha hne hh m g k s p t)))

def response (v t : ℝ) : ℂ :=
  commutator ε hε h hne v (physicalState ε a h hε ha hne hh m g k s p t)
    (physicalState ε a h hε ha hne hh m g k s p t)
    (kineticOutput ε a h hε ha hne hh m g k s p t)
    (kineticOutput ε a h hε ha hne hh m g k s p t)

theorem trajectory_graph (t : ℝ) :
    AveragedGraph ε h hne t (physicalState ε a h hε ha hne hh m g k s p t)
      (kineticOutput ε a h hε ha hne hh m g k s p t) := by
  have hg := completed_form_graph ε hε h hne hh m g k t
    (formTransfer ε hε h hne hh m g k 0 t (trajectory ε a h hε ha hne hh m g k s p t))
  simpa only [transfer_embedding,physicalState,kineticOutput] using hg

theorem response_energy_bound (v t : ℝ) :
    ‖response ε a h hε ha hne hh m g k s p v t‖/|h| ≤
      2*responseConstant ε v*Real.sqrt (timeEnergy ε hε h hne hh m g k t
        (trajectory ε a h hε ha hne hh m g k s p t)) := by
  have hc := completed_form_normalized_bound ε hε h hne hh m g k t v
    (formTransfer ε hε h hne hh m g k 0 t (trajectory ε a h hε ha hne hh m g k s p t))
  have hc' : ‖response ε a h hε ha hne hh m g k s p v t‖/|h| ≤
      2*responseConstant ε v*‖energyOutput ε hε h hne hh m g k t
        (formTransfer ε hε h hne hh m g k 0 t (trajectory ε a h hε ha hne hh m g k s p t))‖ := by
    simpa only [transfer_embedding,trajectory_norm,mul_one,response,physicalState,kineticOutput] using hc
  have he := Real.le_sqrt_of_sq_le (timeEnergy_actual ε hε h hne hh m g k t
    (trajectory ε a h hε ha hne hh m g k s p t)).le
  exact hc'.trans (mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num) (responseConstant_nonneg ε v)))

omit h hne hh in
theorem response_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (hs : ℕ → ℝ) (hn : ∀ n, hs n ≠ 0) (hb : ∀ n, |hs n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto hs atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ v t : ℝ, |t-s| ≤ T →
      ‖response ε a (hs n) hε ha (hn n) (hb n) m g k s p v t‖/|hs n| ≤
        2*responseConstant ε v*Real.sqrt (Real.exp (2*T)*initialBudget ε a m g k s p) := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm hg hk hs hn hb hz T] with n hn'
  intro v t ht
  exact (response_energy_bound ε a (hs n) hε ha (hn n) (hb n) m g k s p v t).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hn' t ht))
      (mul_nonneg (by norm_num) (responseConstant_nonneg ε v)))

#print axioms trajectory_graph
#print axioms response_energy_bound
#print axioms response_window

end
end UnifiedTheory.Audit.KFCausalNeutralPositionKineticEvolution
