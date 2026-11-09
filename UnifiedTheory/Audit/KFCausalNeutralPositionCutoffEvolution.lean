/- Uniform Gaussian cutoff removal on the actual normalized boosted
quantum evolution. The charged tail is supplied by the existing energy
theorem. Cutoff width and Planck parameter may vanish at independent rates;
this asserts L2 approximation, not convergence in energy graph norm. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionCutoffEvolution
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (input)
open UnifiedTheory.Audit.KFCausalNeutralPositionCutoffTail (norm_difference_tail)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedChargedTail (evolved_planeTail_bound evolved_plane_tail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (trajectory)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)

def error (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) : Hilbert :=
  input ε δ v hε hδ (evolvedState ε a h hε ha hne hb m g κ s p t)-
    KFCausalNeutralPositionCharge.action v (evolvedState ε a h hε ha hne hb m g κ s p t)

theorem squared_error_tail (δ : ℝ) (hδ : 0 < δ) (v t R : ℝ) :
    ‖error ε a h hε ha hne hb m g κ s p δ hδ v t‖^2 ≤
      4*δ^2*R^4+planeTail h R 1 (evolvedState ε a h hε ha hne hb m g κ s p t) := by
  simpa only [error,evolvedState_norm,one_pow,mul_one] using
    norm_difference_tail ε δ v hε hδ h R (evolvedState ε a h hε ha hne hb m g κ s p t)

theorem squared_error_energy (δ : ℝ) (hδ : 0 < δ) (v t R : ℝ) (hR : 0 < R) :
    ‖error ε a h hε ha hne hb m g κ s p δ hδ v t‖^2 ≤
      4*δ^2*R^4+(1+Real.exp (-2*t))*timeEnergy ε hε h hne hb m g κ t
        (trajectory ε a h hε ha hne hb m g κ s p t)/R := by
  apply (squared_error_tail ε a h hε ha hne hb m g κ s p δ hδ v t R).trans
  apply add_le_add le_rfl
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using evolved_planeTail_bound ε a h hε ha hne hb m g κ s p t R 1

omit h hne hb in
theorem uniform_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < D →
      ∀ v t : ℝ, |t-s| ≤ T → ‖error ε a (h n) hε ha (hne n) (hb n) m g κ s p δ hδ v t‖ < η := by
  obtain ⟨R,hR,N,hN⟩ := evolved_plane_tail ε a hε ha m g κ s p hm hg hκ
    h hne hb hz T (η^2/2) (by positivity)
  refine ⟨η/(4*R^2),by positivity,N,?_⟩
  intro n hn δ hδ hd v t ht
  have hsmall : δ*(4*R^2) < η := (lt_div_iff₀ (by positivity : 0 < 4*R^2)).mp hd
  have hs : 4*δ^2*R^4 ≤ η^2/4 := by
    have hb' : 2*δ*R^2 ≤ η/2 := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*δ*R^2) hb' 2
    nlinarith only [hp]
  have he := squared_error_tail ε a (h n) hε ha (hne n) (hb n) m g κ s p δ hδ v t R
  have ht' := hN n hn t ht 1
  nlinarith [norm_nonneg (error ε a (h n) hε ha (hne n) (hb n) m g κ s p δ hδ v t),sq_pos_of_pos hη]

omit h hne hb in
theorem sequence_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ v t : ℝ, |t-s| ≤ T →
      ‖error ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) v t‖ < η := by
  obtain ⟨D,hD,N,hN⟩ := uniform_window ε a hε ha m g κ s p hm hg hκ h hne hb hz T η hη
  filter_upwards [eventually_ge_atTop N,hd.eventually (gt_mem_nhds hD)] with n hn hd'
  exact hN n hn (δ n) (hδ n) hd'

omit h hne hb in
theorem uniform_error_limit (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) (T : ℝ) :
    TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => error ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) z.1 z.2)
      (fun _ => (0:Hilbert)) atTop {z | |z.2-s| ≤ T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [sequence_window ε a hε ha m g κ s p hm hg hκ h hne hb hz δ hδ hd T η hη] with n hn
  intro z hz'
  simpa only [dist_zero_left] using hn z.1 z.2 hz'

omit h hne hb in
theorem moving_error_limit (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) (T : ℝ) (v t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, |t n-s| ≤ T) :
    Tendsto (fun n => error ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) (v n) (t n)) atTop
      (𝓝 (0:Hilbert)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [sequence_window ε a hε ha m g κ s p hm hg hκ h hne hb hz δ hδ hd T η hη,ht] with n hn ht'
  simpa only [dist_zero_right] using hn (v n) (t n) ht'

#print axioms squared_error_tail
#print axioms squared_error_energy
#print axioms uniform_window
#print axioms sequence_window
#print axioms uniform_error_limit
#print axioms moving_error_limit

end
end UnifiedTheory.Audit.KFCausalNeutralPositionCutoffEvolution
