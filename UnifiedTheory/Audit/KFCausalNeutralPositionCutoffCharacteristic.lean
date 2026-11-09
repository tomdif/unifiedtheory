/- The localized expectations approximate the actual canonical
neutral-position characteristic of the evolving quantum state, uniformly
in all frequencies and bounded time windows. No position limit or
Hamiltonian response is postulated. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharacteristic
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator operator_coe characteristic scalar)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (frequency frequency_apply)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics (input input_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def localizedExpectation (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) : ℂ :=
  inner ℂ f (input ε δ v hε hδ f)

theorem operator_phase (h v : ℝ) (f : Hilbert) :
    operator volume h (frequency v,(0:Configuration)) f = KFCausalNeutralPositionCharge.action v f := by
  apply Lp.ext
  filter_upwards [operator_coe volume h (frequency v,(0:Configuration)) f,
    KFCausalNeutralPositionCharge.action_coe v f] with x ho ha
  simp only [smul_zero,add_zero,frequency_apply] at ho
  exact ho.trans ha.symm

theorem characteristic_integral (h v : ℝ) (f : Hilbert) :
    characteristic volume h f (frequency v,(0:Configuration)) =
      ∫ x : Configuration, scalar (v*x.2 4)*(‖f x‖^2:ℝ) := by
  rw [characteristic,operator_phase,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [KFCausalNeutralPositionCharge.action_coe v f] with x hx
  rw [hx]
  simpa only [smul_eq_mul,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow] using
    inner_smul_right (𝕜 := ℂ) (f x) (f x) (scalar (v*x.2 4))

theorem localizedExpectation_integral (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    localizedExpectation ε δ v hε hδ f =
      ∫ x : Configuration, (KFCausalNeutralPositionLocalizedLimit.damping δ x:ℂ)*
        scalar (v*x.2 4)*(‖f x‖^2:ℝ) := by
  rw [localizedExpectation,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [input_coe ε δ v hε hδ f] with x hx
  rw [hx,KFCausalNeutralPositionLocalizedLimit.physicalPhase_damping]
  simpa only [smul_eq_mul,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow] using
    inner_smul_right (𝕜 := ℂ) (f x) (f x)
      ((KFCausalNeutralPositionLocalizedLimit.damping δ x:ℂ)*scalar (v*x.2 4))

theorem characteristic_difference_bound (ε δ v h : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    ‖localizedExpectation ε δ v hε hδ f-characteristic volume h f (frequency v,(0:Configuration))‖ ≤
      ‖f‖*‖input ε δ v hε hδ f-KFCausalNeutralPositionCharge.action v f‖ := by
  rw [localizedExpectation,characteristic,operator_phase]
  exact KFCausalNeutralPositionCutoffTail.expectation_difference ε δ v hε hδ f

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)

def difference (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) : ℂ :=
  localizedExpectation ε δ v hε hδ (evolvedState ε a h hε ha hne hb m g κ s p t)-
    characteristic volume h (evolvedState ε a h hε ha hne hb m g κ s p t)
      (frequency v,(0:Configuration))

theorem difference_norm (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) :
    ‖difference ε a h hε ha hne hb m g κ s p δ hδ v t‖ ≤
      ‖KFCausalNeutralPositionCutoffEvolution.error ε a h hε ha hne hb m g κ s p δ hδ v t‖ := by
  simpa only [difference,KFCausalNeutralPositionCutoffEvolution.error,evolvedState_norm,one_mul] using
    characteristic_difference_bound ε δ v h hε hδ (evolvedState ε a h hε ha hne hb m g κ s p t)

omit h hne hb in
theorem uniform_difference_limit (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) (T : ℝ) :
    TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => difference ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) z.1 z.2)
      (fun _ => (0:ℂ)) atTop {z | |z.2-s| ≤ T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [KFCausalNeutralPositionCutoffEvolution.sequence_window
    ε a hε ha m g κ s p hm hg hκ h hne hb hz δ hδ hd T η hη] with n hn
  intro z hz'
  rw [dist_zero_left]
  exact (difference_norm ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) z.1 z.2).trans_lt
    (hn z.1 z.2 hz')

omit h hne hb in
theorem moving_difference_limit (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)
    (hd : Tendsto δ atTop (𝓝 0)) (T : ℝ) (v t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, |t n-s| ≤ T) :
    Tendsto (fun n => difference ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) (v n) (t n)) atTop
      (𝓝 (0:ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [KFCausalNeutralPositionCutoffEvolution.sequence_window
    ε a hε ha m g κ s p hm hg hκ h hne hb hz δ hδ hd T η hη,ht] with n hn ht'
  rw [dist_zero_right]
  exact (difference_norm ε a (h n) hε ha (hne n) (hb n) m g κ s p (δ n) (hδ n) (v n) (t n)).trans_lt
    (hn (v n) (t n) ht')

#print axioms operator_phase
#print axioms characteristic_integral
#print axioms localizedExpectation_integral
#print axioms characteristic_difference_bound
#print axioms difference_norm
#print axioms uniform_difference_limit
#print axioms moving_difference_limit

end
end UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharacteristic
