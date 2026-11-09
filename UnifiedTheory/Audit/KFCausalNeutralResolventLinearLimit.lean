/- Uniform neutral resolvent rates and vanishing explicit quadratic
remainder for actual boosted evolutions. The integral of the linear response
recovers original characteristics in the joint limit. Its classical
identification remains a separate, unproved problem. -/
import UnifiedTheory.Audit.KFCausalDisplacedNeutralResolventDynamics
import UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralResolventLinearLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralResolventDynamics
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (trajectory_energy_window)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (windowBudget errorBound errorBound_tendsto between_window)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear weightedQuadratic)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalNeutralWeightTime (speedBound_nonneg)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "B" => fun T : ℝ => windowBudget ε a m g k s T p
local notation "C" => ‖weightedQuadratic (energyWeight m g k 0)‖
local notation "R" => fun n : ℕ => rate ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "L" => fun n : ℕ => linearRate ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "Q" => fun n : ℕ => quadraticRate ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "Z" => fun n : ℕ => residual ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem rate_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ v t : ℝ, |t-s| ≤ T →
      ‖R n r t v‖ ≤ speedConstant ε a m g k s T p v := by
  have hsmall : ∀ᶠ n in atTop, |h n| ≤ 1 :=
    (hz.abs.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))).mono (fun _ hn => hn.le)
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T,hsmall]
    with n hn hs
  intro r hr v t ht
  exact (rate_energy_bound ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk r t v 1 hr hs).trans
    (mul_le_mul_of_nonneg_left (hn t ht) (speedBound_nonneg _ 1 v (by norm_num)))

theorem linear_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ v t : ℝ, |t-s| ≤ T →
      ‖L n r t v‖ ≤ 2*|v| *‖weightedLinear (energyWeight m g k 0)‖*B T := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T] with n hn
  intro r hr v t ht
  exact (linearRate_energy_bound ε a (h n) hε ha (hne n) (hh n) m g k s p r t v hr).trans
    (mul_le_mul_of_nonneg_left (hn t ht) (by positivity))

theorem quadratic_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ v t : ℝ, |t-s| ≤ T →
      ‖Q n r t v‖ ≤ 2*|h n| *|v|^2*C*B T := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T] with n hn
  intro r hr v t ht
  exact (quadraticRate_energy_bound ε a (h n) hε ha (hne n) (hh n) m g k s p r t v hr).trans
    (mul_le_mul_of_nonneg_left (hn t ht) (by positivity))

theorem quadratic_tendsto (T V : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (v t : ℕ → ℝ) (hv : ∀ n, |v n| ≤ V) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => Q n (r n) (t n) (v n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => 2*|h n| *V^2*C*B T) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero,zero_mul] using (((hz.abs.const_mul 2).mul_const (V^2)).mul_const C).mul_const (B T)
  apply squeeze_zero_norm' _ hs
  filter_upwards [quadratic_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  apply (hn (r n) (hr n) (v n) (t n) (ht n)).trans
  have hv2 := pow_le_pow_left₀ (abs_nonneg (v n)) (hv n) 2
  have hB := (KFCausalClockFloorMovingResolventWindow.windowBudget_positive ε a m g k s T p).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 (by positivity)) (norm_nonneg _)) hB

theorem linearization_tendsto (T V : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (v t : ℕ → ℝ) (hv : ∀ n, |v n| ≤ V) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => R n (r n) (t n) (v n)-L n (r n) (t n) (v n)) atTop (𝓝 0) := by
  have he (n : ℕ) : R n (r n) (t n) (v n)-L n (r n) (t n) (v n) = Q n (r n) (t n) (v n) := by
    dsimp only
    rw [rate_polynomial ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk _ _ _ (hr n)]
    ring
  simpa only [he] using quadratic_tendsto ε a hε ha m g k s p hm hg hk h hne hh hz T V r hr v t hv ht

theorem residual_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
      ‖Z n r v b c‖ ≤ errorBound (B T) T r+4*|T| *|h n| *|v|^2*C*B T := by
  filter_upwards [quadratic_window ε a hε ha m g k s p hm hg hk h hne hh hz T,
    KFCausalClockFloorCanonicalMovingBalance.residual_window
      ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T] with n hn hz'
  intro r hr v b c hb hc
  have hi : ‖∫ t in b..c, Q n r t v‖ ≤ (2*|h n| *|v|^2*C*B T)*|c-b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hn r hr v t (between_window s T b c t hb hc ht))
  have hd : |c-b| ≤ 2*|T| := by
    have hs := abs_sub_le c s b
    rw [abs_sub_comm s b] at hs
    linarith [le_abs_self T]
  have hB := (KFCausalClockFloorMovingResolventWindow.windowBudget_positive ε a m g k s T p).le
  have hi' : ‖∫ t in b..c, Q n r t v‖ ≤ 4*|T| *|h n| *|v|^2*C*B T :=
    hi.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))
  rw [residual_decomposition ε a (h n) hε ha (hne n) (hh n) m g k s p hm hg hk r v b c hr]
  exact (norm_sub_le _ _).trans (add_le_add (hz' r hr (frequency v) b c hb hc) hi')

theorem residual_tendsto (T V : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (v b c : ℕ → ℝ)
    (hv : ∀ n, |v n| ≤ V) (hb : ∀ n, |b n-s| ≤ T) (hc : ∀ n, |c n-s| ≤ T) :
    Tendsto (fun n => Z n (r n) (v n) (b n) (c n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => errorBound (B T) T (r n)+4*|T| *|h n| *V^2*C*B T) atTop (𝓝 0) := by
    have he := (((hz.abs.const_mul (4*|T|)).mul_const (V^2)).mul_const C).mul_const (B T)
    simpa only [abs_zero,mul_zero,zero_mul,add_zero] using (errorBound_tendsto (B T) T r hrtop).add he
  apply squeeze_zero_norm' _ hs
  filter_upwards [residual_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  apply (hn (r n) (hr n) (v n) (b n) (c n) (hb n) (hc n)).trans
  have hv2 := pow_le_pow_left₀ (abs_nonneg (v n)) (hv n) 2
  have hB := (KFCausalClockFloorMovingResolventWindow.windowBudget_positive ε a m g k s T p).le
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 (by positivity)) (norm_nonneg _)) hB)

#print axioms rate_window
#print axioms linear_window
#print axioms quadratic_window
#print axioms quadratic_tendsto
#print axioms linearization_tendsto
#print axioms residual_window
#print axioms residual_tendsto
end
end UnifiedTheory.Audit.KFCausalNeutralResolventLinearLimit
