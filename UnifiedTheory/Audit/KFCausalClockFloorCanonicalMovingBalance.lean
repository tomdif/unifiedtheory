/- Every actual canonical phase test satisfies the current-time resolvent
balance. Its bounded physical commutator integral recovers the original
characteristic increment with a uniform vanishing error. No classical
identification of that commutator limit is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalResolventBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCanonicalMovingBalance
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (Frequencies positionFrequency evolvedCharacteristic)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests (regularizer)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalResolventBalance (test test_norm_le_one expectation_eq_evolved)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (windowBudget errorBound)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

section Fixed
variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
local notation "W" => referenceState ε a h hε ha hne hh m g k s p
local notation "f" => boostedState ε a h hε ha hne (positionFrequency (Prod.fst p) (Prod.snd p))
local notation "U" => evolution ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k

def regularized (r t : ℝ) (z : Frequencies) : ℂ :=
  KFCausalClockFloorMovingResolventEhrenfest.characteristic ε hε h hne hh m g k r (test h z) s t W

def rate (r t : ℝ) (z : Frequencies) : ℂ :=
  KFCausalClockFloorMovingResolventEhrenfest.boundedRate ε hε h hne hh m g k r (test h z) s t W

def correction (r t : ℝ) (z : Frequencies) : ℂ :=
  KFCausalClockFloorMovingResolventEhrenfest.correctionRate ε hε h hne hh m g k r (test h z) s t W

def residual (r : ℝ) (z : Frequencies) (b c : ℝ) : ℂ :=
  (∫ t in b..c, rate ε a h hε ha hne hh m g k s p r t z)-
    (evolvedCharacteristic ε hε h hne hh m g k s c f z-
      evolvedCharacteristic ε hε h hne hh m g k s b f z)

theorem rate_formula (r t : ℝ) (z : Frequencies) :
    rate ε a h hε ha hne hh m g k s p r t z =
      coefficient h*(r:ℂ)*inner ℂ (U s t f)
        (test h z (R r t (U s t f))-R r t (test h z (U s t f))) := by
  have he := congrArg (U s t) (referenceState_embedding ε a h hε ha hne hh m g k s p)
  exact congrArg (fun v : Hilbert => coefficient h*(r:ℂ)*inner ℂ v
    (test h z (R r t v)-R r t (test h z v))) he

theorem expectation_derivative (r : ℝ) (hr : 0 < r) (t : ℝ) (z : Frequencies) :
    HasDerivAt (fun u => regularized ε a h hε ha hne hh m g k s p r u z)
      (rate ε a h hε ha hne hh m g k s p r t z+
        correction ε a h hε ha hne hh m g k s p r t z) t :=
  KFCausalClockFloorMovingResolventEhrenfest.expectation_derivative
    ε hε h hne hh m g k r hr (test h z) s t W

theorem rate_continuous (r : ℝ) (hr : 0 < r) (z : Frequencies) :
    Continuous (fun t => rate ε a h hε ha hne hh m g k s p r t z) :=
  KFCausalClockFloorMovingResolventEhrenfest.boundedRate_continuous
    ε hε h hne hh m g k r hr (test h z) s W

theorem residual_eq_form (r : ℝ) (z : Frequencies) (b c : ℝ) :
    residual ε a h hε ha hne hh m g k s p r z b c =
      KFCausalClockFloorMovingResolventWindow.residual ε hε h hne hh m g k r (test h z) s b c W := by
  simp only [residual,rate,KFCausalClockFloorMovingResolventWindow.residual,expectation_eq_evolved]
end Fixed

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "B" => fun T : ℝ => windowBudget ε a m g k s T p
local notation "K" => fun n : ℕ => correction ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "Z" => fun n : ℕ => residual ε a (h n) hε ha (hne n) (hh n) m g k s p

include hm hg hk hz

theorem correction_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ z : Frequencies, ∀ t : ℝ, |t-s| ≤ T →
      ‖K n r t z‖ ≤ 2*Real.sqrt (B T/r) := by
  filter_upwards [KFCausalClockFloorMovingResolventWindow.correction_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr z t ht
  exact hn r hr (test (h n) z) (test_norm_le_one _ _) t ht

theorem residual_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ z : Frequencies, ∀ b c : ℝ,
      |b-s| ≤ T → |c-s| ≤ T → ‖Z n r z b c‖ ≤ errorBound (B T) T r := by
  filter_upwards [KFCausalClockFloorMovingResolventWindow.residual_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr z b c hb hc
  simpa only [residual_eq_form] using hn r hr (test (h n) z) (test_norm_le_one _ _) b c hb hc

theorem correction_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (z : ℕ → Frequencies)
    (t : ℕ → ℝ) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => K n (r n) (t n) (z n)) atTop (𝓝 0) :=
  KFCausalClockFloorMovingResolventWindow.correction_tendsto
    ε a hε ha m g k s p hm hg hk h hne hh hz T r hr hrtop
    (fun n => test (h n) (z n)) (fun n => test_norm_le_one (h n) (z n)) t ht

theorem residual_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (z : ℕ → Frequencies)
    (b c : ℕ → ℝ) (hb : ∀ n, |b n-s| ≤ T) (hc : ∀ n, |c n-s| ≤ T) :
    Tendsto (fun n => Z n (r n) (z n) (b n) (c n)) atTop (𝓝 0) := by
  simpa only [residual_eq_form] using
    KFCausalClockFloorMovingResolventWindow.residual_tendsto
      ε a hε ha m g k s p hm hg hk h hne hh hz T r hr hrtop
      (fun n => test (h n) (z n)) (fun n => test_norm_le_one (h n) (z n)) b c hb hc

#print axioms rate_formula
#print axioms expectation_derivative
#print axioms rate_continuous
#print axioms residual_eq_form
#print axioms correction_window
#print axioms residual_window
#print axioms correction_tendsto
#print axioms residual_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorCanonicalMovingBalance
