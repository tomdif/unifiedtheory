/- The complete canonical phase-test family has an exact regularized
Ehrenfest identity. For the actual boosted evolutions, its error against
the original characteristics vanishes on arbitrary diverging resolvent
scales as hbar tends to zero, with moving frequencies and bounded times.
This does not identify a classical rate or prove full phase-space tightness. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalClockFloorCanonicalResolventBalance
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (operator)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (Frequencies positionFrequency evolvedCharacteristic)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorResolventBalance (expectation)
open UnifiedTheory.Audit.KFCausalClockFloorResolventWindow (windowBudget)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def test (h : ℝ) (z : Frequencies) : Hilbert →L[ℂ] Hilbert :=
  (operator volume h z).toLinearIsometry.toContinuousLinearMap

theorem test_norm_le_one (h : ℝ) (z : Frequencies) : ‖test h z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖operator volume h z f‖ ≤ 1*‖f‖
  rw [(operator volume h z).norm_map,one_mul]

section Fixed
variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
local notation "W" => referenceState ε a h hε ha hne hh m g k s p
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "f" => boostedState ε a h hε ha hne (positionFrequency (Prod.fst p) (Prod.snd p))

def regularized (r t : ℝ) (z : Frequencies) : ℂ :=
  KFCausalClockFloorResolventEhrenfest.characteristic ε hε h hne hh m g k r s (test h z) s t W

def rate (r t : ℝ) (z : Frequencies) : ℂ :=
  KFCausalClockFloorResolventEhrenfest.exactRate ε hε h hne hh m g k r s (test h z) s t W

theorem expectation_eq_evolved (t : ℝ) (z : Frequencies) :
    expectation ε hε h hne hh m g k (test h z) s t W =
      evolvedCharacteristic ε hε h hne hh m g k s t f z := by
  have he := congrArg (evolution ε hε h hne hh m g k s t)
    (referenceState_embedding ε a h hε ha hne hh m g k s p)
  exact congrArg (fun v : Hilbert => inner ℂ v (test h z v)) he

theorem regularized_derivative (r : ℝ) (hr : 0 < r) (t : ℝ) (z : Frequencies) :
    HasDerivAt (fun u => regularized ε a h hε ha hne hh m g k s p r u z)
      (rate ε a h hε ha hne hh m g k s p r t z) t :=
  KFCausalClockFloorResolventEhrenfest.expectation_derivative ε hε h hne hh m g k r s
    (test h z) hr s t W

theorem rate_continuous (r : ℝ) (z : Frequencies) :
    Continuous (fun t => rate ε a h hε ha hne hh m g k s p r t z) :=
  KFCausalClockFloorResolventEhrenfest.exactRate_continuous ε hε h hne hh m g k r s (test h z) s W

theorem rate_integral (r : ℝ) (hr : 0 < r) (b c : ℝ) (z : Frequencies) :
    (∫ t in b..c, rate ε a h hε ha hne hh m g k s p r t z) =
      regularized ε a h hε ha hne hh m g k s p r c z-
        regularized ε a h hε ha hne hh m g k s p r b z :=
  KFCausalClockFloorResolventEhrenfest.expectation_integral ε hε h hne hh m g k r s
    (test h z) hr s b c W
end Fixed

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "C" => fun n : ℕ => regularized ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "R" => fun n : ℕ => rate ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "X" => fun (n : ℕ) (t : ℝ) (z : Frequencies) =>
  evolvedCharacteristic ε hε (h n) (hne n) (hh n) m g k s t
    (boostedState ε a (h n) hε ha (hne n) (positionFrequency (Prod.fst p) (Prod.snd p))) z
local notation "B" => fun T : ℝ => windowBudget ε a m g k s T p

include hm hg hk hz

theorem expectation_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ z : Frequencies, ∀ t : ℝ, |t-s| ≤ T →
      ‖C n r t z-X n t z‖ ≤ 2*Real.sqrt (B T/(4*r)) := by
  filter_upwards [KFCausalClockFloorResolventWindow.expectation_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr z t ht
  simpa only [regularized,expectation_eq_evolved] using hn r hr (test (h n) z) (test_norm_le_one _ _) t ht

theorem balance_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ z : Frequencies, ∀ b c : ℝ,
      |b-s| ≤ T → |c-s| ≤ T →
        ‖(∫ t in b..c, R n r t z)-(X n c z-X n b z)‖ ≤ 4*Real.sqrt (B T/(4*r)) := by
  filter_upwards [KFCausalClockFloorResolventWindow.balance_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr z b c hb hc
  simpa only [rate,expectation_eq_evolved] using hn r hr (test (h n) z) (test_norm_le_one _ _) b c hb hc

theorem expectation_error_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (z : ℕ → Frequencies)
    (t : ℕ → ℝ) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => C n (r n) (t n) (z n)-X n (t n) (z n)) atTop (𝓝 0) := by
  simpa only [regularized,expectation_eq_evolved] using
    KFCausalClockFloorResolventWindow.expectation_error_tendsto
      ε a hε ha m g k s p hm hg hk h hne hh hz T r hr hrtop
      (fun n => test (h n) (z n)) (fun n => test_norm_le_one (h n) (z n)) t ht

theorem balance_error_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (z : ℕ → Frequencies)
    (b c : ℕ → ℝ) (hb : ∀ n, |b n-s| ≤ T) (hc : ∀ n, |c n-s| ≤ T) :
    Tendsto (fun n => (∫ t in b n..c n, R n (r n) t (z n))-
      (X n (c n) (z n)-X n (b n) (z n))) atTop (𝓝 0) := by
  simpa only [rate,expectation_eq_evolved] using
    KFCausalClockFloorResolventWindow.balance_error_tendsto
      ε a hε ha m g k s p hm hg hk h hne hh hz T r hr hrtop
      (fun n => test (h n) (z n)) (fun n => test_norm_le_one (h n) (z n)) b c hb hc

#print axioms test_norm_le_one
#print axioms expectation_eq_evolved
#print axioms regularized_derivative
#print axioms rate_continuous
#print axioms rate_integral
#print axioms expectation_window
#print axioms balance_window
#print axioms expectation_error_tendsto
#print axioms balance_error_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorCanonicalResolventBalance
