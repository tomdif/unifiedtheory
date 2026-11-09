/- Uniform removal of observable resolvent regularization for the actual
boosted evolutions on finite time windows. One small-hbar threshold works
for every positive resolvent scale and every bounded contraction test.
The integrated rates remain quantum form pairings. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventBalance
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventWindow
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds
open UnifiedTheory.Audit.KFCausalClockFloorResolventEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorResolventBalance

def windowBudget (ε a m g k s T : ℝ) (p : Configuration) : ℝ :=
  Real.exp (4*T)*initialBudget ε a m g k s p

theorem windowBudget_positive (ε a m g k s T : ℝ) (p : Configuration) :
    0 < windowBudget ε a m g k s T p :=
  mul_pos (Real.exp_pos _) (initialBudget_positive ε a m g k s p)

theorem error_bound_tendsto (B C : ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => C*Real.sqrt (B/(4*r n))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => B/(4*r n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hr.const_mul_atTop (by norm_num : (0:ℝ) < 4))
  simpa only [Real.sqrt_zero,mul_zero] using
    ((Real.continuous_sqrt.tendsto 0).comp hd).const_mul C

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "W" => fun n : ℕ => referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "V" => fun (n : ℕ) (t : ℝ) => trajectory ε a (h n) hε ha (hne n) (hh n) m g k s p t
local notation "E" => fun n : ℕ => timeEnergy ε hε (h n) (hne n) (hh n) m g k
local notation "B" => fun T : ℝ => windowBudget ε a m g k s T p
local notation "C" => fun (n : ℕ) (r : ℝ) (D : Hilbert →L[ℂ] Hilbert) (t : ℝ) =>
  characteristic ε hε (h n) (hne n) (hh n) m g k r s D s t (W n)
local notation "X" => fun (n : ℕ) (D : Hilbert →L[ℂ] Hilbert) (t : ℝ) =>
  expectation ε hε (h n) (hne n) (hh n) m g k D s t (W n)
local notation "R" => fun (n : ℕ) (r : ℝ) (D : Hilbert →L[ℂ] Hilbert) (t : ℝ) =>
  exactRate ε hε (h n) (hne n) (hh n) m g k r s D s t (W n)

include hm hg hk hz

theorem reference_energy_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t-s| ≤ T → E n s (V n t) ≤ B T := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro t ht
  calc
    _ ≤ Real.exp (2*|t-s|)*E n t (V n t) :=
      reference_energy_bound ε hε (h n) (hne n) (hh n) m g k s t (V n t)
    _ ≤ Real.exp (2*T)*E n t (V n t) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [ht]))
        (timeEnergy_nonneg ε hε (h n) (hne n) (hh n) m g k t (V n t))
    _ ≤ Real.exp (2*T)*(Real.exp (2*T)*initialBudget ε a m g k s p) :=
      mul_le_mul_of_nonneg_left (hn t ht) (Real.exp_pos _).le
    _ = B T := by
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem expectation_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ D : Hilbert →L[ℂ] Hilbert, ‖D‖ ≤ 1 →
      ∀ t : ℝ, |t-s| ≤ T → ‖C n r D t-X n D t‖ ≤ 2*Real.sqrt (B T/(4*r)) := by
  filter_upwards [reference_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr D hD t ht
  exact expectation_unit_error ε hε (h n) (hne n) (hh n) m g k r s hr D hD s t (W n)
    (referenceState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p) (B T) (hn t ht)

theorem balance_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ D : Hilbert →L[ℂ] Hilbert, ‖D‖ ≤ 1 →
      ∀ b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖(∫ t in b..c, R n r D t)-(X n D c-X n D b)‖ ≤ 4*Real.sqrt (B T/(4*r)) := by
  filter_upwards [reference_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr D hD b c hb hc
  exact integral_balance_error ε hε (h n) (hne n) (hh n) m g k r s hr D hD s b c (W n)
    (referenceState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p) (B T) (hn b hb) (hn c hc)

theorem expectation_error_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (D : ℕ → Hilbert →L[ℂ] Hilbert) (hD : ∀ n, ‖D n‖ ≤ 1)
    (t : ℕ → ℝ) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => C n (r n) (D n) (t n)-X n (D n) (t n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (error_bound_tendsto (B T) 2 r hrtop)
  filter_upwards [expectation_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (D n) (hD n) (t n) (ht n)

theorem balance_error_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (D : ℕ → Hilbert →L[ℂ] Hilbert) (hD : ∀ n, ‖D n‖ ≤ 1)
    (b c : ℕ → ℝ) (hb : ∀ n, |b n-s| ≤ T) (hc : ∀ n, |c n-s| ≤ T) :
    Tendsto (fun n => (∫ t in b n..c n, R n (r n) (D n) t)-
      (X n (D n) (c n)-X n (D n) (b n))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (error_bound_tendsto (B T) 4 r hrtop)
  filter_upwards [balance_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (D n) (hD n) (b n) (c n) (hb n) (hc n)

#print axioms windowBudget_positive
#print axioms error_bound_tendsto
#print axioms reference_energy_window
#print axioms expectation_window
#print axioms balance_window
#print axioms expectation_error_tendsto
#print axioms balance_error_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorResolventWindow
