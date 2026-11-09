/- Uniform removal of the moving-resolvent correction. The original
observable increments are approximated by integrals of the bounded
physical resolvent commutator, with a derived energy-controlled error. -/
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorResolventWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000

namespace UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (initialBudget initialBudget_positive trajectory_energy_window)
open UnifiedTheory.Audit.KFCausalClockFloorResolventBalance (expectation expectation_unit_error)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest

theorem balance_difference_bound (X Y x y I : ℂ) :
    ‖(X-Y-I)-(x-y)‖ ≤ ‖X-x‖+‖Y-y‖+‖I‖ := by
  calc
    _ = ‖((X-Y)-(x-y))-I‖ := congrArg norm (by ring)
    _ ≤ ‖(X-Y)-(x-y)‖+‖I‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (KFCausalClockFloorResolventBalance.difference_bound X Y x y) le_rfl

theorem between_window (s T b c t : ℝ) (hb : |b-s| ≤ T) (hc : |c-s| ≤ T)
    (ht : t ∈ Set.uIoc b c) : |t-s| ≤ T := by
  obtain ⟨hbl,hbu⟩ := abs_le.mp hb
  obtain ⟨hcl,hcu⟩ := abs_le.mp hc
  have hlo : s-T ≤ min b c := le_min (by linarith) (by linarith)
  have hhi : max b c ≤ s+T := max_le (by linarith) (by linarith)
  exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

def errorBound (B T r : ℝ) : ℝ :=
  4*Real.sqrt (B/(4*r))+4*|T| *Real.sqrt (B/r)

theorem errorBound_tendsto (B T : ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => errorBound B T (r n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (B/r n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds.div_atTop hr)
  simpa only [errorBound,mul_zero,add_zero] using
    (KFCausalClockFloorResolventWindow.error_bound_tendsto B 4 r hr).add (hs.const_mul (4*|T|))

section Fixed
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "X" => expectation ε hε h hne hh m g k
local notation "C" => characteristic ε hε h hne hh m g k
local notation "R" => boundedRate ε hε h hne hh m g k
local notation "K" => correctionRate ε hε h hne hh m g k

def residual (r : ℝ) (D : Hilbert →L[ℂ] Hilbert) (s b c : ℝ) (w : V₀) : ℂ :=
  (∫ t in b..c, R r D s t w)-(X D s c w-X D s b w)

theorem correction_unit_bound (r : ℝ) (hr : 0 < r) (D : Hilbert →L[ℂ] Hilbert)
    (hD : ‖D‖ ≤ 1) (s t : ℝ) (w : V₀) (hw : ‖J w‖ = 1)
    (B : ℝ) (hB : E t (F s t w) ≤ B) :
    ‖K r D s t w‖ ≤ 2*Real.sqrt (B/r) := by
  have hb := correctionRate_bound ε hε h hne hh m g k r hr D s t w
  rw [hw,mul_one] at hb
  exact hb.trans (mul_le_mul (by linarith : 2*‖D‖ ≤ 2)
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB hr.le)) (Real.sqrt_nonneg _) (by norm_num))

theorem residual_bound (r : ℝ) (hr : 0 < r) (D : Hilbert →L[ℂ] Hilbert)
    (hD : ‖D‖ ≤ 1) (s b c : ℝ) (w : V₀) (hw : ‖J w‖ = 1)
    (B : ℝ) (hb : E b (F s b w) ≤ B) (hc : E c (F s c w) ≤ B)
    (hE : ∀ t ∈ Set.uIoc b c, E t (F s t w) ≤ B) :
    ‖residual ε hε h hne hh m g k r D s b c w‖ ≤
      4*Real.sqrt (B/(4*r))+2*Real.sqrt (B/r)*|c-b| := by
  have hb' := expectation_unit_error ε hε h hne hh m g k r b hr D hD s b w hw B hb
  have hc' := expectation_unit_error ε hε h hne hh m g k r c hr D hD s c w hw B hc
  have hI : ‖∫ t in b..c, K r D s t w‖ ≤ 2*Real.sqrt (B/r)*|c-b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => correction_unit_bound ε hε h hne hh m g k r hr D hD s t w hw B (hE t ht))
  have hi := boundedRate_integral ε hε h hne hh m g k r hr D s b c w
  have htri := balance_difference_bound (C r D s c w) (C r D s b w) (X D s c w) (X D s b w)
    (∫ t in b..c, K r D s t w)
  exact (congrArg (fun z : ℂ => ‖z-(X D s c w-X D s b w)‖) hi).le.trans
    (htri.trans ((add_le_add (add_le_add hc' hb') hI).trans_eq (by ring)))
end Fixed

def windowBudget (ε a m g k s T : ℝ) (p : Configuration) : ℝ :=
  Real.exp (2*T)*initialBudget ε a m g k s p

theorem windowBudget_positive (ε a m g k s T : ℝ) (p : Configuration) :
    0 < windowBudget ε a m g k s T p :=
  mul_pos (Real.exp_pos _) (initialBudget_positive ε a m g k s p)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "W" => fun n : ℕ => referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "B" => fun T : ℝ => windowBudget ε a m g k s T p
local notation "K" => fun (n : ℕ) (r : ℝ) (D : Hilbert →L[ℂ] Hilbert) (t : ℝ) =>
  correctionRate ε hε (h n) (hne n) (hh n) m g k r D s t (W n)
local notation "Z" => fun (n : ℕ) (r : ℝ) (D : Hilbert →L[ℂ] Hilbert) (b c : ℝ) =>
  residual ε hε (h n) (hne n) (hh n) m g k r D s b c (W n)

include hm hg hk hz

theorem correction_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ D : Hilbert →L[ℂ] Hilbert, ‖D‖ ≤ 1 →
      ∀ t : ℝ, |t-s| ≤ T → ‖K n r D t‖ ≤ 2*Real.sqrt (B T/r) := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr D hD t ht
  exact correction_unit_bound ε hε (h n) (hne n) (hh n) m g k r hr D hD s t (W n)
    (referenceState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p) (B T) (hn t ht)

theorem residual_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ D : Hilbert →L[ℂ] Hilbert, ‖D‖ ≤ 1 →
      ∀ b c : ℝ, |b-s| ≤ T → |c-s| ≤ T → ‖Z n r D b c‖ ≤ errorBound (B T) T r := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr D hD b c hb hc
  have hbound := residual_bound ε hε (h n) (hne n) (hh n) m g k r hr D hD s b c (W n)
    (referenceState_norm ε a (h n) hε ha (hne n) (hh n) m g k s p) (B T)
    (hn b hb) (hn c hc) (fun t ht => hn t (between_window s T b c t hb hc ht))
  have hd : |c-b| ≤ 2*|T| := by
    have hs := abs_sub_le c s b
    rw [abs_sub_comm s b] at hs
    linarith [le_abs_self T]
  have hm : 2*Real.sqrt (B T/r)*|c-b| ≤ 2*Real.sqrt (B T/r)*(2*|T|) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  exact hbound.trans ((add_le_add le_rfl hm).trans_eq (by unfold errorBound; ring))

theorem correction_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (D : ℕ → Hilbert →L[ℂ] Hilbert) (hD : ∀ n, ‖D n‖ ≤ 1)
    (t : ℕ → ℝ) (ht : ∀ n, |t n-s| ≤ T) :
    Tendsto (fun n => K n (r n) (D n) (t n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => 2*Real.sqrt (B T/r n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds.div_atTop hrtop)).const_mul (2:ℝ)
  apply squeeze_zero_norm' _ hs
  filter_upwards [correction_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (D n) (hD n) (t n) (ht n)

theorem residual_tendsto (T : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto r atTop atTop) (D : ℕ → Hilbert →L[ℂ] Hilbert) (hD : ∀ n, ‖D n‖ ≤ 1)
    (b c : ℕ → ℝ) (hb : ∀ n, |b n-s| ≤ T) (hc : ∀ n, |c n-s| ≤ T) :
    Tendsto (fun n => Z n (r n) (D n) (b n) (c n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (errorBound_tendsto (B T) T r hrtop)
  filter_upwards [residual_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (D n) (hD n) (b n) (c n) (hb n) (hc n)

#print axioms balance_difference_bound
#print axioms between_window
#print axioms errorBound_tendsto
#print axioms correction_unit_bound
#print axioms residual_bound
#print axioms windowBudget_positive
#print axioms correction_window
#print axioms residual_window
#print axioms correction_tendsto
#print axioms residual_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow
