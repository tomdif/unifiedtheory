/- The full radial response is uniformly bounded in sufficiently small
hbar on each finite time window along the actual boosted evolution.
The resulting expectation is uniformly Lipschitz in time at fixed
positive cutoffs. The constants are not uniform in cutoff removal. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialResponseWindow
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState referenceState_norm trajectory)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (initialBudget trajectory_energy_window)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (kineticConstant)

def windowBound (ε δ v B : ℝ) : ℝ := responseConstant ε δ v*B+2*kineticConstant ε δ v*Real.sqrt B

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))

include hε hz in
theorem eventually_half_strip : ∀ᶠ n in atTop, |h n| ≤ Real.pi*ε/3 := by
  have ht : Tendsto (fun n => |h n|) atTop (𝓝 (0:ℝ)) := by simpa only [abs_zero] using hz.abs
  exact (ht.eventually (gt_mem_nhds (by positivity : (0:ℝ) < Real.pi*ε/3))).mono (fun _ hn => hn.le)

include hm hg hk hz in
theorem rate_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ v t : ℝ, |t-s| ≤ T →
      ‖exactRate ε hε (h n) δ v hδ (hh n) (hne n) m g k s t
        (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
        windowBound ε δ v (Real.exp (2*T)*initialBudget ε a m g k s p) := by
  filter_upwards [eventually_half_strip ε hε h hz,
    trajectory_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn hE
  intro δ hδ v t ht
  have hb := exactRate_energy_bound ε hε (h n) δ v hδ (hh n) (hne n) m g k hn s t
    (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)
  have hb' : ‖exactRate ε hε (h n) δ v hδ (hh n) (hne n) m g k s t
      (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
      responseConstant ε δ v*timeEnergy ε hε (h n) (hne n) (hh n) m g k t
        (trajectory ε a (h n) hε ha (hne n) (hh n) m g k s p t)+
      2*kineticConstant ε δ v*Real.sqrt (timeEnergy ε hε (h n) (hne n) (hh n) m g k t
        (trajectory ε a (h n) hε ha (hne n) (hh n) m g k s p t)) := by
    simpa only [referenceState_norm,mul_one] using hb
  exact hb'.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hE t ht) (responseConstant_nonneg ε δ v hε))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hE t ht))
      (mul_nonneg (by norm_num) (KFCausalNeutralPositionRadialKineticGraph.responseConstant_nonneg ε δ v))))

include hm hg hk hz in
theorem expectation_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
      ‖characteristic ε hε (h n) δ v hδ (hh n) (hne n) m g k s c
          (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)-
        characteristic ε hε (h n) δ v hδ (hh n) (hne n) m g k s b
          (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
        windowBound ε δ v (Real.exp (2*T)*initialBudget ε a m g k s p)*|c-b| := by
  filter_upwards [rate_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro δ hδ v b c hb hc
  have hmem (x : ℝ) : x ∈ Set.Icc (s-T) (s+T) ↔ |x-s| ≤ T := by
    rw [Set.mem_Icc,abs_le]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1,hx.2]
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (s-T) (s+T)) =>
      (expectation_derivative ε hε (h n) δ v hδ (hh n) (hne n) m g k s t
        (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)).hasDerivWithinAt)
    (fun t ht => hn δ hδ v t ((hmem t).mp ht)) (convex_Icc (s-T) (s+T))
    ((hmem b).mpr hb) ((hmem c).mpr hc)
  simpa only [Real.norm_eq_abs] using hd

#print axioms eventually_half_strip
#print axioms rate_window
#print axioms expectation_window

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialResponseWindow
