/- Dyadic expectation dynamics on the actual boosted states, uniformly
along admissible small-hbar families on finite time windows. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (kineticConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState referenceState_norm trajectory)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (initialBudget trajectory_energy_window)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

def windowBound (ε δ v : ℝ) (N : ℕ) (B : ℝ) : ℝ :=
  responseConstant ε δ v N*B+2*kineticConstant ε (width δ N) v*Real.sqrt B

theorem windowBound_nonneg (ε δ v : ℝ) (N : ℕ) (B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    0 ≤ windowBound ε δ v N B := by
  have hc := responseConstant_nonneg ε δ v N hε
  have hk := KFCausalNeutralPositionRadialKineticGraph.responseConstant_nonneg ε (width δ N) v
  unfold windowBound
  positivity

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))

include hm hg hk hz in
theorem rate_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ N : ℕ, 0 < N → ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ v t : ℝ, |t-s| ≤ T →
      ‖exactRate ε hε (h n) δ v N hδ (hh n) (hne n) m g k s t
        (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
        windowBound ε δ v N (Real.exp (2*T)*initialBudget ε a m g k s p) := by
  filter_upwards [trajectory_energy_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hE
  intro N hN δ hδ v t ht
  have hb := exactRate_energy_bound ε hε (h n) δ v N hδ (hh n) (hne n) m g k hN s t
    (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)
  have hb' : ‖exactRate ε hε (h n) δ v N hδ (hh n) (hne n) m g k s t
      (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
      responseConstant ε δ v N*timeEnergy ε hε (h n) (hne n) (hh n) m g k t
        (trajectory ε a (h n) hε ha (hne n) (hh n) m g k s p t)+
      2*kineticConstant ε (width δ N) v*Real.sqrt (timeEnergy ε hε (h n) (hne n) (hh n) m g k t
        (trajectory ε a (h n) hε ha (hne n) (hh n) m g k s p t)) := by
    simpa only [referenceState_norm,mul_one] using hb
  exact hb'.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hE t ht) (responseConstant_nonneg ε δ v N hε))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hE t ht))
      (mul_nonneg (by norm_num) (KFCausalNeutralPositionRadialKineticGraph.responseConstant_nonneg ε (width δ N) v))))

include hm hg hk hz in
theorem expectation_window (T : ℝ) :
    ∀ᶠ n in atTop, ∀ N : ℕ, 0 < N → ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ v b c : ℝ,
      |b-s| ≤ T → |c-s| ≤ T →
      ‖characteristic ε hε (h n) δ v N hδ (hh n) (hne n) m g k s c
          (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)-
        characteristic ε hε (h n) δ v N hδ (hh n) (hne n) m g k s b
          (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)‖ ≤
        windowBound ε δ v N (Real.exp (2*T)*initialBudget ε a m g k s p)*|c-b| := by
  filter_upwards [rate_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro N hN δ hδ v b c hb hc
  have hmem (x : ℝ) : x ∈ Set.Icc (s-T) (s+T) ↔ |x-s| ≤ T := by
    rw [Set.mem_Icc,abs_le]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1,hx.2]
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (s-T) (s+T)) =>
      (expectation_derivative ε hε (h n) δ v N hδ (hh n) (hne n) m g k s t
        (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)).hasDerivWithinAt)
    (fun t ht => hn N hN δ hδ v t ((hmem t).mp ht)) (convex_Icc (s-T) (s+T))
    ((hmem b).mpr hb) ((hmem c).mpr hc)
  simpa only [Real.norm_eq_abs] using hd

#print axioms windowBound_nonneg
#print axioms rate_window
#print axioms expectation_window

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow
