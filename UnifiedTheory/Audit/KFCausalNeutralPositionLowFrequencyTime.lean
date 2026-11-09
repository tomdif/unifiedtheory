/- At sufficiently small position frequency the bare characteristic
changes arbitrarily little over an entire fixed time window. Dyadic
response cancellation and uniform cutoff removal supply the estimate;
no spatial-tightness or negative-clock-momentum input is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicApproximation
import UnifiedTheory.Audit.KFCausalDyadicWindowChoice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLowFrequencyTime
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic (bare)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicApproximation (uniform_mean_approximation)
open UnifiedTheory.Audit.KFCausalDyadicWindowChoice (exists_small_window)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (initialBudget initialBudget_positive)

theorem low_frequency_time_window (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g k s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ V : ℝ, 0 < V ∧ ∃ M : ℕ, ∀ n ≥ M, ∀ v b c : ℝ,
      |v| ≤ V → |b-s| ≤ T → |c-s| ≤ T →
      ‖bare ε a (h n) hε ha (hne n) (hh n) m g k s p v c-
        bare ε a (h n) hε ha (hne n) (hh n) m g k s p v b‖ < η := by
  obtain ⟨D,hD,M,hM⟩ := uniform_mean_approximation ε a hε ha m g k s p hm hg hk h hne hh hz
    T (η/3) (by positivity)
  let B := Real.exp (2*T)*initialBudget ε a m g k s p
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (initialBudget_positive _ _ _ _ _ _ _).le
  obtain ⟨N,hN,δ,hδ,hd,V,hV,hsmall⟩ := exists_small_window ε B D (η/(3*(2*|T|+1)))
    hε hB hD (by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (expectation_window ε a hε ha m g k s p hm hg hk h hne hh hz T)
  refine ⟨V,hV,max M K,?_⟩
  intro n hn v b c hv hb hc
  let R := fun t => characteristic ε hε (h n) δ v N hδ (hh n) (hne n) m g k s t
    (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)
  let F := fun t => bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t
  have heb : ‖R b-F b‖ < η/3 := hM n ((le_max_left M K).trans hn) N hN δ hδ hd v b hb
  have hec : ‖R c-F c‖ < η/3 := hM n ((le_max_left M K).trans hn) N hN δ hδ hd v c hc
  have hr : ‖R c-R b‖ ≤ windowBound ε δ v N B*|c-b| :=
    hK n ((le_max_right M K).trans hn) N hN δ hδ v b c hb hc
  have htime : |c-b| ≤ 2*|T| := by
    have htri : |c-b| ≤ |c-s|+|b-s| := by
      simpa only [Real.dist_eq,abs_sub_comm s b] using dist_triangle c s b
    linarith [le_abs_self T]
  have hrate := (lt_div_iff₀ (by positivity : 0 < 3*(2*|T|+1))).mp (hsmall v hv)
  have hnB := windowBound_nonneg ε δ v N B hε hB
  have hmid : ‖R c-R b‖ < η/3 := by
    have ht := mul_le_mul_of_nonneg_left htime hnB
    nlinarith
  have hc' : ‖F c-R c‖ < η/3 := by simpa only [norm_sub_rev] using hec
  have htri := (norm_sub_le_norm_sub_add_norm_sub (F c) (R c) (F b)).trans
    (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub (R c) (R b) (F b)))
  change ‖F c-F b‖ < η
  linarith

#print axioms low_frequency_time_window

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLowFrequencyTime
