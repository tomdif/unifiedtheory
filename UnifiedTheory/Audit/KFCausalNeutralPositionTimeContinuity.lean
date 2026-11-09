/- The cutoff-free canonical neutral-position characteristic is
eventually equicontinuous in time, uniformly over bounded frequencies.
Uniform charged-tail approximation and the full regulated dynamics
supply the estimate; no derivative limit or spatial tightness is assumed. -/
import UnifiedTheory.Audit.KFCausalRadialResponseFrequencyBound
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionTimeContinuity
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEvolutionBounds (initialBudget initialBudget_positive)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialResponseWindow (windowBound expectation_window)
open UnifiedTheory.Audit.KFCausalRadialResponseFrequencyBound (windowBound_nonneg windowBound_frequency)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))

include hm hg hk hz in
theorem time_equicontinuity (T V η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ v b c : ℝ,
      |v| ≤ V → |b-s| ≤ T → |c-s| ≤ T → |c-b| < ρ →
      ‖bare ε a (h n) hε ha (hne n) (hh n) m g k s p v c-
        bare ε a (h n) hε ha (hne n) (hh n) m g k s p v b‖ < η := by
  obtain ⟨D,hD,N,hN⟩ := uniform_approximation ε a hε ha m g k s p hm hg hk h hne hh hz
    T (η/3) (by positivity)
  let δ := D/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδD : δ < D := by dsimp [δ]; linarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (expectation_window ε a hε ha m g k s p hm hg hk h hne hh hz T)
  let B := Real.exp (2*T)*initialBudget ε a m g k s p
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (initialBudget_positive _ _ _ _ _ _ _).le
  let C := windowBound ε δ V B
  have hC : 0 ≤ C := windowBound_nonneg ε δ V B hε hB
  refine ⟨η/(3*(C+1)),by positivity,max N M,?_⟩
  intro n hn v b c hv hb hc hbc
  have hec := hN n ((le_max_left N M).trans hn) δ hδ hδD v c hc
  have heb := hN n ((le_max_left N M).trans hn) δ hδ hδD v b hb
  have hr := hM n ((le_max_right N M).trans hn) δ hδ v b c hb hc
  have hmid : ‖radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v c-
      radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v b‖ ≤ C*|c-b| :=
    ((congrArg₂ (fun x y : ℂ => ‖x-y‖)
      (radial_reference ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v c)
      (radial_reference ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v b)).le.trans hr).trans
        (mul_le_mul_of_nonneg_right (windowBound_frequency ε δ v V B hε hδ hB hv) (abs_nonneg _))
  have hsmall : C*|c-b| < η/3 := by
    have hx := (lt_div_iff₀ (by positivity : 0 < 3*(C+1))).mp hbc
    nlinarith [abs_nonneg (c-b)]
  have hec' : ‖bare ε a (h n) hε ha (hne n) (hh n) m g k s p v c-
      radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v c‖ < η/3 := by
    simpa only [norm_sub_rev] using hec
  have htri := (norm_sub_le_norm_sub_add_norm_sub
    (bare ε a (h n) hε ha (hne n) (hh n) m g k s p v c)
    (radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v c)
    (bare ε a (h n) hε ha (hne n) (hh n) m g k s p v b)).trans
      (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
        (radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v c)
        (radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v b)
        (bare ε a (h n) hε ha (hne n) (hh n) m g k s p v b)))
  linarith

include hm hg hk hz in
theorem moving_time_uniform (T V : ℝ) (b c : ℕ → ℝ)
    (hb : ∀ᶠ n in atTop, |b n-s| ≤ T) (hc : ∀ᶠ n in atTop, |c n-s| ≤ T)
    (hbc : Tendsto (fun n => c n-b n) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n v =>
      bare ε a (h n) hε ha (hne n) (hh n) m g k s p v (c n)-
        bare ε a (h n) hε ha (hne n) (hh n) m g k s p v (b n))
      (fun _ => (0:ℂ)) atTop {v | |v| ≤ V} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨ρ,hρ,N,hN⟩ := time_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz T V η hη
  have ht : Tendsto (fun n => |c n-b n|) atTop (𝓝 (0:ℝ)) := by simpa only [abs_zero] using hbc.abs
  filter_upwards [eventually_ge_atTop N,hb,hc,ht.eventually (gt_mem_nhds hρ)] with n hn hb' hc' hd
  intro v hv
  simpa only [dist_zero_left] using hN n hn v (b n) (c n) hv hb' hc' hd

include hm hg hk hz in
theorem moving_time_difference (T V : ℝ) (b c v : ℕ → ℝ)
    (hb : ∀ᶠ n in atTop, |b n-s| ≤ T) (hc : ∀ᶠ n in atTop, |c n-s| ≤ T)
    (hv : ∀ᶠ n in atTop, |v n| ≤ V) (hbc : Tendsto (fun n => c n-b n) atTop (𝓝 0)) :
    Tendsto (fun n => bare ε a (h n) hε ha (hne n) (hh n) m g k s p (v n) (c n)-
      bare ε a (h n) hε ha (hne n) (hh n) m g k s p (v n) (b n)) atTop (𝓝 (0:ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hu := (Metric.tendstoUniformlyOn_iff.mp
    (moving_time_uniform ε a hε ha m g k s p hm hg hk h hne hh hz T V b c hb hc hbc)) η hη
  filter_upwards [hu,hv] with n hn hv'
  simpa only [dist_zero_left,dist_zero_right] using hn (v n) hv'

#print axioms time_equicontinuity
#print axioms moving_time_uniform
#print axioms moving_time_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionTimeContinuity
