/- Positive vacuum coupling gives a strictly negative limiting initial
clock-defect rate. Sufficiently small members of the actual quantum family
therefore decrease strictly on a nonzero forward interval. Its length may
depend on hbar; no all-time strict decay or zero-defect limit is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialRateIdentification
import UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialStrictDecay
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
open UnifiedTheory.Audit.KFCausalClockFloorInitialQuantumRate
open UnifiedTheory.Audit.KFCausalClockFloorInitialRateIdentification
open UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

theorem drift_clock_negative (ε : ℝ) (hε : 0 < ε) (s : ℝ) : drift ε (defect ε s) < 0 := by
  have hd := defect_positive ε s hε
  have hr := (response_bounds ε s hε).1
  have he := response_add_defect ε s hε.le
  unfold drift
  apply div_neg_of_neg_of_pos _ hε
  exact neg_neg_of_pos (mul_pos (sq_pos_of_pos hd) (by linarith only [hr,he]))

theorem dampedClockFunction_ne_zero (ε a : ℝ) (hε : 0 < ε) (s : ℝ) :
    dampedClockFunction ε a s ≠ 0 := by
  unfold dampedClockFunction
  apply mul_ne_zero _ (clockFunction_ne_zero ε a hε.le s)
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')

theorem driftMass_negative (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : driftMass ε a < 0 := by
  have hp (s : ℝ) : 0 < -(drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2) :=
    neg_pos.mpr (mul_neg_of_neg_of_pos (drift_clock_negative ε hε s)
      (sq_pos_of_pos (norm_pos_iff.mpr (dampedClockFunction_ne_zero ε a hε s))))
  have hc : Continuous (fun s : ℝ => -(drift ε (defect ε s)*‖dampedClockFunction ε a s‖^2)) :=
    ((drift_clock_continuous ε hε).mul ((dampedClockFunction_continuous ε a hε).norm.pow 2)).neg
  have hi := (driftMass_integrable ε a hε ha).neg
  have he := integral_pos_of_integrable_nonneg_nonzero hc hi (fun s => (hp s).le) (hp 0).ne'
  rw [integral_neg] at he
  change 0 < -driftMass ε a at he
  linarith

theorem initialClassicalDrift_negative (ε a vacuum s : ℝ) (hε : 0 < ε) (ha : 0 < a) (hv : 0 < vacuum) :
    initialClassicalDrift ε a vacuum s < 0 := by
  unfold initialClassicalDrift
  exact mul_neg_of_pos_of_neg (mul_pos (Real.exp_pos _) hv)
    (div_neg_of_neg_of_pos (driftMass_negative ε a hε ha) (clockMass_positive ε a hε ha))

theorem local_strictAnti_of_continuous_rate (f r : ℝ → ℝ) (s : ℝ)
    (hd : ∀ t, HasDerivAt f (r t) t) (hc : Continuous r) (hn : r s < 0) :
    ∃ δ : ℝ, 0 < δ ∧ StrictAntiOn f (Icc s (s+δ)) := by
  have he : ∀ᶠ t in 𝓝 s, r t < 0 := hc.continuousAt.tendsto.eventually (gt_mem_nhds hn)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2,by positivity,?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc s (s+δ/2))
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
  intro t ht
  rw [(hd t).deriv]
  apply hsub
  have ht' : t ∈ Icc s (s+δ/2) := interior_subset ht
  rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht'.1)]
  linarith only [ht'.2,hδ]

theorem eventually_quantum_strict_decrease (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 < vacuum)
    (h : ℕ → ℝ) (hn : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ δ : ℝ, 0 < δ ∧
      StrictAntiOn (quantumExpectation ε a hε ha (h n) (hn n) (hb n) mass2 quartic vacuum s) (Icc s (s+δ)) := by
  have ht := exact_initial_rate_tendsto ε a hε ha mass2 quartic vacuum s hm hq hv.le h hn hb h1 hz
  have he := ht.eventually (gt_mem_nhds (initialClassicalDrift_negative ε a vacuum s hε ha hv))
  filter_upwards [he] with n hn'
  apply local_strictAnti_of_continuous_rate _ _ s
    (fun t => quantumExpectation_derivative ε a hε ha (h n) (hn n) (hb n) (h1 n)
      mass2 quartic vacuum s t hm hq hv.le)
  · exact exactRate_continuous ε hε (h n) (hn n) (hb n) mass2 quartic vacuum s
      (state ε a hε ha (h n) (hn n) (hb n) (h1 n) mass2 quartic vacuum s hm hq hv.le)
  · exact hn'

theorem exists_small_parameter_strict_decrease (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 < vacuum)
    (η : ℝ) (hη : 0 < η) :
    ∃ (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3),
      0 < hbar ∧ hbar < η ∧ |hbar| ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧
        StrictAntiOn (quantumExpectation ε a hε ha hbar hh hb mass2 quartic vacuum s) (Icc s (s+δ)) := by
  let h := parameter ε
  have hn (n : ℕ) : h n ≠ 0 := (parameter_positive ε hε n).ne'
  have hb (n : ℕ) : |h n| ≤ 2*Real.pi*ε/3 := (parameter_bound ε hε n).trans (min_le_right _ _)
  have h1 (n : ℕ) : |h n| ≤ 1 := (parameter_bound ε hε n).trans (min_le_left _ _)
  have he := eventually_quantum_strict_decrease ε a hε ha mass2 quartic vacuum s hm hq hv
    h hn hb h1 (parameter_tendsto ε)
  have hsmall : ∀ᶠ n in atTop, h n < η := (parameter_tendsto ε).eventually (gt_mem_nhds hη)
  obtain ⟨n,hdec,hs⟩ := (he.and hsmall).exists
  exact ⟨h n,hn n,hb n,parameter_positive ε hε n,hs,h1 n,hdec⟩

#print axioms drift_clock_negative
#print axioms dampedClockFunction_ne_zero
#print axioms driftMass_negative
#print axioms initialClassicalDrift_negative
#print axioms local_strictAnti_of_continuous_rate
#print axioms eventually_quantum_strict_decrease
#print axioms exists_small_parameter_strict_decrease

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialStrictDecay
