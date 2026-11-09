/- Fast classical energy growth is compatible with clock-defect recovery.
This diagnoses a proposed sufficient quantum estimate; it is not a quantum
trajectory or a semiclassical-limit theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumDefectDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumEnergyGrowth
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
open UnifiedTheory.Audit.KFCausalClockFloorVacuumDynamics (amplitude_nonnegative)

variable (ε κ : ℝ) (hε : 0 < ε) (s L : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
  (hL : ∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t)

include hε hs hL in
theorem discounted_amplitude_monotone (hκ : 0 ≤ κ) :
    Monotone (fun t => Real.exp (-(3/2:ℝ)*t)*amplitude ε κ t (s t) (L t)) := by
  have hd (t : ℝ) : HasDerivAt
      (fun u => Real.exp (-(3/2:ℝ)*u)*amplitude ε κ u (s u) (L u))
      (Real.exp (-(3/2:ℝ)*t)*((1-response ε (s t))/2)*amplitude ε κ t (s t) (L t)) t := by
    convert ((((hasDerivAt_id t).const_mul (-(3/2:ℝ))).exp).mul
      (amplitude_derivative ε κ hε s L t (hs t) (hL t))) using 1
    simp only [id_eq]
    ring
  apply monotone_of_hasDerivAt_nonneg hd
  intro t
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (div_nonneg (sub_nonneg.mpr (response_bounds ε (s t) hε).2.le) (by norm_num)))
    (amplitude_nonnegative ε κ t (s t) (L t) hε hκ)

include hε hs hL in
theorem amplitude_exponential_lower (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    amplitude ε κ 0 (s 0) (L 0)*Real.exp ((3/2:ℝ)*t) ≤ amplitude ε κ t (s t) (L t) := by
  have hb := discounted_amplitude_monotone ε κ hε s L hs hL hκ ht
  simp only [mul_zero,Real.exp_zero,one_mul] at hb
  have he : Real.exp (-(3/2:ℝ)*t)*Real.exp ((3/2:ℝ)*t) = 1 := by
    rw [← Real.exp_add,show -(3/2:ℝ)*t+(3/2:ℝ)*t=0 by ring,Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((3/2:ℝ)*t)).le
  calc
    _ ≤ (Real.exp (-(3/2:ℝ)*t)*amplitude ε κ t (s t) (L t))*Real.exp ((3/2:ℝ)*t) := hm
    _ = amplitude ε κ t (s t) (L t)*(Real.exp (-(3/2:ℝ)*t)*Real.exp ((3/2:ℝ)*t)) := by ring
    _ = amplitude ε κ t (s t) (L t) := by rw [he,mul_one]

include hε hs hL in
theorem discounted_energy_lower (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    amplitude ε κ 0 (s 0) (L 0)*Real.exp (t/2) ≤
      Real.exp (-t)*energy ε κ t (s t) (L t) := by
  have he : amplitude ε κ t (s t) (L t) ≤ energy ε κ t (s t) (L t) := by
    unfold energy
    linarith only [clock_positive ε (s t) hε.le]
  have hm := mul_le_mul_of_nonneg_left
    ((amplitude_exponential_lower ε κ hε s L hs hL hκ t ht).trans he) (Real.exp_pos (-t)).le
  calc
    _ = Real.exp (-t)*(amplitude ε κ 0 (s 0) (L 0)*Real.exp ((3/2:ℝ)*t)) := by
      rw [← mul_assoc,mul_comm (Real.exp (-t)),mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hm

include hε hs hL in
theorem discounted_energy_tendsto_atTop (hκ : 0 < κ) :
    Tendsto (fun t => Real.exp (-t)*energy ε κ t (s t) (L t)) atTop atTop := by
  have hA : 0 < amplitude ε κ 0 (s 0) (L 0) := by
    unfold amplitude
    exact div_pos (mul_pos hκ (Real.exp_pos _)) (clock_positive ε (s 0) hε.le)
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0:ℝ)).mono (fun t ht => discounted_energy_lower ε κ hε s L hs hL hκ.le t ht))
  exact (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))).const_mul_atTop hA

#print axioms discounted_amplitude_monotone
#print axioms amplitude_exponential_lower
#print axioms discounted_energy_lower
#print axioms discounted_energy_tendsto_atTop
end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumEnergyGrowth
