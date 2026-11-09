/- Energy growth and the clock-defect equation along actual global vacuum
classical solutions. These estimates concern the classical flow only;
quantum-to-classical propagation is a separate theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical (defect_clock_derivative)

theorem amplitude_nonnegative (ε κ t s L : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) :
    0 ≤ amplitude ε κ t s L :=
  div_nonneg (mul_nonneg hκ (Real.exp_pos _).le) (clock_positive ε s hε.le).le

theorem energy_positive (ε κ t s L : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) :
    0 < energy ε κ t s L :=
  add_pos_of_pos_of_nonneg (div_pos (clock_positive ε s hε.le) (by norm_num))
    (amplitude_nonnegative ε κ t s L hε hκ)

variable (ε κ : ℝ) (hε : 0 < ε) (s L : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
  (hL : ∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t)

include hε hs hL in
theorem weighted_energy_derivative (t : ℝ) :
    HasDerivAt (fun u => Real.exp (-2*u)*energy ε κ u (s u) (L u))
      (-Real.exp (-2*t)*clock ε (s t)) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2)).exp).mul
    (energy_derivative ε κ hε s L t (hs t) (hL t))
  convert hd using 1
  dsimp only [id_eq]
  unfold energy
  ring

include hε hs hL in
theorem weighted_energy_antitone :
    Antitone (fun t => Real.exp (-2*t)*energy ε κ t (s t) (L t)) := by
  apply antitone_of_hasDerivAt_nonpos (weighted_energy_derivative ε κ hε s L hs hL)
  intro t
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) (clock_positive ε (s t) hε.le).le

include hε hs hL in
theorem energy_monotone (hκ : 0 ≤ κ) : Monotone (fun t => energy ε κ t (s t) (L t)) := by
  apply monotone_of_hasDerivAt_nonneg (fun t => energy_derivative ε κ hε s L t (hs t) (hL t))
  intro t
  exact mul_nonneg (by norm_num) (amplitude_nonnegative ε κ t (s t) (L t) hε hκ)

include hε hs hL in
theorem energy_forward_bound (u t : ℝ) (hut : u ≤ t) :
    energy ε κ t (s t) (L t) ≤ Real.exp (2*(t-u))*energy ε κ u (s u) (L u) := by
  have hb := mul_le_mul_of_nonneg_left ((weighted_energy_antitone ε κ hε s L hs hL) hut) (Real.exp_pos (2*t)).le
  have hcancel : Real.exp (2*t)*Real.exp (-2*t) = 1 := by
    rw [← Real.exp_add,show 2*t+-2*t = 0 by ring,Real.exp_zero]
  have htimes : Real.exp (2*t)*Real.exp (-2*u) = Real.exp (2*(t-u)) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [← mul_assoc,hcancel,htimes,one_mul] using hb

include hε hs in
theorem clock_monotone (hκ : 0 ≤ κ) : Monotone s := by
  apply monotone_of_hasDerivAt_nonneg hs
  intro t
  exact div_nonneg (amplitude_nonnegative ε κ t (s t) (L t) hε hκ) (clock_positive ε (s t) hε.le).le

include hε hs in
theorem defect_derivative (t : ℝ) :
    HasDerivAt (fun u => defect ε (s u))
      (drift ε (defect ε (s t))*amplitude ε κ t (s t) (L t)) t := by
  have hd := (defect_clock_derivative ε (s t) hε).comp t (hs t)
  convert hd using 1
  have hc := (clock_positive ε (s t) hε.le).ne'
  unfold drift defect
  field_simp
  unfold clock
  ring

include hε hs in
theorem defect_strictAnti (hκ : 0 < κ) : StrictAnti (fun t => defect ε (s t)) := by
  apply strictAnti_of_hasDerivAt_neg (defect_derivative ε κ hε s L hs)
  intro t
  have hD := defect_positive ε (s t) hε
  have hresponse := (response_bounds ε (s t) hε).1
  have hadd := response_add_defect ε (s t) hε.le
  have hdrift : drift ε (defect ε (s t)) < 0 := by
    unfold drift
    apply div_neg_of_neg_of_pos _ hε
    exact neg_neg_of_pos (mul_pos (sq_pos_of_pos hD) (by linarith only [hresponse,hadd]))
  have hA : 0 < amplitude ε κ t (s t) (L t) := by
    unfold amplitude
    exact div_pos (mul_pos hκ (Real.exp_pos _)) (clock_positive ε (s t) hε.le)
  exact mul_neg_of_neg_of_pos hdrift hA

#print axioms amplitude_nonnegative
#print axioms energy_positive
#print axioms weighted_energy_derivative
#print axioms weighted_energy_antitone
#print axioms energy_monotone
#print axioms energy_forward_bound
#print axioms clock_monotone
#print axioms defect_derivative
#print axioms defect_strictAnti

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumDynamics
