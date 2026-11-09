/- Uniform control of the orbit exponential by the charged energy variables.
Together with the energy work estimate this controls the lower clock-momentum
drift on finite time windows, a necessary continuation estimate. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)

theorem phaseSize_nonnegative (z : Phase) : 0 ≤ phaseSize z := by
  exact mul_nonneg (by norm_num) (add_nonneg (staticKinetic_nonnegative z) (growingKinetic_nonnegative z))

theorem phaseSize_rotate (θ : ℝ) (z : Phase) : phaseSize (rotate θ z) = phaseSize z := by
  calc
    _ = (Real.sin θ^2+Real.cos θ^2)*(phaseSize z-(p (.inr 3) z)^2)+(p (.inr 3) z)^2 := by
      simp [phaseSize, staticKinetic, growingKinetic, q_apply, p_apply, rotate,
        -Real.sin_sq_add_cos_sq]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem shear_abs_bound (z : Phase) : |shear z| ≤ 2*phaseSize z := by
  have hp (a b : ℝ) : 2*|a*b| ≤ a^2+b^2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a|-|b|), sq_abs a, sq_abs b]
  have hs : |scale| ≤ 1 := by nlinarith [scale_square, sq_abs scale, abs_nonneg scale]
  have hn : |2*scale*z.1 (.inr 2)*z.2 (.inr 3)| ≤ z.1 (.inr 2)^2+z.2 (.inr 3)^2 := by
    calc
      _ = 2*|scale| *|z.1 (.inr 2)*z.2 (.inr 3)| := by rw [abs_mul,abs_mul,abs_mul]; norm_num; ring
      _ ≤ 2*|z.1 (.inr 2)*z.2 (.inr 3)| := by nlinarith [abs_nonneg (z.1 (.inr 2)*z.2 (.inr 3))]
      _ ≤ _ := hp _ _
  have hd := abs_add_le (diagonalPairing z/2) (2*scale*z.1 (.inr 2)*z.2 (.inr 3))
  rw [← shear_eq] at hd
  have h1 := hp (z.1 (.inl 0)) (z.2 (.inl 0))
  have h2 := hp (z.1 (.inr 1)) (z.2 (.inr 1))
  have h3 := hp (z.1 (.inl 1)) (z.2 (.inl 1))
  have h4 := hp (z.1 (.inr 2)) (z.2 (.inr 2))
  have ha := abs_add_le (z.1 (.inl 0)*z.2 (.inl 0)) (z.1 (.inr 1)*z.2 (.inr 1))
  have hb := abs_add_le (z.1 (.inl 0)*z.2 (.inl 0)+z.1 (.inr 1)*z.2 (.inr 1))
    (z.1 (.inl 1)*z.2 (.inl 1))
  have hc := abs_add_le (z.1 (.inl 0)*z.2 (.inl 0)+z.1 (.inr 1)*z.2 (.inr 1)+
    z.1 (.inl 1)*z.2 (.inl 1)) (z.1 (.inr 2)*z.2 (.inr 2))
  norm_num only [abs_div] at hd
  unfold diagonalPairing at hd
  unfold phaseSize staticKinetic growingKinetic
  simp only [p_apply,q_apply]
  nlinarith [sq_nonneg (z.1 (.inl 0)),sq_nonneg (z.1 (.inl 1)),
    sq_nonneg (z.1 (.inr 1)),sq_nonneg (z.1 (.inr 2)),
    sq_nonneg (z.2 (.inl 0)),sq_nonneg (z.2 (.inl 1)),
    sq_nonneg (z.2 (.inr 1)),sq_nonneg (z.2 (.inr 2)),sq_nonneg (z.2 (.inr 3))]

theorem exponentialMean_upper (C : ℝ) (hC : 0 < C) (z : Phase) :
    exponentialMean C z ≤ Real.exp (2*phaseSize z/C) := by
  have hm := mean_mono (fun θ => Real.exp (shear (rotate θ z)/C))
    (fun _ => Real.exp (2*phaseSize z/C))
    (Real.continuous_exp.comp ((shear_continuous z).div_const C)) continuous_const
    (fun θ => by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hC.le
      simpa only [phaseSize_rotate] using (le_abs_self (shear (rotate θ z))).trans (shear_abs_bound (rotate θ z)))
  simpa only [mean_const] using hm

theorem exponentialMean_energy_upper (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    exponentialMean (clock ε (q (.inr 0) x.2)) x.2 ≤
      Real.exp (8*(1+Real.exp (-2*x.1))*(fullHamiltonian ε κ x)^2/ε) := by
  apply (exponentialMean_upper _ (clock_positive ε _ hε.le) x.2).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 2*phaseSize x.2/ε := div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2)) hε (clock_above_floor ε _).le
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hε.le
      linarith [phaseSize_energy_bound ε κ hε.le hκ x]

def momentumEnvelope (ε κ t E : ℝ) : ℝ :=
  E+κ*Real.exp (2*t)*Real.exp (8*(1+Real.exp (-2*t))*E^2/ε)/ε

theorem momentumRate_energy_lower (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    -momentumEnvelope ε κ x.1 (fullHamiltonian ε κ x) ≤
      momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  apply le_trans _ (clockMomentum_rate_lower ε κ hε hκ x)
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exponentialMean_energy_upper ε κ hε hκ x)
      (mul_nonneg hκ (Real.exp_pos (2*x.1)).le)) hε.le
  unfold momentumEnvelope
  linarith

#print axioms phaseSize_nonnegative
#print axioms phaseSize_rotate
#print axioms shear_abs_bound
#print axioms exponentialMean_upper
#print axioms exponentialMean_energy_upper
#print axioms momentumRate_energy_lower

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds
