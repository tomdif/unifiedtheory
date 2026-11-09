/- An upper bound on clock-momentum velocity complements the lower bound.
It controls the lower momentum tail when the trajectory is followed backward. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

theorem tiltedShear_upper (C : ℝ) (hC : 0 < C) (z : Phase) :
    tiltedShear C z ≤ (2*phaseSize z/C)*exponentialMean C z := by
  have hc : Continuous (fun θ => shear (rotate θ z)/C) := (shear_continuous z).div_const C
  have hm := mean_mono (fun θ => shear (rotate θ z)/C*Real.exp (shear (rotate θ z)/C))
    (fun θ => (2*phaseSize z/C)*Real.exp (shear (rotate θ z)/C))
    (hc.mul (Real.continuous_exp.comp hc)) (continuous_const.mul (Real.continuous_exp.comp hc))
    (fun θ => by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply div_le_div_of_nonneg_right _ hC.le
      simpa only [phaseSize_rotate] using
        (le_abs_self (shear (rotate θ z))).trans (shear_abs_bound (rotate θ z)))
  simpa only [tiltedShear,exponentialMean,mul_comm (2*phaseSize z/C),mean_mul_const] using hm

theorem clockMomentum_ratio_upper (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 < κ) (x : TimePhase) :
    p (.inr 0) x.2/clock ε (q (.inr 0) x.2) ≤
      clock ε (q (.inr 0) x.2)*fullHamiltonian ε κ x/(κ*Real.exp (2*x.1)) := by
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have h := div_le_div_of_nonneg_right (clockMomentum_energy_upper ε κ hε hκ x) hc.le
  convert h using 1
  field_simp

theorem momentumRate_upper (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x : TimePhase) :
    momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤
      fullHamiltonian ε κ x*(2+clock ε (q (.inr 0) x.2)*fullHamiltonian ε κ x/
        (κ*Real.exp (2*x.1))+2*phaseSize x.2/ε) := by
  let C := clock ε (q (.inr 0) x.2)
  let H := fullHamiltonian ε κ x
  let F := exponentialMean C x.2
  let A := amplitude ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)
  let U := C*H/(κ*Real.exp (2*x.1))
  let V := 2*phaseSize x.2/ε
  have hc : 0 < C := clock_positive ε _ hε.le
  have hh : 0 < H := (energy_bounds ε κ hε.le hκ.le x).1
  have hf : 0 ≤ F := le_trans (by norm_num) (exponentialMean_ge_one C x.2)
  have ha : 0 ≤ A := amplitude_nonnegative ε κ _ _ _ hκ.le
  have hu : 0 ≤ U := by dsimp [U]; positivity
  have hv : 0 ≤ V := div_nonneg (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2)) hε.le
  have hb : p (.inr 0) x.2/C ≤ U := clockMomentum_ratio_upper ε κ hε.le hκ x
  have ht : tiltedShear C x.2 ≤ V*F := by
    apply (tiltedShear_upper C hc x.2).trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2)) hε (clock_above_floor ε _).le) hf
  have hn : (1+p (.inr 0) x.2/C)*F+tiltedShear C x.2 ≤ (1+U+V)*F := by
    nlinarith only [mul_le_mul_of_nonneg_right hb hf,ht]
  have hk : kineticMean x.1 x.2 ≤ C*H := by
    have he := clock_times_energy ε κ hε.le x
    change C*H = C^2/2+kineticMean x.1 x.2+A*F at he
    nlinarith [sq_nonneg C,mul_nonneg ha hf]
  have haf : A*F ≤ C*H := vacuum_energy_bound ε κ hε.le x
  have hn' : kineticMean x.1 x.2+A*((1+p (.inr 0) x.2/C)*F+tiltedShear C x.2) ≤
      C*H*(2+U+V) := by
    have h1 := mul_le_mul_of_nonneg_left hn ha
    have h2 := mul_le_mul_of_nonneg_right haf (by linarith : 0 ≤ 1+U+V)
    nlinarith only [h1,h2,hk]
  have he : Real.exp (q (.inr 0) x.2) ≤ C := by dsimp [C,clock]; linarith
  have hcoef : Real.exp (q (.inr 0) x.2)/C^2 ≤ 1/C := by
    calc
      _ ≤ C/C^2 := div_le_div_of_nonneg_right he (sq_nonneg C)
      _ = _ := by field_simp
  have hscaled := mul_le_mul_of_nonneg_left hn'
    (div_nonneg (Real.exp_pos (q (.inr 0) x.2)).le (sq_nonneg C))
  have hupper := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ C*H*(2+U+V))
  have hid : 1/C*(C*H*(2+U+V)) = H*(2+U+V) := by field_simp
  rw [hid] at hupper
  change -Real.exp (q (.inr 0) x.2)/2+Real.exp (q (.inr 0) x.2)/C^2*
    (kineticMean x.1 x.2+A*((1+p (.inr 0) x.2/C)*F+tiltedShear C x.2)) ≤ H*(2+U+V)
  linarith only [hscaled,hupper,Real.exp_pos (q (.inr 0) x.2)]

def upperMomentumEnvelope (ε κ t E : ℝ) : ℝ :=
  E*(2+2*E^2/(κ*Real.exp (2*t))+8*(1+Real.exp (-2*t))*E^2/ε)

theorem momentumRate_energy_upper (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x : TimePhase) :
    momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤
      upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε κ x) := by
  apply (momentumRate_upper ε κ hε hκ x).trans
  have hh := (energy_bounds ε κ hε.le hκ.le x).1
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (clock_energy_bound ε κ hε.le hκ.le x) hh.le)
    (mul_pos hκ (Real.exp_pos (2*x.1))).le
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (phaseSize_energy_bound ε κ hε.le hκ.le x) (by norm_num : (0:ℝ) ≤ 2)) hε.le
  unfold upperMomentumEnvelope
  apply mul_le_mul_of_nonneg_left _ hh.le
  convert add_le_add (add_le_add_left h1 2) h2 using 1 <;> ring

#print axioms tiltedShear_upper
#print axioms clockMomentum_ratio_upper
#print axioms momentumRate_upper
#print axioms momentumRate_energy_upper

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds
