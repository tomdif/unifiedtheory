/- Pointwise energy control of the clock, every charged phase coordinate,
neutral momentum, and the upper clock-momentum tail in the full averaged
vacuum candidate. The remaining lower tails need dynamical estimates. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

def phaseSize (z : Phase) : ℝ := 2*(staticKinetic z+growingKinetic z)

theorem kinetic_split (t : ℝ) (z : Phase) :
    kineticMean t z = staticKinetic z+Real.exp (2*t)*growingKinetic z := by
  rw [kineticMean_eq]
  unfold staticKinetic growingKinetic
  simp only [p_apply,q_apply]
  ring

theorem amplitude_nonnegative (ε κ t s r : ℝ) (hκ : 0 ≤ κ) : 0 ≤ amplitude ε κ t s r :=
  mul_nonneg hκ (Real.exp_pos _).le

theorem clock_energy_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    clock ε (q (.inr 0) x.2) ≤ 2*fullHamiltonian ε κ x := by
  rw [hamiltonian_split]
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have hk := div_nonneg (staticKinetic_nonnegative x.2) hc.le
  have hg := growingEnergy_nonnegative ε κ hε hκ x
  linarith

theorem clock_times_energy (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    clock ε (q (.inr 0) x.2)*fullHamiltonian ε κ x =
      (clock ε (q (.inr 0) x.2))^2/2+kineticMean x.1 x.2+
      amplitude ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
        exponentialMean (clock ε (q (.inr 0) x.2)) x.2 := by
  have hc := (clock_positive ε (q (.inr 0) x.2) hε).ne'
  unfold fullHamiltonian hamiltonian
  field_simp
  ring

theorem kinetic_energy_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    kineticMean x.1 x.2 ≤ 2*(fullHamiltonian ε κ x)^2 := by
  have ha := amplitude_nonnegative ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2) hκ
  have hf : 0 ≤ exponentialMean (clock ε (q (.inr 0) x.2)) x.2 :=
    le_trans (by norm_num) (exponentialMean_ge_one _ _)
  have he := clock_times_energy ε κ hε x
  have hc := clock_energy_bound ε κ hε hκ x
  have hH := (energy_bounds ε κ hε hκ x).1
  nlinarith [sq_nonneg (clock ε (q (.inr 0) x.2)), mul_nonneg ha hf,
    mul_le_mul_of_nonneg_right hc hH.le]

theorem vacuum_energy_bound (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    amplitude ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
      exponentialMean (clock ε (q (.inr 0) x.2)) x.2 ≤
        clock ε (q (.inr 0) x.2)*fullHamiltonian ε κ x := by
  rw [clock_times_energy ε κ hε]
  linarith [sq_nonneg (clock ε (q (.inr 0) x.2)), kineticMean_nonnegative x.1 x.2]

theorem phaseSize_energy_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    phaseSize x.2 ≤ 4*(1+Real.exp (-2*x.1))*(fullHamiltonian ε κ x)^2 := by
  have hK := kinetic_energy_bound ε κ hε hκ x
  have h0 := staticKinetic_nonnegative x.2
  have h1 := growingKinetic_nonnegative x.2
  have he : Real.exp (-2*x.1)*Real.exp (2*x.1) = 1 := by
    rw [← Real.exp_add, show -2*x.1+2*x.1 = 0 by ring, Real.exp_zero]
  have hG : growingKinetic x.2 ≤ Real.exp (-2*x.1)*kineticMean x.1 x.2 := by
    rw [kinetic_split, mul_add, ← mul_assoc, he, one_mul]
    linarith [mul_nonneg (Real.exp_pos (-2*x.1)).le h0]
  have hS : staticKinetic x.2 ≤ kineticMean x.1 x.2 := by
    rw [kinetic_split]
    exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le h1)
  unfold phaseSize
  nlinarith [mul_le_mul_of_nonneg_left hK (Real.exp_pos (-2*x.1)).le]

theorem logClock_energy_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    q (.inr 0) x.2 ≤ 2*fullHamiltonian ε κ x := by
  have h := Real.add_one_le_exp (q (.inr 0) x.2)
  have hc := clock_energy_bound ε κ hε hκ x
  unfold clock at hc
  linarith

theorem clockRate_energy_bound (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    clockRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤ fullHamiltonian ε κ x/ε := by
  have hc := clock_positive ε (q (.inr 0) x.2) hε.le
  have hC := (clock_above_floor ε (q (.inr 0) x.2)).le
  have hH := (energy_bounds ε κ hε.le hκ x).1
  have hv := vacuum_energy_bound ε κ hε.le x
  calc
    _ ≤ (clock ε (q (.inr 0) x.2)*fullHamiltonian ε κ x)/(clock ε (q (.inr 0) x.2))^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = fullHamiltonian ε κ x/clock ε (q (.inr 0) x.2) := by field_simp
    _ ≤ fullHamiltonian ε κ x/ε := div_le_div_of_nonneg_left hH.le hε hC

theorem clockMomentum_energy_upper (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 < κ) (x : TimePhase) :
    p (.inr 0) x.2 ≤ (clock ε (q (.inr 0) x.2))^2*fullHamiltonian ε κ x/
      (κ*Real.exp (2*x.1)) := by
  let C := clock ε (q (.inr 0) x.2)
  let r := p (.inr 0) x.2
  have hc : 0 < C := clock_positive ε _ hε
  have ha := amplitude_nonnegative ε κ x.1 (q (.inr 0) x.2) r hκ.le
  have hv := (le_mul_of_one_le_right ha (exponentialMean_ge_one C x.2)).trans
    (vacuum_energy_bound ε κ hε x)
  have hex : Real.exp (r/C) ≤ C*fullHamiltonian ε κ x/(κ*Real.exp (2*x.1)) := by
    apply (le_div_iff₀ (mul_pos hκ (Real.exp_pos _))).2
    simpa only [amplitude, Real.exp_add, mul_assoc, mul_comm, mul_left_comm] using hv
  have hb : r/C ≤ Real.exp (r/C) := by linarith [Real.add_one_le_exp (r/C)]
  calc
    r = C*(r/C) := (mul_div_cancel₀ _ hc.ne').symm
    _ ≤ C*Real.exp (r/C) := mul_le_mul_of_nonneg_left hb hc.le
    _ ≤ C*(C*fullHamiltonian ε κ x/(κ*Real.exp (2*x.1))) := mul_le_mul_of_nonneg_left hex hc.le
    _ = _ := by ring

theorem exponential_linear_lower (u : ℝ) : -1 ≤ (1+u)*Real.exp u := by
  have h := Real.mul_exp_neg_le_exp_neg_one (-u)
  rw [neg_neg] at h
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  nlinarith [Real.exp_pos u]

theorem clockMomentum_rate_lower (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    -fullHamiltonian ε κ x-κ*Real.exp (2*x.1)*
      exponentialMean (clock ε (q (.inr 0) x.2)) x.2/ε ≤
        momentumRate ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  let C := clock ε (q (.inr 0) x.2)
  let F := exponentialMean C x.2
  let B := p (.inr 0) x.2/C
  let Q := κ*Real.exp (2*x.1)*F
  have hc : 0 < C := clock_positive ε _ hε.le
  have hF : 0 ≤ F := le_trans (by norm_num) (exponentialMean_ge_one C x.2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have ha := amplitude_nonnegative ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2) hκ
  have hT := mul_nonneg ha (tiltedShear_nonnegative C x.2)
  have hK := kineticMean_nonnegative x.1 x.2
  have hlinear := mul_le_mul_of_nonneg_left (exponential_linear_lower B) hQ
  have hN : -Q ≤ kineticMean x.1 x.2+
      amplitude ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
        ((1+B)*F+tiltedShear C x.2) := by
    dsimp [Q,B,F,C] at hlinear ⊢
    simp only [amplitude, Real.exp_add] at hT ⊢
    nlinarith only [hlinear,hT,hK]
  have hCexp : Real.exp (q (.inr 0) x.2) ≤ C := by dsimp [C,clock]; linarith
  have hcoef : Real.exp (q (.inr 0) x.2)/C^2 ≤ 1/ε := by
    calc
      _ ≤ C/C^2 := div_le_div_of_nonneg_right hCexp (sq_nonneg _)
      _ = 1/C := by field_simp
      _ ≤ 1/ε := div_le_div_of_nonneg_left zero_le_one hε (clock_above_floor ε _).le
  have hclock : Real.exp (q (.inr 0) x.2)/2 ≤ fullHamiltonian ε κ x := by
    linarith [clock_energy_bound ε κ hε.le hκ x]
  have hscaled := mul_le_mul_of_nonneg_left hN (div_nonneg (Real.exp_pos (q (.inr 0) x.2)).le (sq_nonneg C))
  have hQscaled : Real.exp (q (.inr 0) x.2)/C^2*Q ≤ Q/ε := by
    convert mul_le_mul_of_nonneg_right hcoef hQ using 1
    ring
  change -fullHamiltonian ε κ x-Q/ε ≤ _
  unfold momentumRate
  change _ ≤ -Real.exp (q (.inr 0) x.2)/2+Real.exp (q (.inr 0) x.2)/C^2*
    (kineticMean x.1 x.2+amplitude ε κ x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
      ((1+B)*F+tiltedShear C x.2))
  rw [mul_neg] at hscaled
  linarith only [hclock,hscaled,hQscaled]

#print axioms kinetic_split
#print axioms amplitude_nonnegative
#print axioms clock_energy_bound
#print axioms clock_times_energy
#print axioms kinetic_energy_bound
#print axioms vacuum_energy_bound
#print axioms phaseSize_energy_bound
#print axioms logClock_energy_bound
#print axioms clockRate_energy_bound
#print axioms clockMomentum_energy_upper
#print axioms exponential_linear_lower
#print axioms clockMomentum_rate_lower

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
