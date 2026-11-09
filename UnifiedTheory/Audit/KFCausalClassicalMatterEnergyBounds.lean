/- Energy control of the nonnegative full matter candidate. The weighted
interaction retains the positive vacuum floor, so charged coordinates and
the upper clock-momentum tail remain controlled by the energy. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
import UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_nonnegative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy (staticKinetic growingKinetic staticKinetic_nonnegative growingKinetic_nonnegative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize kinetic_split)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

theorem clock_energy_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    clock ε (q (.inr 0) x.2) ≤ 2*fullHamiltonian ε m g κ x := by
  rw [hamiltonian_split]
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have hk := div_nonneg (staticKinetic_nonnegative x.2) hc.le
  have hg := growingEnergy_nonnegative ε m g κ hε hm hg hκ x
  linarith

theorem clock_times_energy (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    clock ε (q (.inr 0) x.2)*fullHamiltonian ε m g κ x =
      (clock ε (q (.inr 0) x.2))^2/2+kineticMean x.1 x.2+
      amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
        weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2 := by
  have hc := (clock_positive ε (q (.inr 0) x.2) hε).ne'
  unfold fullHamiltonian hamiltonian
  field_simp
  ring

theorem kinetic_energy_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    kineticMean x.1 x.2 ≤ 2*(fullHamiltonian ε m g κ x)^2 := by
  have ha : 0 ≤ amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2) := (Real.exp_pos _).le
  have hf : 0 ≤ weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2 :=
    le_trans hκ (weightedMean_lower m g κ _ hm hg hκ _)
  have he := clock_times_energy ε m g κ hε x
  have hc := clock_energy_bound ε m g κ hε hm hg hκ x
  have hH := (energy_bounds ε m g κ hε hm hg hκ x).1
  nlinarith [sq_nonneg (clock ε (q (.inr 0) x.2)), mul_nonneg ha hf,
    mul_le_mul_of_nonneg_right hc hH.le]

theorem interaction_energy_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)*
      weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2 ≤
        clock ε (q (.inr 0) x.2)*fullHamiltonian ε m g κ x := by
  rw [clock_times_energy ε m g κ hε]
  linarith [sq_nonneg (clock ε (q (.inr 0) x.2)), kineticMean_nonnegative x.1 x.2]

theorem phaseSize_energy_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    phaseSize x.2 ≤ 4*(1+Real.exp (-2*x.1))*(fullHamiltonian ε m g κ x)^2 := by
  have hK := kinetic_energy_bound ε m g κ hε hm hg hκ x
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

theorem logClock_energy_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    q (.inr 0) x.2 ≤ 2*fullHamiltonian ε m g κ x := by
  have h := Real.add_one_le_exp (q (.inr 0) x.2)
  have hc := clock_energy_bound ε m g κ hε hm hg hκ x
  unfold clock at hc
  linarith

theorem clockRate_energy_bound (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤ fullHamiltonian ε m g κ x/ε := by
  have hc := clock_positive ε (q (.inr 0) x.2) hε.le
  have hC := (clock_above_floor ε (q (.inr 0) x.2)).le
  have hH := (energy_bounds ε m g κ hε.le hm hg hκ x).1
  have hv := interaction_energy_bound ε m g κ hε.le x
  calc
    _ ≤ (clock ε (q (.inr 0) x.2)*fullHamiltonian ε m g κ x)/(clock ε (q (.inr 0) x.2))^2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = fullHamiltonian ε m g κ x/clock ε (q (.inr 0) x.2) := by field_simp
    _ ≤ fullHamiltonian ε m g κ x/ε := div_le_div_of_nonneg_left hH.le hε hC

theorem clockMomentum_energy_upper (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (x : TimePhase) :
    p (.inr 0) x.2 ≤ (clock ε (q (.inr 0) x.2))^2*fullHamiltonian ε m g κ x/
      (κ*Real.exp (2*x.1)) := by
  let C := clock ε (q (.inr 0) x.2)
  let r := p (.inr 0) x.2
  have hc : 0 < C := clock_positive ε _ hε
  have ha : 0 ≤ amplitude ε x.1 (q (.inr 0) x.2) r := (Real.exp_pos _).le
  have hv := (mul_le_mul_of_nonneg_left (weightedMean_lower m g κ C hm hg hκ.le x.2) ha).trans
    (interaction_energy_bound ε m g κ hε x)
  have hex : Real.exp (r/C) ≤ C*fullHamiltonian ε m g κ x/(κ*Real.exp (2*x.1)) := by
    apply (le_div_iff₀ (mul_pos hκ (Real.exp_pos _))).2
    simpa only [amplitude,Real.exp_add,mul_assoc,mul_comm,mul_left_comm] using hv
  have hb : r/C ≤ Real.exp (r/C) := by linarith [Real.add_one_le_exp (r/C)]
  calc
    r = C*(r/C) := (mul_div_cancel₀ _ hc.ne').symm
    _ ≤ C*Real.exp (r/C) := mul_le_mul_of_nonneg_left hb hc.le
    _ ≤ C*(C*fullHamiltonian ε m g κ x/(κ*Real.exp (2*x.1))) := mul_le_mul_of_nonneg_left hex hc.le
    _ = _ := by ring

#print axioms clock_energy_bound
#print axioms clock_times_energy
#print axioms kinetic_energy_bound
#print axioms interaction_energy_bound
#print axioms phaseSize_energy_bound
#print axioms logClock_energy_bound
#print axioms clockRate_energy_bound
#print axioms clockMomentum_energy_upper

end
end UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
