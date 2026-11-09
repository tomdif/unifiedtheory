/- Two-sided clock-momentum velocity control for the matter candidate.
The lower bound explicitly retains the possibly negative weighted tilt. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
import UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
import UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterMomentumBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_nonnegative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize exponential_linear_lower)
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds (phaseSize_nonnegative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumMomentumBounds (upperMomentumEnvelope)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

theorem clockMomentum_ratio_upper (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ) (x : TimePhase) :
    p (.inr 0) x.2/clock ε (q (.inr 0) x.2) ≤
      clock ε (q (.inr 0) x.2)*fullHamiltonian ε m g κ x/(κ*Real.exp (2*x.1)) := by
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have h := div_le_div_of_nonneg_right (clockMomentum_energy_upper ε m g κ hε hm hg hκ x) hc.le
  convert h using 1
  field_simp

theorem momentumRate_upper (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ) (x : TimePhase) :
    momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤
      fullHamiltonian ε m g κ x*(2+clock ε (q (.inr 0) x.2)*fullHamiltonian ε m g κ x/
        (κ*Real.exp (2*x.1))+2*phaseSize x.2/ε) := by
  let C := clock ε (q (.inr 0) x.2)
  let H := fullHamiltonian ε m g κ x
  let F := weightedMean m g κ C x.2
  let A := amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)
  let U := C*H/(κ*Real.exp (2*x.1))
  let V := 2*phaseSize x.2/ε
  have hc : 0 < C := clock_positive ε _ hε.le
  have hh : 0 < H := (energy_bounds ε m g κ hε.le hm hg hκ.le x).1
  have hf : 0 ≤ F := hκ.le.trans (weightedMean_lower m g κ C hm hg hκ.le x.2)
  have ha : 0 ≤ A := (Real.exp_pos _).le
  have hu : 0 ≤ U := by dsimp [U]; positivity
  have hv : 0 ≤ V := div_nonneg (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2)) hε.le
  have hb : p (.inr 0) x.2/C ≤ U := clockMomentum_ratio_upper ε m g κ hε.le hm hg hκ x
  have ht : weightedTilt m g κ C x.2 ≤ V*F := by
    have ht := (le_abs_self (weightedTilt m g κ C x.2)).trans
      (weightedTilt_abs_bound m g κ C hm hg hκ.le hc x.2)
    rw [mul_comm (weightedMean m g κ C x.2)] at ht
    apply ht.trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2)) hε (clock_above_floor ε _).le) hf
  have hn : (1+p (.inr 0) x.2/C)*F+weightedTilt m g κ C x.2 ≤ (1+U+V)*F := by
    nlinarith only [mul_le_mul_of_nonneg_right hb hf,ht]
  have hk : kineticMean x.1 x.2 ≤ C*H := by
    have he := clock_times_energy ε m g κ hε.le x
    change C*H = C^2/2+kineticMean x.1 x.2+A*F at he
    nlinarith [sq_nonneg C,mul_nonneg ha hf]
  have haf : A*F ≤ C*H := interaction_energy_bound ε m g κ hε.le x
  have hn' : kineticMean x.1 x.2+A*((1+p (.inr 0) x.2/C)*F+weightedTilt m g κ C x.2) ≤
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
    (kineticMean x.1 x.2+A*((1+p (.inr 0) x.2/C)*F+weightedTilt m g κ C x.2)) ≤ H*(2+U+V)
  linarith only [hscaled,hupper,Real.exp_pos (q (.inr 0) x.2)]

theorem momentumRate_energy_upper (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ) (x : TimePhase) :
    momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) ≤
      upperMomentumEnvelope ε κ x.1 (fullHamiltonian ε m g κ x) := by
  apply (momentumRate_upper ε m g κ hε hm hg hκ x).trans
  have hh := (energy_bounds ε m g κ hε.le hm hg hκ.le x).1
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (clock_energy_bound ε m g κ hε.le hm hg hκ.le x) hh.le)
    (mul_pos hκ (Real.exp_pos (2*x.1))).le
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (phaseSize_energy_bound ε m g κ hε.le hm hg hκ.le x) (by norm_num : (0:ℝ) ≤ 2)) hε.le
  unfold upperMomentumEnvelope
  apply mul_le_mul_of_nonneg_left _ hh.le
  convert add_le_add (add_le_add_left h1 2) h2 using 1 <;> ring

theorem momentumRate_lower (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 ≤ κ) (x : TimePhase) :
    -fullHamiltonian ε m g κ x-Real.exp (2*x.1)*weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2/ε-
      2*phaseSize x.2*fullHamiltonian ε m g κ x/ε ≤
        momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  let C := clock ε (q (.inr 0) x.2)
  let H := fullHamiltonian ε m g κ x
  let F := weightedMean m g κ C x.2
  let A := amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)
  let B := p (.inr 0) x.2/C
  let P := phaseSize x.2
  let Q := Real.exp (2*x.1)*F
  have hc : 0 < C := clock_positive ε _ hε.le
  have hH : 0 < H := (energy_bounds ε m g κ hε.le hm hg hκ x).1
  have hP : 0 ≤ P := phaseSize_nonnegative x.2
  have hF : 0 ≤ F := hκ.trans (weightedMean_lower m g κ C hm hg hκ x.2)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := mul_nonneg (Real.exp_pos _).le hF
  have hAF : A*F ≤ C*H := interaction_energy_bound ε m g κ hε.le x
  have hT : -(F*(2*P/C)) ≤ weightedTilt m g κ C x.2 :=
    (abs_le.mp (weightedTilt_abs_bound m g κ C hm hg hκ hc x.2)).1
  have hAT : -(2*P*H) ≤ A*weightedTilt m g κ C x.2 := by
    have h1 := mul_le_mul_of_nonneg_left hT hA
    have h2 := mul_le_mul_of_nonneg_right hAF (div_nonneg (by positivity : 0 ≤ 2*P) hc.le)
    have hid : C*H*(2*P/C) = 2*P*H := by field_simp
    rw [hid] at h2
    nlinarith only [h1,h2]
  have hlinear := mul_le_mul_of_nonneg_left (exponential_linear_lower B) hQ
  have hAB : -Q ≤ A*((1+B)*F) := by
    dsimp [A,B,Q,F,C] at hlinear ⊢
    simp only [amplitude,Real.exp_add]
    nlinarith only [hlinear]
  have hN : -(Q+2*P*H) ≤ kineticMean x.1 x.2+A*((1+B)*F+weightedTilt m g κ C x.2) := by
    nlinarith only [hAB,hAT,kineticMean_nonnegative x.1 x.2]
  have hCexp : Real.exp (q (.inr 0) x.2) ≤ C := by dsimp [C,clock]; linarith
  have hcoef : Real.exp (q (.inr 0) x.2)/C^2 ≤ 1/ε := by
    calc
      _ ≤ C/C^2 := div_le_div_of_nonneg_right hCexp (sq_nonneg C)
      _ = 1/C := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one hε (clock_above_floor ε _).le
  have hclock : Real.exp (q (.inr 0) x.2)/2 ≤ H := by
    linarith [clock_energy_bound ε m g κ hε.le hm hg hκ x]
  have hscaled := mul_le_mul_of_nonneg_left hN
    (div_nonneg (Real.exp_pos (q (.inr 0) x.2)).le (sq_nonneg C))
  have hQscaled : Real.exp (q (.inr 0) x.2)/C^2*(Q+2*P*H) ≤ (Q+2*P*H)/ε := by
    convert mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ Q+2*P*H) using 1
    ring
  change -H-Q/ε-2*P*H/ε ≤ -Real.exp (q (.inr 0) x.2)/2+
    Real.exp (q (.inr 0) x.2)/C^2*(kineticMean x.1 x.2+A*((1+B)*F+weightedTilt m g κ C x.2))
  rw [mul_neg] at hscaled
  have hdiv : (Q+2*P*H)/ε = Q/ε+2*P*H/ε := by ring
  rw [hdiv] at hQscaled
  linarith only [hclock,hscaled,hQscaled]

theorem weightedMean_floor_upper (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 ≤ κ) (x : TimePhase) :
    weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2 ≤
      potentialEnvelope m g κ (phaseSize x.2) |q (.inr 3) x.2| * Real.exp (2*phaseSize x.2/ε) := by
  apply (weightedMean_upper m g κ _ hm hg hκ (clock_positive ε _ hε.le) x.2).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold potentialEnvelope; positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (phaseSize_nonnegative x.2))
    hε (clock_above_floor ε _).le

def lowerMomentumEnvelope (ε m g κ t H P N : ℝ) : ℝ :=
  H+Real.exp (2*t)*potentialEnvelope m g κ P N*Real.exp (2*P/ε)/ε+2*P*H/ε

theorem momentumRate_envelope_lower (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 ≤ κ) (x : TimePhase) :
    -lowerMomentumEnvelope ε m g κ x.1 (fullHamiltonian ε m g κ x) (phaseSize x.2) |q (.inr 3) x.2| ≤
      momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  apply le_trans _ (momentumRate_lower ε m g κ hε hm hg hκ x)
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (weightedMean_floor_upper ε m g κ hε hm hg hκ x) (Real.exp_pos (2*x.1)).le) hε.le
  unfold lowerMomentumEnvelope
  simp only [← mul_assoc] at h
  linarith only [h]

#print axioms clockMomentum_ratio_upper
#print axioms momentumRate_upper
#print axioms momentumRate_energy_upper
#print axioms momentumRate_lower
#print axioms weightedMean_floor_upper
#print axioms momentumRate_envelope_lower

end
end UnifiedTheory.Audit.KFCausalClassicalMatterMomentumBounds
