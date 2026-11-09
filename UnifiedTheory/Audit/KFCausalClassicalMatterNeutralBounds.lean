/- Energy controls neutral-position velocity even with nonzero matter.
This replaces the cyclic-position argument used only in the vacuum case. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
import UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterNeutralBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalMatterNeutralShift
open UnifiedTheory.Audit.KFCausalClassicalMatterOrbitBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds (phaseSize)
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds (phaseSize_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock clock_above_floor)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

theorem neutralSpeed_energy_bound (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 ≤ κ) (x : TimePhase) :
    |q (.inr 3) (field ε m g κ x).2| ≤ (phaseSize x.2+1)/ε+
      fullHamiltonian ε m g κ x*(4*(phaseSize x.2+1))/ε := by
  let C := clock ε (q (.inr 0) x.2)
  let A := amplitude ε x.1 (q (.inr 0) x.2) (p (.inr 0) x.2)
  let F := weightedMean m g κ C x.2
  let L := 4*(phaseSize x.2+1)
  have hc : 0 < C := clock_positive ε _ hε.le
  have hfloor : ε ≤ C := (clock_above_floor ε _).le
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hH := (energy_bounds ε m g κ hε.le hm hg hκ x).1
  have hP := phaseSize_nonnegative x.2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hF : 0 ≤ F := hκ.trans (weightedMean_lower m g κ C hm hg hκ x.2)
  have hn := neutralMean_abs_bound m g κ C hm hg hκ x.2
  have he : A*F ≤ C*fullHamiltonian ε m g κ x := interaction_energy_bound ε m g κ hε.le x
  have hr : |p (.inr 3) x.2/C| ≤ (phaseSize x.2+1)/ε := by
    rw [abs_div,abs_of_pos hc]
    exact (div_le_div_of_nonneg_right (distinguished_abs_bounds x.2).2.2 hc.le).trans
      (div_le_div_of_nonneg_left (by positivity) hε hfloor)
  have hi : |A*neutralMean m g κ C x.2/C^2| ≤ fullHamiltonian ε m g κ x*L/ε := by
    rw [abs_div,abs_mul,abs_of_nonneg hA,abs_of_pos (sq_pos_of_pos hc)]
    calc
      _ ≤ A*(F*L)/C^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) (sq_nonneg C)
      _ = A*F*L/C^2 := by ring
      _ ≤ C*fullHamiltonian ε m g κ x*L/C^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hL) (sq_nonneg C)
      _ = fullHamiltonian ε m g κ x*L/C := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hH.le hL) hε hfloor
  rw [field_neutralPosition ε m g κ hε.le]
  exact (abs_add_le _ _).trans (add_le_add hr hi)

#print axioms neutralSpeed_energy_bound

end
end UnifiedTheory.Audit.KFCausalClassicalMatterNeutralBounds
