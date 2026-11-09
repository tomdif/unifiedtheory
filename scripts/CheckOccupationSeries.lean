import UnifiedTheory.Audit.KFCausalOccupationConstraintSeries
import UnifiedTheory.Audit.KFCausalOccupationEnergyObstruction

open UnifiedTheory.Audit
open KFCausalOccupationSeries KFCausalOccupationConstraintSeries
open KFCausalOccupationEnergyObstruction KFCausalConcreteClockConstraint

#print axioms card_shell
#print axioms occupation_euler
#print axioms shell_dimension_eq_euler_coeff
#print axioms occupationCharacter_matches_euler
#print axioms occupationCharacter_above_cutoff
#print axioms ladder_number_operator
#print axioms card_neutralShell
#print axioms neutralCharacter_matches_series
#print axioms neutral_shell_dimension
#print axioms unit_coefficient_ne_zero
#print axioms constraint_kernel_iff
#print axioms neutralEquivKernel
#print axioms constraint_kernel_dimension_series
#print axioms constraint_commutes_occupation
#print axioms hamiltonian_preserves_neutral
#print axioms neutral_coefficients_through_four
#print axioms seven_ladder
#print axioms hamiltonian_vacuum_clock_entry
#print axioms hamiltonian_not_occupation_preserving
#print axioms hamiltonian_not_affine_number

-- Generic coefficients from the actual shell, including the capacity boundary.
example (R : ℕ) (hR : 4 ≤ R) : Fintype.card (Shell 6 R 4) = 126 := by
  rw [card_shell 6 R 4 (by omega) hR]
  decide

-- An independently enumerated neutral shell is strictly smaller.
example (R : ℕ) (hR : 4 ≤ R) : Fintype.card (NeutralShell R 4) = 26 := by
  rw [card_neutralShell R 4 hR]
  exact neutral_coefficients_through_four.2.2.2.2

-- Actual constraint kernel, not just a formally named state count.
example : Module.finrank ℂ
    (LinearMap.ker (Matrix.mulVecLin (constraint 3 (fun _ => 1) 2))) = 22 := by
  rw [constraint_kernel_dimension_series 3 (fun _ => 1) 2
    (unit_coefficient_ne_zero 3 2 (by norm_num))]
  decide

-- A finite cutoff never acquires spurious states above its capacity.
example : PowerSeries.coeff 5 (occupationCharacter 6 4) = 0 :=
  occupationCharacter_above_cutoff 6 4 5 (by omega)
