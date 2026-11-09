/- The Jordan reconstruction simplifies to C^(-1)K exactly when the
clock commutes with the source primitive. This condition is not assumed
for the finite capacity model; it isolates the tensor-limit obligation. -/
import UnifiedTheory.Audit.KFCausalPositiveClockReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCommutingClockReconstruction
noncomputable section
open Matrix
open scoped ComplexOrder
open UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

theorem inverse_primitive_solves (C K : M) (hC : C.PosDef) (hCK : Commute C K) :
    matrixJordan C (C⁻¹*K) = K := by
  have hu := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hl : C*(C⁻¹*K) = K := by rw [← mul_assoc,Matrix.mul_nonsing_inv _ hu,one_mul]
  have hr : (C⁻¹*K)*C = K := by
    rw [mul_assoc,← hCK.eq,← mul_assoc,Matrix.nonsing_inv_mul _ hu,one_mul]
  rw [matrixJordan,hl,hr]
  module

theorem solveJordan_commuting (C K : M) (hC : C.PosDef) (hCK : Commute C K) :
    solveJordan C hC K = C⁻¹*K :=
  (solveJordan_unique C hC K _ (inverse_primitive_solves C K hC hCK)).symm

theorem reconstructed_commuting (C : M) (hC : C.PosDef) (q : n → ℤ) (base source : M)
    (hCK : Commute C (primitive q source)) :
    reconstructed C hC q base source = base+C⁻¹*primitive q source := by
  rw [reconstructed,solveJordan_commuting C _ hC hCK]

#print axioms inverse_primitive_solves
#print axioms solveJordan_commuting
#print axioms reconstructed_commuting

end
end UnifiedTheory.Audit.KFCausalCommutingClockReconstruction
