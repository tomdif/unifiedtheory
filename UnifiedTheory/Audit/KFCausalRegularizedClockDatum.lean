/- The actual finite regularized longitudinal datum. The clock and spatial
constraint stay fixed; only the neutral homogeneous datum is changed. -/
import UnifiedTheory.Audit.KFCausalExponentialClockDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedClockDatum
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- An invertible neutral matrix has a neutral inverse. -/
theorem charge_inverse (q : n → ℤ) (A : M) (hA : HasCharge q 0 A) (hu : IsUnit A) :
    HasCharge q 0 A⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hu
  have hm : A*meanPart q A⁻¹=1 := by
    rw [← mean_mul_neutral_left q A A⁻¹ hA,Matrix.mul_nonsing_inv A hd]
    exact mean_zero_charge q 1 (charge_one q)
  have he := congrArg (fun X : M => A⁻¹*X) hm
  have hi : meanPart q A⁻¹=A⁻¹ := by
    simpa only [← mul_assoc,Matrix.nonsing_inv_mul A hd,one_mul,mul_one] using he
  intro i j hij
  have hq : q i ≠ q j := sub_ne_zero.mp hij
  have hp := congrFun (congrFun hi i) j
  simpa [meanPart,hq] using hp.symm

def shiftedClock (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) : Matrix (State R) (State R) ℂ :=
  exponentialClock R r hbar+ε • 1

def mobility (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) : Matrix (State R) (State R) ℂ :=
  (shiftedClock R r hbar ε)⁻¹

def regularizedBase (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) : Matrix (State R) (State R) ℂ :=
  symmetrize (mobility R r hbar ε*clockPs R r hbar)

theorem shiftedClock_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    (shiftedClock R r hbar ε).PosDef :=
  (exponentialClock_positive R r hbar).add_posSemidef (Matrix.PosSemidef.one.smul hε)

theorem shiftedClock_charge (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) :
    HasCharge charge 0 (shiftedClock R r hbar ε) :=
  charge_add charge _ _
    (charge_gram charge _ (halfExp_neutral charge _ (clockS_neutral R r hbar)))
    (charge_real_smul charge 1 ε (charge_one charge))

theorem mobility_positive (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    (mobility R r hbar ε).PosDef := (shiftedClock_positive R r hbar ε hε).inv

theorem mobility_inverse (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    shiftedClock R r hbar ε*mobility R r hbar ε=1 ∧
      mobility R r hbar ε*shiftedClock R r hbar ε=1 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (shiftedClock_positive R r hbar ε hε).isUnit
  exact ⟨Matrix.mul_nonsing_inv _ hu,Matrix.nonsing_inv_mul _ hu⟩

theorem mobility_charge (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    HasCharge charge 0 (mobility R r hbar ε) :=
  charge_inverse charge _ (shiftedClock_charge R r hbar ε)
    (shiftedClock_positive R r hbar ε hε).isUnit

theorem regularizedBase_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) :
    (regularizedBase R r hbar ε).IsHermitian := symmetrize_hermitian _

theorem regularizedBase_neutral (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    spatialDeriv charge (regularizedBase R r hbar ε)=0 := by
  have hp : HasCharge charge 0 (mobility R r hbar ε*clockPs R r hbar) := by
    simpa only [zero_add] using charge_mul charge 0 0 _ _
      (mobility_charge R r hbar ε hε) (clockPs_neutral R r hbar)
  exact neutral_spatialDeriv charge _
    (charge_real_smul charge _ (1/2) (charge_add charge _ _ hp
      (by simpa using charge_adjoint charge 0 _ hp)))

/-- At epsilon=0 this is exactly the previous finite ordering. The
infinite-domain obstruction is not hidden by a different zero-regulator
matrix definition. -/
theorem regularizedBase_zero (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    regularizedBase R r hbar 0=exponentialBase R r hbar := by
  have hi : (exponentialClock R r hbar)⁻¹=gram (halfExp (-clockS R r hbar)) :=
    Matrix.inv_eq_right_inv (clock_inverse_exact _ (clockS_hermitian R r hbar))
  simp only [regularizedBase,mobility,shiftedClock,zero_smul,add_zero,hi,
    gram,(halfExp_hermitian _ (clockS_hermitian R r hbar).neg).eq,exponentialBase]

def regularizedLongitudinal (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) : Matrix (State R) (State R) ℂ :=
  reconstructed (exponentialClock R r hbar) (exponentialClock_positive R r hbar) charge
    (regularizedBase R r hbar ε) (source R r hbar)

def regularizedConstraint (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) : Matrix (State R) (State R) ℂ :=
  source R r hbar-matrixJordan (exponentialClock R r hbar)
    (spatialDeriv charge (regularizedLongitudinal R r hbar ε))

theorem regularizedLongitudinal_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) :
    (regularizedLongitudinal R r hbar ε).IsHermitian :=
  reconstructed_hermitian _ _ charge _ _ (regularizedBase_hermitian R r hbar ε)
    (spin_source_hermitian hbar _ _ _ _ _)

theorem regularizedConstraint_identity (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    regularizedConstraint R r hbar ε=meanPart charge (source R r hbar) :=
  reconstructed_identity _ _ charge (exponentialClock_neutral R r hbar) _ _
    (regularizedBase_neutral R r hbar ε hε)

theorem regularizedConstraint_sector (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    regularizedConstraint R r hbar ε*sector charge 0=0 := by
  rw [regularizedConstraint_identity R r hbar ε hε]
  exact source_annihilates_zero R r hbar

theorem regularizedLongitudinal_zero (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    regularizedLongitudinal R r hbar 0=exponentialLongitudinal R r hbar := by
  simp only [regularizedLongitudinal,regularizedBase_zero,exponentialLongitudinal]

#print axioms charge_inverse
#print axioms shiftedClock_positive
#print axioms mobility_positive
#print axioms mobility_inverse
#print axioms mobility_charge
#print axioms regularizedBase_hermitian
#print axioms regularizedBase_neutral
#print axioms regularizedBase_zero
#print axioms regularizedLongitudinal_hermitian
#print axioms regularizedConstraint_identity
#print axioms regularizedConstraint_sector
#print axioms regularizedLongitudinal_zero

end
end UnifiedTheory.Audit.KFCausalRegularizedClockDatum
