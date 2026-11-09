/- Explicit finite counterpart of the optional equal-mobility clock floor.
The shifted positive clock is used in both the homogeneous datum and the
Jordan reconstruction. This is a new model variant; the old regularized
datum remains unchanged. An exact residual identity quantifies why merely
relabeling that old datum is insufficient. No capacity limit is proved. -/
import UnifiedTheory.Audit.KFCausalRegularizedClockDatum
import UnifiedTheory.Audit.KFCausalCommutingClockReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorFiniteReconstruction
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalPositiveClockReconstruction
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalRegularizedClockDatum

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

theorem matrixJordan_shift (C X : M) (ε : ℝ) :
    matrixJordan (C + ε • 1) X = matrixJordan C X + ε • X := by
  ext i j
  simp [matrixJordan, add_mul, mul_add]
  ring

omit [DecidableEq n] in
theorem matrixJordan_sub (C X Y : M) :
    matrixJordan C (X-Y) = matrixJordan C X - matrixJordan C Y := by
  simp only [matrixJordan, mul_sub, sub_mul, smul_sub, smul_add]
  abel

theorem matrixJordan_real_smul (C X : M) (ε : ℝ) :
    matrixJordan C (ε • X) = ε • matrixJordan C X := by
  ext i j
  simp [matrixJordan]
  ring

/-- Exact resolvent identity for the two Jordan reconstructions. It
quantifies the correction needed before any finite-to-infinite comparison. -/
theorem solveJordan_shift_correction (C K : M) (hC : C.PosDef) (ε : ℝ)
    (hD : (C + ε • 1).PosDef) :
    solveJordan (C + ε • 1) hD K = solveJordan C hC K -
      ε • solveJordan (C + ε • 1) hD (solveJordan C hC K) := by
  apply matrixJordan_injective (C + ε • 1) hD
  rw [matrixJordan_sub, matrixJordan_real_smul, solveJordan_spec,
    solveJordan_spec, matrixJordan_shift, solveJordan_spec]
  abel

/-- Exact error if the old regularized longitudinal operator is retained
while the clock in the spatial constraint is replaced by its shifted value. -/
theorem old_datum_shifted_residual (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    source R r hbar - matrixJordan (shiftedClock R r hbar ε)
      (spatialDeriv charge (regularizedLongitudinal R r hbar ε)) =
    meanPart charge (source R r hbar) -
      ε • spatialDeriv charge (regularizedLongitudinal R r hbar ε) := by
  have h := regularizedConstraint_identity R r hbar ε hε
  unfold regularizedConstraint at h
  rw [shiftedClock, matrixJordan_shift, sub_add_eq_sub_sub, h]

theorem old_datum_shifted_residual_eq_iff (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ)
    (hε : 0 < ε) :
    (source R r hbar - matrixJordan (shiftedClock R r hbar ε)
      (spatialDeriv charge (regularizedLongitudinal R r hbar ε)) =
      meanPart charge (source R r hbar)) ↔
    spatialDeriv charge (regularizedLongitudinal R r hbar ε) = 0 := by
  rw [old_datum_shifted_residual R r hbar ε hε.le, sub_eq_self]
  exact smul_eq_zero_iff_right hε.ne'

def floorLongitudinal (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    Matrix (State R) (State R) ℂ :=
  reconstructed (shiftedClock R r hbar ε) (shiftedClock_positive R r hbar ε hε)
    charge (regularizedBase R r hbar ε) (source R r hbar)

def floorConstraint (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    Matrix (State R) (State R) ℂ :=
  source R r hbar - matrixJordan (shiftedClock R r hbar ε)
    (spatialDeriv charge (floorLongitudinal R r hbar ε hε))

theorem floorLongitudinal_hermitian (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    (floorLongitudinal R r hbar ε hε).IsHermitian :=
  reconstructed_hermitian _ _ charge _ _ (regularizedBase_hermitian R r hbar ε)
    (spin_source_hermitian hbar _ _ _ _ _)

theorem floorConstraint_identity (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    floorConstraint R r hbar ε hε = meanPart charge (source R r hbar) :=
  reconstructed_identity _ _ charge
    (neutral_spatialDeriv charge _ (shiftedClock_charge R r hbar ε)) _ _
    (regularizedBase_neutral R r hbar ε hε)

theorem floorConstraint_sector (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    floorConstraint R r hbar ε hε * sector charge 0 = 0 := by
  rw [floorConstraint_identity]
  exact source_annihilates_zero R r hbar

theorem floorLongitudinal_zero (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    floorLongitudinal R r hbar 0 (by norm_num) = exponentialLongitudinal R r hbar := by
  have hc : shiftedClock R r hbar 0 = exponentialClock R r hbar := by
    simp [shiftedClock]
  unfold floorLongitudinal exponentialLongitudinal reconstructed
  rw [regularizedBase_zero]
  apply congrArg (fun X => exponentialBase R r hbar + X)
  apply solveJordan_unique
  have hs := solveJordan_spec (shiftedClock R r hbar 0)
    (shiftedClock_positive R r hbar 0 (by norm_num)) (primitive charge (source R r hbar))
  exact (congrArg (fun C => matrixJordan C (solveJordan (shiftedClock R r hbar 0)
    (shiftedClock_positive R r hbar 0 (by norm_num))
    (primitive charge (source R r hbar)))) hc).symm.trans hs

/-- The inverse-clock formula is derived only when the source primitive
commutes with the shifted clock. This is still an obligation for a limit. -/
theorem floorLongitudinal_commuting (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε)
    (hcomm : Commute (shiftedClock R r hbar ε) (primitive charge (source R r hbar))) :
    floorLongitudinal R r hbar ε hε = regularizedBase R r hbar ε +
      mobility R r hbar ε * primitive charge (source R r hbar) :=
  UnifiedTheory.Audit.KFCausalCommutingClockReconstruction.reconstructed_commuting
    _ _ charge _ _ hcomm

theorem floorLongitudinal_correction (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 ≤ ε) :
    floorLongitudinal R r hbar ε hε = regularizedLongitudinal R r hbar ε -
      ε • solveJordan (shiftedClock R r hbar ε) (shiftedClock_positive R r hbar ε hε)
        (regularizedLongitudinal R r hbar ε - regularizedBase R r hbar ε) := by
  unfold floorLongitudinal regularizedLongitudinal reconstructed
  rw [add_sub_cancel_left]
  have hc := solveJordan_shift_correction (exponentialClock R r hbar)
    (primitive charge (source R r hbar)) (exponentialClock_positive R r hbar) ε
    (shiftedClock_positive R r hbar ε hε)
  change solveJordan (shiftedClock R r hbar ε) _ _ = _ at hc
  rw [hc]
  abel

/-- Unless the old spatial derivative vanishes, the finite repair really
changes the longitudinal matrix; it is not a new name for the old model. -/
theorem floorLongitudinal_ne_old (R : ℕ) (r : ℕ → ℝ) (hbar ε : ℝ) (hε : 0 < ε)
    (hδ : spatialDeriv charge (regularizedLongitudinal R r hbar ε) ≠ 0) :
    floorLongitudinal R r hbar ε hε.le ≠ regularizedLongitudinal R r hbar ε := by
  intro he
  have h := floorConstraint_identity R r hbar ε hε.le
  unfold floorConstraint at h
  rw [he] at h
  exact hδ ((old_datum_shifted_residual_eq_iff R r hbar ε hε).mp h)

#print axioms matrixJordan_shift
#print axioms solveJordan_shift_correction
#print axioms old_datum_shifted_residual
#print axioms old_datum_shifted_residual_eq_iff
#print axioms floorLongitudinal_hermitian
#print axioms floorConstraint_identity
#print axioms floorConstraint_sector
#print axioms floorLongitudinal_zero
#print axioms floorLongitudinal_commuting
#print axioms floorLongitudinal_correction
#print axioms floorLongitudinal_ne_old

end
end UnifiedTheory.Audit.KFCausalClockFloorFiniteReconstruction
