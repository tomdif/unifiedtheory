/- An exact finite counterexample to occupation = energy for the existing
polynomial Hamiltonian. All matrices are the model's actual matrices,
reindexed onto its seven states at capacity one. -/
import UnifiedTheory.Audit.KFCausalOccupationSeries
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalOccupationEnergyObstruction
noncomputable section
open Matrix
open KFCausalFiniteOccupationLadders KFCausalSpinSourceIdentity
open KFCausalQuantumArealCandidate KFCausalConcreteClockConstraint
open KFCausalReducedSpinHamiltonian KFCausalGradedSpinSource
open KFCausalQuantumConstraintReduction

/-- Vacuum followed by the six single-occupation states. -/
def oneState (i : Fin 7) : State 1 :=
  ⟨fun a => if i.val = a.val + 1 then 1 else 0, by
    fin_cases i <;> norm_num [total, Fin.sum_univ_succ]⟩

def oneEquiv : Fin 7 ≃ State 1 := Equiv.ofBijective oneState (by decide)

def seven (A : Matrix (State 1) (State 1) ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  A.submatrix oneEquiv oneEquiv

theorem seven_mul (A B : Matrix (State 1) (State 1) ℂ) :
    seven (A * B) = seven A * seven B :=
  (Matrix.submatrix_mul_equiv A B oneEquiv oneEquiv oneEquiv).symm

theorem seven_adjoint (A : Matrix (State 1) (State 1) ℂ) :
    seven Aᴴ = (seven A)ᴴ := rfl

theorem seven_add (A B : Matrix (State 1) (State 1) ℂ) :
    seven (A + B) = seven A + seven B := rfl

theorem seven_rsmul (c : ℝ) (A : Matrix (State 1) (State 1) ℂ) :
    seven (c • A) = c • seven A := rfl

theorem seven_csmul (c : ℂ) (A : Matrix (State 1) (State 1) ℂ) :
    seven (c • A) = c • seven A := rfl

theorem seven_sub (A B : Matrix (State 1) (State 1) ℂ) :
    seven (A - B) = seven A - seven B := rfl

theorem seven_neg (A : Matrix (State 1) (State 1) ℂ) : seven (-A) = -seven A := rfl

theorem seven_one : seven 1 = 1 := Matrix.submatrix_one_equiv oneEquiv

theorem seven_gram (A : Matrix (State 1) (State 1) ℂ) : seven (gram A) = gram (seven A) := by
  rw [gram, seven_mul, seven_adjoint]
  rfl

theorem seven_half (A : Matrix (State 1) (State 1) ℂ) :
    seven (halfPolynomial A) = halfPolynomial (seven A) := by
  simp only [halfPolynomial, seven_add, seven_rsmul, seven_one, seven_gram]

def sevenLadder (a : Fin 6) : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => if i = 0 ∧ j.val = a.val + 1 then 1 else 0

set_option maxHeartbeats 2000000 in
-- The finite reindexing checks six ladders at all 49 matrix entries in the kernel.
theorem seven_ladder (a : Fin 6) :
    seven (ladder (R := 1) (fun _ => 1) a) = sevenLadder a := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [seven, oneEquiv, oneState, sevenLadder, ladder, compress, annihilator,
      amplitude, weight, total, lower, Fin.sum_univ_succ] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Expand the nested seven-dimensional Gram products using exact complex arithmetic.
/-- A transition between the vacuum and the single-clock state survives the
charge projection: both states have charge zero, but different occupations. -/
theorem hamiltonian_vacuum_clock_entry :
    hamiltonian 1 (fun _ => 1) 2 0 0 0 0 (oneState 0) (oneState 1) = (-63 / 32 : ℂ) := by
  rw [hamiltonian, dephase_eq_meanPart]
  have hq : charge (oneState 0) = charge (oneState 1) := by decide
  rw [meanPart, if_pos hq]
  change seven (seedHamiltonian 1 (fun _ => 1) 2 0 0 0 0) 0 1 = _
  simp only [seedHamiltonian, kinetic, growing, potentialHamiltonian,
    zero_div, zero_smul, add_zero, mul_zero, Real.exp_zero, one_smul]
  simp only [staticHamiltonian, inverseHalf, fieldP, fieldPi, fieldQx, fieldPhix,
    clockS, momentumPair, gradientPair, skew, seven_add, seven_rsmul, seven_csmul,
    seven_gram, seven_mul, seven_half, seven_neg, seven_sub, seven_adjoint, seven_ladder]
  norm_num [sevenLadder, halfPolynomial, gram, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  norm_num only [Fin.ext_iff, Fin.val_ofNat, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
    Fin.coe_natCast_eq_mod, Fin.val_succ, Fin.val_zero, Fin.val_one, ite_true, ite_false]
  ring_nf; norm_num [Complex.I_sq]

def numberMatrix (R : ℕ) : Matrix (State R) (State R) ℂ :=
  diagonal (fun v => (total v.val : ℂ))

/-- A kernel-checked counterexample: the specified Hamiltonian is not graded by
total occupation, even inside the zero-charge sector. -/
theorem hamiltonian_not_occupation_preserving :
    ¬ Commute (numberMatrix 1) (hamiltonian 1 (fun _ => 1) 2 0 0 0 0) := by
  intro h
  have he := congrArg (fun A => A (oneState 0) (oneState 1)) h.eq
  simp only [numberMatrix, diagonal_mul, mul_diagonal, hamiltonian_vacuum_clock_entry] at he
  norm_num [oneState, total, Fin.sum_univ_succ] at he

theorem hamiltonian_not_affine_number (E0 gap : ℂ) :
    hamiltonian 1 (fun _ => 1) 2 0 0 0 0 ≠ E0 • 1 + gap • numberMatrix 1 := by
  intro h
  have he := congrArg (fun A => A (oneState 0) (oneState 1)) h
  dsimp only at he
  rw [hamiltonian_vacuum_clock_entry] at he
  have hn : oneState 0 ≠ oneState 1 := by decide
  norm_num [numberMatrix, Matrix.one_apply, hn] at he

end
end UnifiedTheory.Audit.KFCausalOccupationEnergyObstruction
