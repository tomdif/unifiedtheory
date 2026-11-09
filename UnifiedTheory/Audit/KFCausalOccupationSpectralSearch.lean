/- A basis-independent test of the occupation-energy proposal in the actual
capacity-one, charge-zero polynomial model. No spectrum is supplied as input. -/
import UnifiedTheory.Audit.KFCausalOccupationEnergyObstruction
import UnifiedTheory.Audit.KFCausalOccupationConstraintSeries

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalOccupationSpectralSearch
noncomputable section
open Matrix
open KFCausalFiniteOccupationLadders KFCausalSpinSourceIdentity
open KFCausalQuantumArealCandidate KFCausalConcreteClockConstraint
open KFCausalReducedSpinHamiltonian KFCausalGradedSpinSource
open KFCausalQuantumConstraintReduction KFCausalOccupationEnergyObstruction
open KFCausalOccupationConstraintSeries

def neutralIndex (i : Fin 3) : Fin 7 := ![0, 1, 6] i
def neutralOne (i : Fin 3) : State 1 := oneState (neutralIndex i)

theorem neutralOne_charge (i : Fin 3) : charge (neutralOne i) = 0 := by
  fin_cases i <;> decide

/-- This is the complete neutral state basis, not a selected subspace. -/
def neutralOneEquiv : Fin 3 ≃ NeutralState 1 :=
  Equiv.ofBijective (fun i => ⟨neutralOne i, neutralOne_charge i⟩) (by decide)

def neutralHamiltonian : Matrix (Fin 3) (Fin 3) ℂ :=
  (hamiltonian 1 (fun _ => 1) 2 0 0 0 0).submatrix neutralOne neutralOne

def neutralMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  !![413 / 64, -63 / 32, 0; -63 / 32, 241 / 128, 0; 0, 0, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check all nine entries after transporting the actual seven-state Gram products.
theorem neutralHamiltonian_eq_matrix : neutralHamiltonian = neutralMatrix := by
  ext i j
  change hamiltonian 1 (fun _ => 1) 2 0 0 0 0 (neutralOne i) (neutralOne j) = _
  rw [hamiltonian, dephase_eq_meanPart, meanPart,
    if_pos ((neutralOne_charge i).trans (neutralOne_charge j).symm)]
  change seven (seedHamiltonian 1 (fun _ => 1) 2 0 0 0 0) (neutralIndex i) (neutralIndex j) = _
  simp only [seedHamiltonian, kinetic, growing, potentialHamiltonian,
    zero_div, zero_smul, add_zero, mul_zero, Real.exp_zero, one_smul]
  simp only [staticHamiltonian, inverseHalf, fieldP, fieldPi, fieldQx, fieldPhix,
    clockS, momentumPair, gradientPair, skew, seven_add, seven_rsmul, seven_csmul,
    seven_gram, seven_mul, seven_half, seven_neg, seven_sub, seven_adjoint, seven_ladder]
  fin_cases i <;> fin_cases j
  all_goals norm_num [neutralIndex, neutralMatrix, sevenLadder, halfPolynomial, gram,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply]
  all_goals norm_num only [Fin.ext_iff, Fin.val_ofNat, Fin.val_natCast, Fin.coe_ofNat_eq_mod,
    Fin.coe_natCast_eq_mod, Fin.val_succ, Fin.val_zero, Fin.val_one, ite_true, ite_false]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

/-- A three-dimensional Hamiltonian with three spectral values cannot satisfy
the quadratic identity forced by the capacity-one occupation multiplicities. -/
theorem neutralHamiltonian_no_quadratic (a b : ℂ) :
    neutralHamiltonian * neutralHamiltonian ≠ a • neutralHamiltonian + b • 1 := by
  rw [neutralHamiltonian_eq_matrix]
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 1) h
  have h22 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 2) h
  norm_num [neutralMatrix, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h01 h22
  simp only [show (2 : Fin 3) = Fin.succ (Fin.succ 0) from rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero] at h22
  norm_num at h22
  have hb : (-7685 / 8192 : ℂ) = 0 := by
    linear_combination h00 - (349 / 126 : ℂ) * h01 - h22
  norm_num at hb

/-- Every similarity transform of an affine idempotent obeys this quadratic.
This applies in particular to every unitary change of occupation basis. -/
theorem similar_affine_idempotent_quadratic
    (N U V : Matrix (Fin 3) (Fin 3) ℂ) (hN : N * N = N)
    (hUV : U * V = 1) (hVU : V * U = 1) (e g : ℂ) :
    let H := U * (e • 1 + g • N) * V
    H * H = (2 * e + g) • H + (-e * (e + g)) • 1 := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := e • 1 + g • N
  have ha : A * A = (2 * e + g) • A + (-e * (e + g)) • 1 := by
    dsimp [A]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hN,
      smul_smul, smul_add]
    module
  change (U * A * V) * (U * A * V) = (2 * e + g) • (U * A * V) + (-e * (e + g)) • 1
  calc
    _ = U * (A * (V * U) * A) * V := by noncomm_ring
    _ = U * (A * A) * V := by rw [hVU, mul_one]
    _ = _ := by
      rw [ha]
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, hUV, mul_assoc]

/-- Changing basis cannot rescue the original `1 + 2q` energy multiplicities
in this model instance. The obstruction covers all invertible similarities. -/
theorem no_affine_idempotent_similarity
    (N U V : Matrix (Fin 3) (Fin 3) ℂ) (hN : N * N = N)
    (hUV : U * V = 1) (hVU : V * U = 1) (e g : ℂ) :
    neutralHamiltonian ≠ U * (e • 1 + g • N) * V := by
  intro h
  apply neutralHamiltonian_no_quadratic (2 * e + g) (-e * (e + g))
  rw [h]
  exact similar_affine_idempotent_quadratic N U V hN hUV hVU e g

end
end UnifiedTheory.Audit.KFCausalOccupationSpectralSearch
