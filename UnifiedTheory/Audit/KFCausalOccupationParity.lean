/- Occupation parity repairs the boundary defect in the inverse-clock
estimate. This is an exact finite-matrix identity, including the top shell. -/
import UnifiedTheory.Audit.KFCausalGravityPairCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalOccupationParity
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalGravityPairCoercivity

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local instance : NormedAlgebra ℚ M := NormedAlgebra.restrictScalars ℚ ℂ M

/-- Anticommutation with an involution gives an exponential congruence. -/
theorem halfExp_parity (S J : M) (hJ : J*J=1) (hS : J*S= -S*J) :
    halfExp S*J*halfExp S=J := by
  let u : Mˣ := ⟨J,J,hJ,hJ⟩
  have hc : J*((1/2 : ℝ) • S)*J=(1/2 : ℝ) • (-S) := by
    rw [mul_smul_comm,smul_mul_assoc,hS]
    simp [mul_assoc,hJ]
  have he := NormedSpace.exp_units_conj u ((1/2 : ℝ) • S)
  change NormedSpace.exp (J*((1/2 : ℝ) • S)*J)=J*halfExp S*J at he
  rw [hc] at he
  change halfExp (-S)=J*halfExp S*J at he
  have hd := halfExp_inverse S
  rw [he] at hd
  have hh := congrArg (fun X : M => X*J) hd
  simpa only [mul_assoc,hJ,mul_one,one_mul] using hh

/-- A useful positive remainder: exp(S)-J = F†(I-J)F. -/
theorem clock_minus_parity_positive (S J : M) (hS : S.IsHermitian)
    (hJ : J*J=1) (hanti : J*S= -S*J) (hp : (1-J).PosSemidef) :
    (gram (halfExp S)-J).PosSemidef := by
  have he := halfExp_parity S J hJ hanti
  have h := hp.conjTranspose_mul_mul_same (halfExp S)
  convert h using 1
  simp only [mul_sub,sub_mul,mul_one,gram,(halfExp_hermitian S hS).eq,he]

def paritySign (R : ℕ) (v : State R) : ℝ := (-1 : ℝ)^(R+total v.val)
def occupationParity (R : ℕ) : Matrix (State R) (State R) ℂ :=
  diagonal (fun v => (paritySign R v : ℂ))

theorem paritySign_cases (R : ℕ) (v : State R) : paritySign R v=1 ∨ paritySign R v= -1 :=
  neg_one_pow_eq_or ℝ (R+total v.val)

theorem paritySign_top (R : ℕ) (v : State R) (hv : total v.val=R) : paritySign R v=1 := by
  simp [paritySign,hv,pow_add,← pow_two,← pow_mul,← mul_comm 2 R]

theorem parity_square (R : ℕ) : occupationParity R*occupationParity R=1 := by
  rw [occupationParity,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    rcases paritySign_cases R i with h | h <;> simp [h]
  · simp [hij]

theorem parity_hermitian (R : ℕ) : (occupationParity R).IsHermitian := by
  unfold occupationParity Matrix.IsHermitian
  simp

theorem one_minus_parity_positive (R : ℕ) : (1-occupationParity R).PosSemidef := by
  have he : (1 : Matrix (State R) (State R) ℂ)-occupationParity R=
      diagonal (fun v => (1-paritySign R v : ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [occupationParity,hij]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ 1-(paritySign R v : ℂ)
  rcases paritySign_cases R v with h | h <;> norm_num [h]

theorem clock_lower_total (R : ℕ) (v : Occupation 6 R) (hv : 0 < (v 0 : ℕ)) :
    total (lower 0 v)+1=total v := by
  simp [total,Fin.sum_univ_succ,lower]
  omega

theorem parity_ladder (R : ℕ) (r : ℕ → ℝ) :
    occupationParity R*ladder r 0= -ladder r 0*occupationParity R := by
  ext i j
  simp only [occupationParity,diagonal_mul,mul_diagonal,neg_apply]
  by_cases h : 0 < (j.val 0 : ℕ) ∧ i.val=lower 0 j.val
  · have ht : total i.val+1=total j.val := by rw [h.2]; exact clock_lower_total R j.val h.1
    have hs : paritySign R j= -paritySign R i := by
      unfold paritySign
      rw [← ht,← Nat.add_assoc,pow_succ]
      ring
    simp only [hs,Complex.ofReal_neg,mul_neg]
    ring
  · have hz : ladder r 0 i j=0 := if_neg h
    simp [hz]

theorem parity_clockS (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    occupationParity R*clockS R r hbar= -clockS R r hbar*occupationParity R := by
  have ha := parity_ladder R r
  have had := congrArg Matrix.conjTranspose ha
  simp only [conjTranspose_mul,conjTranspose_neg,(parity_hermitian R).eq] at had
  have had' : occupationParity R*(ladder r 0)ᴴ= -(ladder r 0)ᴴ*occupationParity R := by
    have hn := congrArg (fun X : Matrix (State R) (State R) ℂ => -X) had
    simpa only [neg_mul,mul_neg,neg_neg] using hn.symm
  simp only [clockS,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,neg_mul]
  rw [ha,had']
  simp only [neg_mul]
  module

/-- The gravity pair has enough positive weight on the opposite parity.
The top shell has parity +1, so it contributes no negative remainder. -/
theorem loops_minus_parity_positive (R : ℕ) :
    (loops (ladder (R := R) (fun _ => 1) 1)+loops (ladder (fun _ => 1) 2)-
      (1-occupationParity R)).PosSemidef := by
  have he : loops (ladder (R := R) (fun _ => 1) 1)+loops (ladder (fun _ => 1) 2)-
      (1-occupationParity R)=diagonal (fun v : State R =>
      ((1+2*((v.val 1 : ℝ)+(v.val 2 : ℝ))+paritySign R v-
        (if total v.val=R then (v.val 1 : ℝ)+(v.val 2 : ℝ)+2 else 0) : ℝ) : ℂ)) := by
    rw [exact_loops_sum]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [gravityNumber,gravityBoundary,occupationParity]
      ring
    · simp [gravityNumber,gravityBoundary,occupationParity,hij]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ ((1+2*((v.val 1 : ℝ)+(v.val 2 : ℝ))+paritySign R v-
    (if total v.val=R then (v.val 1 : ℝ)+(v.val 2 : ℝ)+2 else 0) : ℝ) : ℂ)
  norm_cast
  by_cases ht : total v.val=R
  · rw [if_pos ht,paritySign_top R v ht]
    have hn : (0 : ℝ) ≤ (v.val 1 : ℝ)+(v.val 2 : ℝ) := by positivity
    push_cast
    linarith
  · rw [if_neg ht]
    have hn : (0 : ℝ) ≤ (v.val 1 : ℝ)+(v.val 2 : ℝ) := by positivity
    rcases paritySign_cases R v with h | h <;> rw [h] <;> push_cast <;> linarith

#print axioms halfExp_parity
#print axioms clock_minus_parity_positive
#print axioms paritySign_top
#print axioms parity_square
#print axioms parity_hermitian
#print axioms one_minus_parity_positive
#print axioms clock_lower_total
#print axioms parity_ladder
#print axioms parity_clockS
#print axioms loops_minus_parity_positive

end
end UnifiedTheory.Audit.KFCausalOccupationParity
