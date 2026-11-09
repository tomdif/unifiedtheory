/- The averaged gravity momentum/gradient pair, including its exact
finite-capacity boundary term. No canonical commutator is assumed. -/
import UnifiedTheory.Audit.KFCausalExponentialEnergyBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGravityPairCoercivity
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.Audit.KFCausalFiniteOccupationLadders
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalQuantumArealCandidate
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalConcreteClockConstraint
open UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian (fieldP fieldQx)
open UnifiedTheory.Audit.KFCausalExponentialClockDynamics
open UnifiedTheory.Audit.KFCausalExponentialEnergyBound

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

theorem gram_pair (A B : M) :
    gram (momentumPair A B)+gram (gradientPair A B)=
      (-2 : ℂ) • (skew A*skew A+skew B*skew B) := by
  have hp : (momentumPair A B).IsHermitian := by
    simpa [momentumPair,smul_add] using (momentum_hermitian A).add (momentum_hermitian B)
  have hq : (gradientPair A B).IsHermitian := by
    simpa [gradientPair,smul_sub] using (momentum_hermitian A).sub (momentum_hermitian B)
  simp only [gram]
  rw [hp.eq,hq.eq]
  simp only [momentumPair,gradientPair,smul_mul_assoc,mul_smul_comm,
    smul_smul,neg_mul_neg,Complex.I_mul_I,neg_one_smul]
  simp only [mul_add,add_mul,mul_sub,sub_mul]
  module

theorem gram_complex_smul (z : ℂ) (A : M) : gram (z • A)=(star z*z) • gram A := by
  simp only [gram,conjTranspose_smul,smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm z]

theorem mean_gram_pair (q : n → ℤ) (k l : ℤ) (A B : M)
    (hk : k ≠ 0) (hl : l ≠ 0) (hA : HasCharge q k A) (hB : HasCharge q l B) :
    meanPart q (gram (momentumPair A B)+gram (gradientPair A B))=
      (2 : ℂ) • (loops A+loops B) := by
  rw [gram_pair,mean_smul,mean_add,mean_skew_square q k A hk hA,
    mean_skew_square q l B hl hB]
  module

/-- Exact charge average of the physical gravity fields. -/
theorem dephase_gravity_pair (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    dephase charge (gram (fieldP R r hbar)+gram (fieldQx R r hbar))=
      hbar • (loops (ladder (R := R) r 1)+loops (ladder r 2)) := by
  have hs : star (Real.sqrt (hbar/2) : ℂ)*(Real.sqrt (hbar/2) : ℂ)=(hbar/2 : ℂ) := by
    simp only [Complex.star_def,Complex.conj_ofReal,← pow_two]
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have ha : HasCharge (charge (R := R)) (-1) (ladder r 1) := by
    simpa [flavorCharge] using ladder_charge (R := R) r 1
  have hb : HasCharge (charge (R := R)) 1 (ladder r 2) := by
    simpa [flavorCharge] using ladder_charge (R := R) r 2
  rw [dephase_eq_meanPart,fieldP,fieldQx,gram_complex_smul,gram_complex_smul,hs,
    ← smul_add,mean_smul,mean_gram_pair charge (-1) 1 _ _ (by norm_num) (by norm_num) ha hb,
    smul_smul]
  norm_num

/-- The exact-amplitude profile still has no upward ladder at N=R. -/
theorem exact_loops (R : ℕ) (a : Fin 6) :
    loops (ladder (R := R) (fun _ => 1) a)=diagonal (fun v : State R =>
      ((2*(v.val a : ℝ)+1-(if total v.val=R then (v.val a : ℝ)+1 else 0) : ℝ) : ℂ)) := by
  rw [loops_ladder]
  congr 1
  funext v
  have hn := v.property
  by_cases ht : total v.val=R
  · simp [weight,ht]
    ring
  · have hlt : total v.val+1 ≤ R := by omega
    simp [weight,hn,hlt,ht]
    ring

def gravityNumber (R : ℕ) : Matrix (State R) (State R) ℂ :=
  diagonal (fun v => ((v.val 1 : ℝ)+(v.val 2 : ℝ) : ℝ))

def gravityBoundary (R : ℕ) : Matrix (State R) (State R) ℂ :=
  diagonal (fun v => ((if total v.val=R then (v.val 1 : ℝ)+(v.val 2 : ℝ)+2 else 0 : ℝ) : ℂ))

theorem gravityNumber_positive (R : ℕ) : (gravityNumber R).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ (((v.val 1 : ℝ)+(v.val 2 : ℝ) : ℝ) : ℂ)
  exact_mod_cast (show (0 : ℝ) ≤ (v.val 1 : ℝ)+(v.val 2 : ℝ) by positivity)

theorem gravityBoundary_positive (R : ℕ) : (gravityBoundary R).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro v
  change (0 : ℂ) ≤ ((if total v.val=R then (v.val 1 : ℝ)+(v.val 2 : ℝ)+2 else 0 : ℝ) : ℂ)
  split_ifs <;> positivity

theorem exact_loops_sum (R : ℕ) :
    loops (ladder (R := R) (fun _ => 1) 1)+loops (ladder (fun _ => 1) 2)=
      (2 : ℝ) • (1 : Matrix (State R) (State R) ℂ)+(2 : ℝ) • gravityNumber R-gravityBoundary R := by
  rw [exact_loops,exact_loops]
  ext i j
  by_cases hij : i=j
  · subst j
    simp [gravityNumber,gravityBoundary]
    split_ifs <;> push_cast <;> ring
  · simp [gravityNumber,gravityBoundary,hij]

omit [DecidableEq n] in
theorem gram_product (A D : M) : gram (A*D)=Dᴴ*gram A*D := by
  simp [gram,mul_assoc]

theorem dephase_gram_pair_product (q : n → ℤ) (A B D : M) (hD : HasCharge q 0 D) :
    dephase q (gram (A*D)+gram (B*D))=Dᴴ*dephase q (gram A+gram B)*D := by
  simp only [gram_product,← add_mul,← mul_add,dephase_eq_meanPart,mean_conjugate q D _ hD]

def clockInverseHalf (R : ℕ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  halfExp (-clockS R (fun _ => 1) hbar)

def inverseClock (R : ℕ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  gram (clockInverseHalf R hbar)

def boundaryClock (R : ℕ) (hbar : ℝ) : Matrix (State R) (State R) ℂ :=
  (clockInverseHalf R hbar)ᴴ*gravityBoundary R*clockInverseHalf R hbar

theorem clockInverseHalf_neutral (R : ℕ) (hbar : ℝ) :
    HasCharge charge 0 (clockInverseHalf R hbar) := by
  apply halfExp_neutral
  intro i j hij
  simp [(clockS_neutral R (fun _ => 1) hbar) i j hij]

theorem inverseClock_exact (R : ℕ) (hbar : ℝ) :
    exponentialClock R (fun _ => 1) hbar*inverseClock R hbar=1 :=
  clock_inverse_exact _ (clockS_hermitian R (fun _ => 1) hbar)

/-- The entire boundary correction is retained in this equality. -/
theorem exact_gravity_pair (R : ℕ) (hbar : ℝ) (hh : 0 ≤ hbar) :
    (1/2 : ℝ) • dephase charge
      (gram (fieldP R (fun _ => 1) hbar*clockInverseHalf R hbar)+
       gram (fieldQx R (fun _ => 1) hbar*clockInverseHalf R hbar))=
      hbar • inverseClock R hbar+
      hbar • ((clockInverseHalf R hbar)ᴴ*gravityNumber R*clockInverseHalf R hbar)-
      (hbar/2 : ℝ) • boundaryClock R hbar := by
  rw [dephase_gram_pair_product charge _ _ _ (clockInverseHalf_neutral R hbar),
    dephase_gravity_pair R (fun _ => 1) hbar hh,exact_loops_sum]
  simp only [mul_smul_comm,smul_mul_assoc,mul_add,mul_sub,add_mul,sub_mul,mul_one,
    inverseClock,boundaryClock,gram]
  module

#print axioms gram_pair
#print axioms mean_gram_pair
#print axioms dephase_gravity_pair
#print axioms exact_loops
#print axioms gravityNumber_positive
#print axioms gravityBoundary_positive
#print axioms exact_loops_sum
#print axioms dephase_gram_pair_product
#print axioms clockInverseHalf_neutral
#print axioms inverseClock_exact
#print axioms exact_gravity_pair

end
end UnifiedTheory.Audit.KFCausalGravityPairCoercivity
