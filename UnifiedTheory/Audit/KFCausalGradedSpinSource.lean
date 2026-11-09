/- Translation grading of the actual quadratic scalar/geometry current.
No canonical commutation relation is assumed; capacity-boundary terms
remain in both A†A and AA†. -/
import UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalGradedSpinSource
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction

variable {n : Type*} [Fintype n]
local notation "M" => Matrix n n ℂ

def HasCharge (q : n → ℤ) (k : ℤ) (A : M) : Prop :=
  ∀ i j, q i-q j ≠ k → A i j=0

omit [Fintype n] in
theorem charge_adjoint (q : n → ℤ) (k : ℤ) (A : M) (hA : HasCharge q k A) :
    HasCharge q (-k) Aᴴ := by
  intro i j hij
  have hn : q j-q i ≠ k := by omega
  simp [Matrix.conjTranspose_apply, hA j i hn]

theorem charge_mul (q : n → ℤ) (k l : ℤ) (A B : M)
    (hA : HasCharge q k A) (hB : HasCharge q l B) : HasCharge q (k+l) (A*B) := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : q i-q a=k
  · have hb : q a-q j ≠ l := by omega
    simp [hB a j hb]
  · simp [hA i a ha]

omit [Fintype n] in
theorem charge_sub (q : n → ℤ) (k : ℤ) (A B : M)
    (hA : HasCharge q k A) (hB : HasCharge q k B) : HasCharge q k (A-B) := by
  intro i j hij; simp [hA i j hij,hB i j hij]

omit [Fintype n] in
theorem charge_smul (q : n → ℤ) (k : ℤ) (A : M) (z : ℂ)
    (hA : HasCharge q k A) : HasCharge q k (z • A) := by
  intro i j hij; simp [hA i j hij]

omit [Fintype n] in
theorem mean_zero_charge (q : n → ℤ) (A : M) (hA : HasCharge q 0 A) : meanPart q A=A := by
  ext i j
  by_cases h : q i=q j
  · simp [meanPart,h]
  · simp [meanPart,h,hA i j (sub_ne_zero.mpr h)]

omit [Fintype n] in
theorem mean_nonzero_charge (q : n → ℤ) (k : ℤ) (A : M) (hk : k ≠ 0)
    (hA : HasCharge q k A) : meanPart q A=0 := by
  ext i j
  by_cases h : q i=q j
  · have hn : q i-q j ≠ k := by omega
    simp [meanPart,h,hA i j hn]
  · simp [meanPart,h]

omit [Fintype n] in
theorem mean_add (q : n → ℤ) (A B : M) : meanPart q (A+B)=meanPart q A+meanPart q B := by
  ext i j; simp [meanPart]; split_ifs <;> simp
omit [Fintype n] in
theorem mean_sub (q : n → ℤ) (A B : M) : meanPart q (A-B)=meanPart q A-meanPart q B := by
  ext i j; simp [meanPart]; split_ifs <;> simp
omit [Fintype n] in
theorem mean_smul (q : n → ℤ) (z : ℂ) (A : M) : meanPart q (z • A)=z • meanPart q A := by
  ext i j; simp [meanPart]
omit [Fintype n] in
theorem mean_neg (q : n → ℤ) (A : M) : meanPart q (-A)= -meanPart q A := by
  ext i j; simp [meanPart]; split_ifs <;> simp

theorem mean_mul_neutral_left (q : n → ℤ) (N A : M) (hN : HasCharge q 0 N) :
    meanPart q (N*A)=N*meanPart q A := by
  ext i j
  simp only [meanPart,Matrix.mul_apply]
  by_cases h : q i=q j
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : q k=q j
    · simp [hk]
    · simp [hk,hN i k (by omega)]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : q k=q j
    · simp [hk,hN i k (by omega)]
    · simp [hk]

theorem mean_mul_neutral_right (q : n → ℤ) (A N : M) (hN : HasCharge q 0 N) :
    meanPart q (A*N)=meanPart q A*N := by
  ext i j
  simp only [meanPart,Matrix.mul_apply]
  by_cases h : q i=q j
  · rw [if_pos h]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : q i=q k
    · simp [hk]
    · simp [hk,hN k j (by omega)]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : q i=q k
    · simp [hk,hN k j (by omega)]
    · simp [hk]

/-- Averaging is covariant under charge-preserving changes of basis.
The equality also holds for nonunitary charge-preserving matrices. -/
theorem mean_conjugate (q : n → ℤ) (U A : M) (hU : HasCharge q 0 U) :
    meanPart q (Uᴴ*A*U)=Uᴴ*meanPart q A*U := by
  rw [mean_mul_neutral_right q _ U hU,mean_mul_neutral_left]
  simpa using charge_adjoint q 0 U hU

theorem neutral_commutes_sector [DecidableEq n] (q : n → ℤ) (U : M)
    (hU : HasCharge q 0 U) (k : ℤ) : Commute U (sector q k) := by
  have h := dephase_commutes_sector q U k
  rwa [dephase_eq_meanPart,mean_zero_charge q U hU] at h

def skew (A : M) : M := A-Aᴴ
def loops (A : M) : M := A*Aᴴ+Aᴴ*A
def momentumPair (A B : M) : M := -Complex.I • (skew A+skew B)
def gradientPair (A B : M) : M := -Complex.I • (skew A-skew B)
def current (P D : M) : M := (1/2 : ℂ) • (P*D+D*P)

theorem pair_current_expansion (A B : M) :
    current (momentumPair A B) (gradientPair A B)= -(skew A*skew A)+skew B*skew B := by
  simp only [current, momentumPair, gradientPair, smul_mul_assoc, mul_smul_comm,
    smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  module

theorem mean_skew_square (q : n → ℤ) (k : ℤ) (A : M) (hk : k ≠ 0)
    (hA : HasCharge q k A) : meanPart q (skew A*skew A)= -loops A := by
  have had := charge_adjoint q k A hA
  have haa := mean_nonzero_charge q (k+k) (A*A) (by omega) (charge_mul q k k A A hA hA)
  have hdd := mean_nonzero_charge q (-k+-k) (Aᴴ*Aᴴ) (by omega)
    (charge_mul q (-k) (-k) Aᴴ Aᴴ had had)
  have had' : meanPart q (A*Aᴴ)=A*Aᴴ :=
    mean_zero_charge q _ (by simpa using charge_mul q k (-k) A Aᴴ hA had)
  have hda : meanPart q (Aᴴ*A)=Aᴴ*A :=
    mean_zero_charge q _ (by simpa using charge_mul q (-k) k Aᴴ A had hA)
  have he : skew A*skew A=A*A-A*Aᴴ-Aᴴ*A+Aᴴ*Aᴴ := by unfold skew; noncomm_ring
  rw [he,mean_add,mean_sub,mean_sub,haa,hdd,had',hda]
  unfold loops
  abel

theorem mean_pair_current (q : n → ℤ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    meanPart q (current (momentumPair A B) (gradientPair A B))=loops A-loops B := by
  rw [pair_current_expansion,mean_add,mean_neg,
    mean_skew_square q (-1) A (by omega) hA,mean_skew_square q 1 B (by omega) hB]
  abel

theorem neutral_skew_mean (q : n → ℤ) (k : ℤ) (N A : M)
    (hN : HasCharge q 0 N) (hA : HasCharge q k A) (hk : k ≠ 0) :
    meanPart q (N*skew A)=0 ∧ meanPart q (skew A*N)=0 := by
  have had := charge_adjoint q k A hA
  have hna := mean_nonzero_charge q k (N*A) hk (by simpa using charge_mul q 0 k N A hN hA)
  have hnd := mean_nonzero_charge q (-k) (N*Aᴴ) (by omega)
    (by simpa using charge_mul q 0 (-k) N Aᴴ hN had)
  have han := mean_nonzero_charge q k (A*N) hk (by simpa using charge_mul q k 0 A N hA hN)
  have hdn := mean_nonzero_charge q (-k) (Aᴴ*N) (by omega)
    (by simpa using charge_mul q (-k) 0 Aᴴ N had hN)
  simp [skew,mul_sub,sub_mul,mean_sub,hna,hnd,han,hdn]

theorem neutral_current_mean (q : n → ℤ) (N A B : M)
    (hN : HasCharge q 0 N) (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    meanPart q (current N (gradientPair A B))=0 := by
  obtain ⟨ha,ha'⟩ := neutral_skew_mean q (-1) N A hN hA (by omega)
  obtain ⟨hb,hb'⟩ := neutral_skew_mean q 1 N B hN hB (by omega)
  simp [current,gradientPair,mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,
    mean_smul,mean_add,mean_sub,mean_neg,ha,ha',hb,hb']

def spinSource (hbar : ℝ) (A B C D Z : M) : M := (hbar/2 : ℂ) •
  (current (momentumPair A B) (gradientPair A B)+
   current (momentumPair C D-Complex.I • skew Z) (gradientPair C D))

theorem spinSource_mean (q : n → ℤ) (hbar : ℝ) (A B C D Z : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B)
    (hC : HasCharge q (-1) C) (hD : HasCharge q 1 D) (hZ : HasCharge q 0 Z) :
    meanPart q (spinSource hbar A B C D Z)=
      (hbar/2 : ℂ) • (loops A-loops B+loops C-loops D) := by
  have hn : HasCharge q 0 (Complex.I • skew Z) :=
    charge_smul q 0 _ Complex.I (charge_sub q 0 Z Zᴴ hZ (by simpa using charge_adjoint q 0 Z hZ))
  have he : current (momentumPair C D-Complex.I • skew Z) (gradientPair C D)=
      current (momentumPair C D) (gradientPair C D)-current (Complex.I • skew Z) (gradientPair C D) := by
    simp [current,sub_mul,mul_sub,smul_sub]
    module
  rw [spinSource,mean_smul,mean_add,he,mean_sub,
    mean_pair_current q A B hA hB,mean_pair_current q C D hC hD,
    neutral_current_mean q _ C D hn hC hD]
  congr 1
  abel

#print axioms mean_conjugate
#print axioms neutral_commutes_sector
#print axioms charge_mul
#print axioms mean_pair_current
#print axioms neutral_current_mean
#print axioms spinSource_mean

end
end UnifiedTheory.Audit.KFCausalGradedSpinSource
