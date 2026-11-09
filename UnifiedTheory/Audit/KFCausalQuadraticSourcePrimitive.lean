/- Exact quadratic spatial primitive of the actual six-mode source.
Only translation charges are used; no CCR or removal of capacity-boundary
terms is assumed. The formula exposes the transverse dilation and shear
which must be treated in the infinite-dimensional longitudinal operator. -/
import UnifiedTheory.Audit.KFCausalGradedSpinSource
import UnifiedTheory.Audit.KFCausalSpinSourceIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalQuadraticSourcePrimitive
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalQuantumConstraintReduction
open UnifiedTheory.Audit.KFCausalGradedSpinSource
open UnifiedTheory.Audit.KFCausalSpinSourceIdentity

variable {n : Type*} [Fintype n]
local notation "M" => Matrix n n ℂ

omit [Fintype n] in
theorem primitive_add (q : n → ℤ) (A B : M) : primitive q (A+B) = primitive q A+primitive q B := by
  ext i j
  simp only [primitive,Matrix.add_apply]
  split_ifs <;> simp [add_div]

omit [Fintype n] in
theorem primitive_sub (q : n → ℤ) (A B : M) : primitive q (A-B) = primitive q A-primitive q B := by
  ext i j
  simp only [primitive,Matrix.sub_apply]
  split_ifs <;> simp [sub_div]

omit [Fintype n] in
theorem primitive_smul (q : n → ℤ) (c : ℂ) (A : M) : primitive q (c • A) = c • primitive q A := by
  ext i j
  simp only [primitive,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp [mul_div_assoc]

omit [Fintype n] in
theorem primitive_charge (q : n → ℤ) (k : ℤ) (A : M) (hk : k ≠ 0) (hA : HasCharge q k A) :
    primitive q A = (Complex.I*(k:ℂ))⁻¹ • A := by
  ext i j
  by_cases h : q i-q j = k
  · have hq : q i ≠ q j := by omega
    simp [primitive,hq,h,div_eq_mul_inv,mul_comm]
  · simp [primitive,hA i j h]

omit [Fintype n] in
theorem primitive_neutral (q : n → ℤ) (A : M) (hA : HasCharge q 0 A) : primitive q A = 0 := by
  ext i j
  by_cases h : q i = q j
  · simp [primitive,h]
  · simp [primitive,h,hA i j (sub_ne_zero.mpr h)]

theorem primitive_skew_square (q : n → ℤ) (k : ℤ) (A : M) (hk : k ≠ 0) (hA : HasCharge q k A) :
    primitive q (skew A*skew A) = (Complex.I*((k+k:ℤ):ℂ))⁻¹ • (A*A-Aᴴ*Aᴴ) := by
  have had := charge_adjoint q k A hA
  have haa := primitive_charge q (k+k) (A*A) (by omega) (charge_mul q k k A A hA hA)
  have hdd := primitive_charge q (-k+-k) (Aᴴ*Aᴴ) (by omega) (charge_mul q (-k) (-k) Aᴴ Aᴴ had had)
  have had' := primitive_neutral q (A*Aᴴ) (by simpa using charge_mul q k (-k) A Aᴴ hA had)
  have hda := primitive_neutral q (Aᴴ*A) (by simpa using charge_mul q (-k) k Aᴴ A had hA)
  have he : skew A*skew A = A*A-A*Aᴴ-Aᴴ*A+Aᴴ*Aᴴ := by unfold skew; noncomm_ring
  rw [he,primitive_add,primitive_sub,primitive_sub,haa,hdd,had',hda]
  simp only [show -k+-k = -(k+k) by omega,Int.cast_neg,mul_neg,inv_neg,neg_smul,sub_zero,smul_sub]
  abel

theorem inverse_charge_two : (Complex.I*2)⁻¹ = -Complex.I/2 := by
  rw [_root_.mul_inv_rev,Complex.inv_I]
  ring

theorem primitive_pair (q : n → ℤ) (A B : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B) :
    primitive q (current (momentumPair A B) (gradientPair A B)) =
      (-Complex.I/2) • ((A*A-Aᴴ*Aᴴ)+(B*B-Bᴴ*Bᴴ)) := by
  have ha := primitive_skew_square q (-1) A (by norm_num) hA
  have hb := primitive_skew_square q 1 B (by norm_num) hB
  norm_num only [neg_add_rev,neg_add,Int.cast_neg,mul_neg,inv_neg] at ha hb
  rw [pair_current_expansion,show -(skew A*skew A) = (-1:ℂ) • (skew A*skew A) by simp,
    primitive_add,primitive_smul,ha,hb]
  rw [inverse_charge_two]
  module

theorem primitive_neutral_left (q : n → ℤ) (k : ℤ) (N A : M)
    (hN : HasCharge q 0 N) (hA : HasCharge q k A) (hk : k ≠ 0) :
    primitive q (N*skew A) = (Complex.I*(k:ℂ))⁻¹ • (N*(A+Aᴴ)) := by
  have ha := primitive_charge q k (N*A) hk (by simpa using charge_mul q 0 k N A hN hA)
  have hd := primitive_charge q (-k) (N*Aᴴ) (by omega)
    (by simpa using charge_mul q 0 (-k) N Aᴴ hN (charge_adjoint q k A hA))
  rw [skew,mul_sub,primitive_sub,ha,hd]
  simp only [Int.cast_neg,mul_neg,inv_neg,neg_smul,mul_add,smul_add]
  abel

theorem primitive_neutral_right (q : n → ℤ) (k : ℤ) (N A : M)
    (hN : HasCharge q 0 N) (hA : HasCharge q k A) (hk : k ≠ 0) :
    primitive q (skew A*N) = (Complex.I*(k:ℂ))⁻¹ • ((A+Aᴴ)*N) := by
  have ha := primitive_charge q k (A*N) hk (by simpa using charge_mul q k 0 A N hA hN)
  have hd := primitive_charge q (-k) (Aᴴ*N) (by omega)
    (by simpa using charge_mul q (-k) 0 Aᴴ N (charge_adjoint q k A hA) hN)
  rw [skew,sub_mul,primitive_sub,ha,hd]
  simp only [Int.cast_neg,mul_neg,inv_neg,neg_smul,add_mul,smul_add]
  abel

def quadraticPrimitive (hbar : ℝ) (A B C D Z : M) : M :=
  (-Complex.I*(hbar/4:ℝ)) •
    ((A*A-Aᴴ*Aᴴ)+(B*B-Bᴴ*Bᴴ)+(C*C-Cᴴ*Cᴴ)+(D*D-Dᴴ*Dᴴ)+
      skew Z*(C+Cᴴ+D+Dᴴ)+(C+Cᴴ+D+Dᴴ)*skew Z)

theorem spinSource_primitive (q : n → ℤ) (hbar : ℝ) (A B C D Z : M)
    (hA : HasCharge q (-1) A) (hB : HasCharge q 1 B)
    (hC : HasCharge q (-1) C) (hD : HasCharge q 1 D) (hZ : HasCharge q 0 Z) :
    primitive q (spinSource hbar A B C D Z) = quadraticPrimitive hbar A B C D Z := by
  have hN : HasCharge q 0 (skew Z) :=
    charge_sub q 0 Z Zᴴ hZ (by simpa using charge_adjoint q 0 Z hZ)
  have he : current (momentumPair C D-Complex.I • skew Z) (gradientPair C D) =
      current (momentumPair C D) (gradientPair C D) +
        (-1/2:ℂ) • (skew Z*skew C-skew Z*skew D+skew C*skew Z-skew D*skew Z) := by
    simp only [current,momentumPair,gradientPair,smul_mul_assoc,mul_smul_comm,smul_smul,
      mul_sub,sub_mul,mul_add,add_mul]
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  rw [spinSource,primitive_smul,primitive_add,he,primitive_add,primitive_smul,
    primitive_pair q A B hA hB,primitive_pair q C D hC hD,
    primitive_sub,primitive_add,primitive_sub,
    primitive_neutral_left q (-1) _ C hN hC (by norm_num),
    primitive_neutral_left q 1 _ D hN hD (by norm_num),
    primitive_neutral_right q (-1) _ C hN hC (by norm_num),
    primitive_neutral_right q 1 _ D hN hD (by norm_num)]
  simp only [Int.cast_neg,Int.cast_one,mul_neg,mul_one,inv_neg,Complex.inv_I,neg_neg,
    quadraticPrimitive,mul_add,add_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  module

theorem actual_source_primitive (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    primitive charge (source R r hbar) = quadraticPrimitive hbar
      (ladder r 1) (ladder r 2) (ladder r 3) (ladder r 4) (ladder r 5) := by
  exact spinSource_primitive charge hbar _ _ _ _ _
    (by simpa [flavorCharge] using ladder_charge (R := R) r 1)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 2)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 3)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 4)
    (by simpa [flavorCharge] using ladder_charge (R := R) r 5)

#print axioms primitive_charge
#print axioms primitive_skew_square
#print axioms primitive_pair
#print axioms primitive_neutral_left
#print axioms primitive_neutral_right
#print axioms spinSource_primitive
#print axioms actual_source_primitive

end
end UnifiedTheory.Audit.KFCausalQuadraticSourcePrimitive
