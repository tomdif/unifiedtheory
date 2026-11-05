/- Coefficients of the formal SU(2) conditional-source expansion.
The recurrence and its factorial bound are proved algebraically. No
convergence of an infinite inverse-coupling series or identification with a
Haar integral is assumed here. The factorial bound starts at index one. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2SourceCoefficients
noncomputable section
open scoped BigOperators

/-- Exact formal Riccati coefficients. In the last clause the sum runs
over the original indices 1,...,n. -/
def coefficient : ℕ → ℝ
  | 0 => 3/2
  | 1 => -3/8
  | n+2 => (((n+2 : ℕ) : ℝ)*coefficient (n+1)+
      ∑ i : Fin n, coefficient (i.val+1)*coefficient (n-i.val))/2
termination_by n => n
decreasing_by all_goals omega

theorem coefficient_zero : coefficient 0 = 3/2 := by rw [coefficient]
theorem coefficient_one : coefficient 1 = -3/8 := by rw [coefficient]
theorem coefficient_two : coefficient 2 = -3/8 := by
  norm_num [coefficient, Fin.sum_univ_succ]
theorem coefficient_three : coefficient 3 = -63/128 := by
  norm_num [coefficient, Fin.sum_univ_succ]
theorem coefficient_four : coefficient 4 = -27/32 := by
  norm_num [coefficient, Fin.sum_univ_succ]

theorem coefficient_recurrence (n : ℕ) :
    2*coefficient (n+2) = ((n+2 : ℕ) : ℝ)*coefficient (n+1)+
      ∑ i : Fin n, coefficient (i.val+1)*coefficient (n-i.val) := by
  rw [coefficient]
  ring

/-- An elementary factorial-product estimate replacing binomial
unimodality: move one factor at a time into the larger factorial. -/
theorem factorial_product_le (s t : ℕ) :
    Nat.factorial (s+2)*Nat.factorial (t+2) ≤ 2*Nat.factorial (s+t+2) := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc
      Nat.factorial (s+1+2)*Nat.factorial (t+2) =
          (s+3)*(Nat.factorial (s+2)*Nat.factorial (t+2)) := by
        rw [show s+1+2 = (s+2)+1 by omega, Nat.factorial_succ]
        ring
      _ ≤ (s+3)*(2*Nat.factorial (s+t+2)) := Nat.mul_le_mul_left _ ih
      _ ≤ (s+t+3)*(2*Nat.factorial (s+t+2)) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 2*Nat.factorial (s+1+t+2) := by
        rw [show s+1+t+2 = (s+t+2)+1 by omega, Nat.factorial_succ (s+t+2)]
        ring

/-- The full factorial convolution is bounded, including its number of
terms; no convolution estimate is supplied as an assumption. -/
theorem factorial_convolution_fin (n : ℕ) :
    (∑ i : Fin n, Nat.factorial (i.val+2)*Nat.factorial (n-i.val+1)) ≤
      2*Nat.factorial (n+2) := by
  have hp (i : Fin n) : Nat.factorial (i.val+2)*Nat.factorial (n-i.val+1) ≤
      2*Nat.factorial (n+1) := by
    have h1 : n-i.val+1 = (n-i.val-1)+2 := by omega
    have h2 : i.val+(n-i.val-1)+2 = n+1 := by omega
    rw [h1]
    simpa only [h2] using factorial_product_le i.val (n-i.val-1)
  calc
    _ ≤ ∑ _i : Fin n, 2*Nat.factorial (n+1) := Finset.sum_le_sum (fun i _ => hp i)
    _ = n*(2*Nat.factorial (n+1)) := by simp
    _ ≤ (n+2)*(2*Nat.factorial (n+1)) := Nat.mul_le_mul_right _ (by omega)
    _ = 2*Nat.factorial (n+2) := by rw [Nat.factorial_succ (n+1)]; ring

/-- Uniform factorial growth of every positive-index coefficient. Index
zero is deliberately excluded: its value 3/2 violates this bound. -/
theorem abs_coefficient_le_factorial (n : ℕ) (hn : 1 ≤ n) :
    |coefficient n| ≤ (Nat.factorial (n+1) : ℝ)/(2 : ℝ)^(n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · omega
    rcases n with _ | k
    · norm_num [coefficient]
    change |coefficient (k+2)| ≤ (Nat.factorial (k+3) : ℝ)/(2 : ℝ)^(k+3)
    have hlin := ih (k+1) (by omega) (by omega)
    have hterm (i : Fin k) :
        |coefficient (i.val+1)*coefficient (k-i.val)| ≤
          ((Nat.factorial (i.val+2) : ℝ)*(Nat.factorial (k-i.val+1) : ℝ)) /
            (2 : ℝ)^(k+3) := by
      have hleft := ih (i.val+1) (by omega) (by omega)
      have hright := ih (k-i.val) (by omega) (by omega)
      calc
        _ = |coefficient (i.val+1)| *|coefficient (k-i.val)| := abs_mul _ _
        _ ≤ ((Nat.factorial (i.val+2) : ℝ)/(2 : ℝ)^(i.val+2))*
            ((Nat.factorial (k-i.val+1) : ℝ)/(2 : ℝ)^(k-i.val+1)) :=
          mul_le_mul hleft hright (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [div_mul_div_comm, ← pow_add]
          have he : (i.val+2)+(k-i.val+1) = k+3 := by omega
          rw [he]
    have hconv : (∑ i : Fin k,
        (Nat.factorial (i.val+2) : ℝ)*(Nat.factorial (k-i.val+1) : ℝ)) ≤
        2*(Nat.factorial (k+2) : ℝ) := by
      exact_mod_cast factorial_convolution_fin k
    have hsum : (∑ i : Fin k, |coefficient (i.val+1)*coefficient (k-i.val)|) ≤
        (2*(Nat.factorial (k+2) : ℝ))/(2 : ℝ)^(k+3) := by
      calc
        _ ≤ ∑ i : Fin k,
            ((Nat.factorial (i.val+2) : ℝ)*(Nat.factorial (k-i.val+1) : ℝ)) /
              (2 : ℝ)^(k+3) := Finset.sum_le_sum (fun i _ => hterm i)
        _ = (∑ i : Fin k,
            (Nat.factorial (i.val+2) : ℝ)*(Nat.factorial (k-i.val+1) : ℝ)) /
              (2 : ℝ)^(k+3) := (Finset.sum_div _ _ _).symm
        _ ≤ _ := div_le_div_of_nonneg_right hconv (by positivity)
    have hab : |((k+2 : ℕ) : ℝ)*coefficient (k+1)+
        ∑ i : Fin k, coefficient (i.val+1)*coefficient (k-i.val)| ≤
        ((k+2 : ℕ) : ℝ)*|coefficient (k+1)|+
          ∑ i : Fin k, |coefficient (i.val+1)*coefficient (k-i.val)| := by
      calc
        _ ≤ |((k+2 : ℕ) : ℝ)*coefficient (k+1)|+
            |∑ i : Fin k, coefficient (i.val+1)*coefficient (k-i.val)| := abs_add_le _ _
        _ ≤ _ := add_le_add (by rw [abs_mul, abs_of_nonneg (by positivity)])
          (Finset.abs_sum_le_sum_abs _ _)
    calc
      |coefficient (k+2)| ≤
          (((k+2 : ℕ) : ℝ)*((Nat.factorial (k+2) : ℝ)/(2 : ℝ)^(k+2))+
            (2*(Nat.factorial (k+2) : ℝ))/(2 : ℝ)^(k+3))/2 := by
        rw [coefficient, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact hab.trans (add_le_add (mul_le_mul_of_nonneg_left hlin (by positivity)) hsum)
      _ = (Nat.factorial (k+3) : ℝ)/(2 : ℝ)^(k+3) := by
        rw [Nat.factorial_succ (k+2), Nat.cast_mul]
        simp only [Nat.cast_add, Nat.cast_ofNat, pow_succ]
        field_simp
        ring

/-- Reindex a finite sum by the positive integer interval. -/
theorem sum_fin_shift {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    (∑ i : Fin n, f (i.val+1)) = ∑ i ∈ Finset.Icc 1 n, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i+1)) n,
    ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

/-- The convolution estimate in the original positive-index notation. -/
theorem factorial_convolution (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 (n-1), Nat.factorial (i+1)*Nat.factorial (n-i+1)) ≤
      2*Nat.factorial (n+1) := by
  rcases n with _ | k
  · omega
  have heq : (∑ i : Fin k, Nat.factorial (i.val+2)*Nat.factorial (k-i.val+1)) =
      ∑ i ∈ Finset.Icc 1 k, Nat.factorial (i+1)*Nat.factorial (k+1-i+1) := by
    calc
      _ = ∑ i : Fin k,
          Nat.factorial (i.val+1+1)*Nat.factorial (k+1-(i.val+1)+1) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        omega
      _ = _ := sum_fin_shift k (fun i =>
          Nat.factorial (i+1)*Nat.factorial (k+1-i+1))
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    (heq ▸ factorial_convolution_fin k)

/-- The requested Riccati recurrence with indices 1,...,n-1. -/
theorem coefficient_recurrence_icc (n : ℕ) (hn : 1 ≤ n) :
    2*coefficient (n+1) = ((n+1 : ℕ) : ℝ)*coefficient n+
      ∑ i ∈ Finset.Icc 1 (n-1), coefficient i*coefficient (n-i) := by
  rcases n with _ | k
  · omega
  have heq : (∑ i : Fin k, coefficient (i.val+1)*coefficient (k-i.val)) =
      ∑ i ∈ Finset.Icc 1 k, coefficient i*coefficient (k+1-i) := by
    calc
      _ = ∑ i : Fin k, coefficient (i.val+1)*coefficient (k+1-(i.val+1)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        omega
      _ = _ := sum_fin_shift k (fun i => coefficient i*coefficient (k+1-i))
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, heq] using
    coefficient_recurrence k

/-- These initial values and recurrence determine exactly one sequence. -/
theorem coefficient_unique (q : ℕ → ℝ) (hzero : q 0 = 3 / 2) (hone : q 1 = -3 / 8)
    (hrec : ∀ n, 2 * q (n + 2) = ((n + 2 : ℕ) : ℝ) * q (n + 1) +
      ∑ i : Fin n, q (i.val + 1) * q (n - i.val)) : q = coefficient := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · exact hzero.trans coefficient_zero.symm
    rcases n with _ | k
    · exact hone.trans coefficient_one.symm
    have hsum : (∑ i : Fin k, q (i.val+1)*q (k-i.val)) =
        ∑ i : Fin k, coefficient (i.val+1)*coefficient (k-i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ih (i.val+1) (by omega), ih (k-i.val) (by omega)]
    have h := hrec k
    rw [ih (k+1) (by omega), hsum] at h
    linarith [coefficient_recurrence k]

/-- The coefficient bound in the scaling used for the finite local
operator expansion. The zeroth operator is handled separately. -/
theorem abs_scaled_coefficient_le (j : ℕ) (hj : 1 ≤ j)
    (beta : ℝ) (hbeta : 0 < beta) :
    |coefficient j/((2 : ℝ)^j*beta^(j+1))| ≤
      (Nat.factorial (j+1) : ℝ)/(2*(4 : ℝ)^j*beta^(j+1)) := by
  rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^j*beta^(j+1))]
  calc
    _ ≤ ((Nat.factorial (j+1) : ℝ)/(2 : ℝ)^(j+1))/
        ((2 : ℝ)^j*beta^(j+1)) :=
      div_le_div_of_nonneg_right (abs_coefficient_le_factorial j hj) (by positivity)
    _ = _ := by
      have hfour : (4 : ℝ)^j = (2 : ℝ)^j*(2 : ℝ)^j := by
        rw [show (4 : ℝ) = 2*2 by norm_num, mul_pow]
      rw [hfour, pow_succ]
      field_simp

end
end UnifiedTheory.Clay.YangMills.SU2SourceCoefficients
