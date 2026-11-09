/- Finite remainder for the actual Gamma quotient with shape 3/2.
The coefficient convolution, Gamma moment errors, factorial growth, and
positive denominator bound are all proved in the imported chain. The result
is a scalar integral estimate; a Wilson Haar/staple dictionary and control
of evolved interacting source correlations are separate obligations. -/
import UnifiedTheory.Clay.YangMills.SqrtSourceRemainder
import UnifiedTheory.Clay.YangMills.SU2SourceCoefficients
import UnifiedTheory.Clay.YangMills.OptimalSourceTruncation
import UnifiedTheory.Clay.YangMills.FiniteSourceConvolution
import UnifiedTheory.Clay.YangMills.SU2SourceQuotient
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2QuotientRemainder
noncomputable section
open Finset

/-- The exact rising Gamma moment for shape `3/2`. -/
def moment (n : ℕ) : ℝ := ∏ i ∈ range n, ((3 / 2 : ℝ) + (i : ℝ))
/-- Actual normalized Gamma denominator, including its cutoff. -/
def denominator (κ : ℝ) : ℝ :=
  SqrtSourceRemainder.gammaAverage (3 / 2) (SqrtSourceRemainder.cutoffSqrt κ)
/-- Actual normalized first-moment Gamma numerator. -/
def numerator (κ : ℝ) : ℝ :=
  SqrtSourceRemainder.gammaAverage (3 / 2) (fun u => u * SqrtSourceRemainder.cutoffSqrt κ u)
def denominatorTruncation (N : ℕ) (κ : ℝ) : ℝ :=
  ∑ i ∈ range N, SqrtSourceRemainder.coefficient i * moment i / (2 * κ)^i
def numeratorTruncation (N : ℕ) (κ : ℝ) : ℝ :=
  ∑ i ∈ range N, SqrtSourceRemainder.coefficient i * moment (i + 1) / (2 * κ)^i
def sourceTruncation (N : ℕ) (κ : ℝ) : ℝ :=
  ∑ i ∈ range N, SU2SourceCoefficients.coefficient i / κ^i
/-- The normalized scalar source ratio; no asymptotic replacement is used. -/
def sourceRatio (κ : ℝ) : ℝ := numerator κ / denominator κ

theorem moment_nonneg (n : ℕ) : 0 ≤ moment n := by
  unfold moment
  positivity

theorem moment_succ (n : ℕ) : moment (n + 1) = moment n * ((3 / 2 : ℝ) + n) :=
  prod_range_succ _ _

theorem moment_le_factorial (n : ℕ) : moment n ≤ ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => norm_num [moment]
  | succ n ih =>
    rw [moment_succ, Nat.factorial_succ (n + 1), Nat.cast_mul]
    calc
      _ ≤ ((n + 1).factorial : ℝ) * ((3 / 2 : ℝ) + n) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ _ := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ (n + 1).factorial by positivity]

theorem denominator_remainder {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    |denominator κ-denominatorTruncation N κ| ≤ 2 * moment N / (2 * κ)^N :=
  SqrtSourceRemainder.su2_denominator_expansion hκ N

theorem numerator_remainder {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    |numerator κ-numeratorTruncation N κ| ≤ 2 * moment (N + 1) / (2 * κ)^N := by
  simpa only [Nat.add_comm] using SqrtSourceRemainder.su2_numerator_expansion hκ N

theorem denominator_ge_half {κ : ℝ} (hκ : 3 / 2 ≤ κ) : 1 / 2 ≤ denominator κ :=
  SqrtSourceRemainder.su2_denominator_ge_half hκ

theorem scaled_coefficient_bound (i : ℕ) (hi : 1 ≤ i) :
    |SU2SourceCoefficients.coefficient i| * (2 : ℝ)^i ≤ ((i + 1).factorial : ℝ) / 2 := by
  have h := mul_le_mul_of_nonneg_right
    (SU2SourceCoefficients.abs_coefficient_le_factorial i hi)
    (show 0 ≤ (2 : ℝ)^i by positivity)
  calc
    _ ≤ (((i + 1).factorial : ℝ) / (2 : ℝ)^(i + 1)) * (2 : ℝ)^i := h
    _ = _ := by rw [pow_succ]; field_simp

/-- Zeroth coefficient, positive-index convolution, and numerator moment
are bounded together with their full combinatorial prefactor. -/
theorem weighted_moment_sum_bound (N : ℕ) (hN : 1 ≤ N) :
    (∑ i ∈ range N, |SU2SourceCoefficients.coefficient i| * (2 : ℝ)^i * moment (N-i)) + 
      moment (N + 1) ≤ ((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hterm (i : ℕ) (hi : i ∈ range k) :
      |SU2SourceCoefficients.coefficient (i + 1)| * (2 : ℝ)^(i + 1) * moment (k + 1-(i + 1)) ≤
        (((i + 2).factorial : ℝ) * ((k-i + 1).factorial : ℝ)) / 2 := by
    have hmi : k + 1-(i + 1) = k-i := by omega
    rw [hmi]
    calc
      _ ≤ (((i + 2).factorial : ℝ) / 2) * moment (k-i) :=
        mul_le_mul_of_nonneg_right (scaled_coefficient_bound (i + 1) (by omega))
          (moment_nonneg _)
      _ ≤ (((i + 2).factorial : ℝ) / 2) * ((k-i + 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left (moment_le_factorial _) (by positivity)
      _ = _ := by ring
  have hconv : (∑ i ∈ range k,
      ((i + 2).factorial : ℝ) * ((k-i + 1).factorial : ℝ)) ≤ 2 * ((k + 2).factorial : ℝ) := by
    have h := SU2SourceCoefficients.factorial_convolution_fin k
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      Nat.factorial (i + 2) * Nat.factorial (k-i + 1)) k] at h
    exact_mod_cast h
  have hsum : (∑ i ∈ range k,
      |SU2SourceCoefficients.coefficient (i + 1)| * (2 : ℝ)^(i + 1) * moment (k + 1-(i + 1))) ≤
        ((k + 2).factorial : ℝ) := by
    calc
      _ ≤ ∑ i ∈ range k, (((i + 2).factorial : ℝ) * ((k-i + 1).factorial : ℝ)) / 2 :=
        sum_le_sum hterm
      _ = (∑ i ∈ range k, ((i + 2).factorial : ℝ) * ((k-i + 1).factorial : ℝ)) / 2 :=
        (sum_div _ _ _).symm
      _ ≤ _ := by linarith
  rw [sum_range_succ']
  have h0 := moment_le_factorial (k + 1)
  have hn := moment_le_factorial (k + 2)
  rw [Nat.factorial_succ (k + 2), Nat.cast_mul] at hn
  simp only [SU2SourceCoefficients.coefficient_zero, abs_of_pos (by norm_num : (0 : ℝ)<3 / 2),
    pow_zero, mul_one, Nat.sub_zero, Nat.cast_add, Nat.cast_one] at * 
  push_cast at hn
  simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] at * 
  push_cast
  simp only [Nat.add_sub_add_right] at hsum
  nlinarith

theorem scaled_denominator_remainder {κ : ℝ} (hκ : 0 < κ)
    (N i : ℕ) (hi : i ≤ N) :
    |(SU2SourceCoefficients.coefficient i / κ^i) * 
      (denominator κ-denominatorTruncation (N-i) κ)| ≤
      (2 / (2 * κ)^N) * (|SU2SourceCoefficients.coefficient i| * (2 : ℝ)^i * moment (N-i)) := by
  rw [abs_mul, abs_div, abs_of_pos (pow_pos hκ i)]
  calc
    _ ≤ (|SU2SourceCoefficients.coefficient i| / κ^i) * 
        (2 * moment (N-i) / (2 * κ)^(N-i)) :=
      mul_le_mul_of_nonneg_left (denominator_remainder hκ (N-i)) (by positivity)
    _ = _ := by
      have he : i + (N-i) = N := Nat.add_sub_of_le hi
      have hp : (2 * κ)^N = (2 * κ)^i * (2 * κ)^(N-i) := by
        rw [← pow_add, he]
      rw [hp, mul_pow]
      field_simp
      ring

theorem denominatorTruncation_eq (N : ℕ) (κ : ℝ) :
    denominatorTruncation N κ =
      ∑ i ∈ range N, SU2SourceQuotient.denominatorCoefficient i * (κ⁻¹)^i := by
  unfold denominatorTruncation SU2SourceQuotient.denominatorCoefficient moment
  apply sum_congr rfl
  intro i _
  rw [inv_pow, mul_pow]
  ring

theorem numeratorTruncation_eq (N : ℕ) (κ : ℝ) :
    numeratorTruncation N κ =
      ∑ i ∈ range N, SU2SourceQuotient.numeratorCoefficient i * (κ⁻¹)^i := by
  unfold numeratorTruncation SU2SourceQuotient.numeratorCoefficient
    SU2SourceQuotient.denominatorCoefficient
  apply sum_congr rfl
  intro i _
  rw [moment_succ, inv_pow, mul_pow]
  unfold moment
  ring

/-- Exact finite cancellation follows from the proved quotient convolution.
No infinite asymptotic series is summed. -/
theorem remainder_identity (N : ℕ) (κ : ℝ) :
    denominator κ * sourceTruncation N κ-numerator κ =
      (∑ i ∈ range N, (SU2SourceCoefficients.coefficient i / κ^i) * 
        (denominator κ-denominatorTruncation (N-i) κ)) + 
      (numeratorTruncation N κ-numerator κ) := by
  have h := FiniteSourceConvolution.shifted_remainder_identity
    SU2SourceCoefficients.coefficient SU2SourceQuotient.denominatorCoefficient
    SU2SourceQuotient.numeratorCoefficient SU2SourceQuotient.coefficient_convolution
    N (κ⁻¹) (denominator κ) (numerator κ)
  simp_rw [← denominatorTruncation_eq, ← numeratorTruncation_eq] at h
  simp only [inv_pow, ← div_eq_mul_inv] at h
  exact h

/-- The unnormalized quotient residual combines the two actual Gamma errors. -/
theorem scalar_remainder {κ : ℝ} (hκ : 0 < κ)
    (N : ℕ) (hN : 1 ≤ N) :
    |denominator κ * sourceTruncation N κ-numerator κ| ≤
      2 * ((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ) / (2 * κ)^N := by
  rw [remainder_identity]
  calc
    _ ≤ |∑ i ∈ range N, (SU2SourceCoefficients.coefficient i / κ^i) * 
        (denominator κ-denominatorTruncation (N-i) κ)| + 
        |numeratorTruncation N κ-numerator κ| := abs_add_le _ _
    _ ≤ (∑ i ∈ range N, |(SU2SourceCoefficients.coefficient i / κ^i) * 
        (denominator κ-denominatorTruncation (N-i) κ)|) + 
        2 * moment (N + 1) / (2 * κ)^N := by
      apply add_le_add (abs_sum_le_sum_abs _ _)
      rw [abs_sub_comm]
      exact numerator_remainder hκ N
    _ ≤ (∑ i ∈ range N, (2 / (2 * κ)^N) * 
        (|SU2SourceCoefficients.coefficient i| * (2 : ℝ)^i * moment (N-i))) + 
        2 * moment (N + 1) / (2 * κ)^N := by
      apply add_le_add _ le_rfl
      exact sum_le_sum (fun i hi => scaled_denominator_remainder hκ N i
        (mem_range.mp hi).le)
    _ = (2 / (2 * κ)^N) * ((∑ i ∈ range N,
        |SU2SourceCoefficients.coefficient i| * (2 : ℝ)^i * moment (N-i)) + moment (N + 1)) := by
      rw [← mul_sum]
      ring
    _ ≤ (2 / (2 * κ)^N) * (((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (weighted_moment_sum_bound N hN) (by positivity)
    _ = _ := by ring

/-- Actual normalized quotient remainder. The denominator lower bound
is proved from its cutoff integrand, rather than assumed here. -/
theorem quotient_remainder {κ : ℝ} (hκ : 3 / 2 ≤ κ)
    (N : ℕ) (hN : 1 ≤ N) :
    |sourceRatio κ-sourceTruncation N κ| ≤
      6 * ((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ) / (2 * κ)^N := by
  have hp : 0 < κ := by linarith
  have hd := denominator_ge_half hκ
  have hdpos : 0 < denominator κ := by linarith
  have he : sourceRatio κ-sourceTruncation N κ =
      -(denominator κ * sourceTruncation N κ-numerator κ) / denominator κ := by
    unfold sourceRatio
    field_simp
    ring
  rw [he, abs_div, abs_neg, abs_of_pos hdpos]
  apply (div_le_iff₀ hdpos).2
  have h := scalar_remainder hp N hN
  let R : ℝ := ((N : ℝ) + 9 / 2) * ((N + 1).factorial : ℝ) / (2 * κ)^N
  have hc : 0 ≤ R := by dsimp [R]; positivity
  have hm := mul_le_mul_of_nonneg_left hd hc
  calc
    _ ≤ 2 * R := by convert h using 1; dsimp [R]; ring
    _ ≤ 6 * R * denominator κ := by nlinarith
    _ = _ := by dsimp [R]; ring

/-- A single truncation index gives exponential accuracy uniformly on the
whole good region `κ ≥ κ₀`. -/
theorem optimal_quotient_remainder (κ₀ κ : ℝ) (hκ₀ : 3 / 2 ≤ κ₀) (hκ : κ₀ ≤ κ) :
    |sourceRatio κ-sourceTruncation ⌊2 * κ₀⌋₊ κ| ≤
      6 * Real.exp 2 * (2 * κ₀) * (2 * κ₀ + 1) * (2 * κ₀ + 9 / 2) * Real.exp (-2 * κ₀) := by
  have hN : 1 ≤ ⌊2 * κ₀⌋₊ := Nat.le_floor (by norm_num; linarith)
  exact (quotient_remainder (hκ₀.trans hκ) _ hN).trans
    (OptimalSourceTruncation.optimal_remainder_bound κ₀ κ hκ₀ hκ)

end
end UnifiedTheory.Clay.YangMills.SU2QuotientRemainder
