/- Exact formal quotient coefficients for the cutoff Gamma source integrals.
The denominator coefficients are derived from the proved square-root binomial
coefficients and exact Gamma moments. The quotient identity is finite coefficient
algebra; no convergence of an infinite inverse-coupling series is asserted.
The separate SU(2) Haar-coordinate identification is not asserted here. -/
import UnifiedTheory.Clay.YangMills.SU2SourceCoefficients
import UnifiedTheory.Clay.YangMills.SqrtSourceRemainder
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2SourceQuotient
noncomputable section
open scoped BigOperators PowerSeries
open PowerSeries

/-- Denominator coefficients obtained from the actual binomial and Gamma moments. -/
def denominatorCoefficient (n : ℕ) : ℝ :=
  SqrtSourceRemainder.coefficient n * (∏ i ∈ Finset.range n, (3 / 2 + (i : ℝ))) / 2 ^ n

/-- The numerator includes one additional Gamma moment. -/
def numeratorCoefficient (n : ℕ) : ℝ :=
  (3 / 2 + (n : ℝ)) * denominatorCoefficient n

@[simp] theorem denominatorCoefficient_zero : denominatorCoefficient 0 = 1 := by
  simp [denominatorCoefficient]

@[simp] theorem denominatorCoefficient_one : denominatorCoefficient 1 = -3 / 8 := by
  norm_num [denominatorCoefficient]

/-- Explicit Gamma normalization, without an assumed coefficient identification. -/
theorem denominatorCoefficient_eq_gamma (n : ℕ) :
    denominatorCoefficient n = SqrtSourceRemainder.coefficient n *
      Real.Gamma (3 / 2 + (n : ℝ)) / (2 ^ n * Real.Gamma (3 / 2)) := by
  rw [SqrtSourceRemainder.gamma_shift_eq_product (by norm_num : (0 : ℝ) < 3 / 2)]
  unfold denominatorCoefficient
  field_simp [(Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne']

/-- The numerator coefficient uses the original Gamma normalizer and one extra moment. -/
theorem numeratorCoefficient_eq_gamma (n : ℕ) :
    numeratorCoefficient n = SqrtSourceRemainder.coefficient n *
      Real.Gamma ((3 / 2 + 1) + (n : ℝ)) / (2 ^ n * Real.Gamma (3 / 2)) := by
  have he : (3 / 2 + 1) + (n : ℝ) = (3 / 2 + (n : ℝ)) + 1 := by ring
  rw [he, Real.Gamma_add_one (by positivity : (3 / 2 + (n : ℝ)) ≠ 0)]
  unfold numeratorCoefficient
  rw [denominatorCoefficient_eq_gamma]
  ring

/-- The exact linear recurrence of the denominator coefficients. -/
theorem denominatorCoefficient_recurrence (n : ℕ) :
    2 * ((n : ℝ) + 1) * denominatorCoefficient (n + 1) =
      ((n : ℝ) * ((n : ℝ) + 1) - 3 / 4) * denominatorCoefficient n := by
  have ha := SqrtSourceRemainder.coefficient_recurrence n
  unfold denominatorCoefficient
  rw [Finset.prod_range_succ, pow_succ]
  field_simp
  linear_combination (8 * ((n : ℝ) + 3 / 2)) * ha

/-- Formal denominator series; no nonzero-radius convergence is asserted. -/
def denominatorSeries : PowerSeries ℝ := PowerSeries.mk denominatorCoefficient

@[simp] theorem denominatorSeries_coeff (n : ℕ) :
    coeff n denominatorSeries = denominatorCoefficient n := coeff_mk _ _

@[simp] theorem denominatorSeries_constant : constantCoeff denominatorSeries = 1 := by
  simpa only [← coeff_zero_eq_constantCoeff_apply, denominatorCoefficient_zero] using
    denominatorSeries_coeff 0

/-- Twice the logarithmic-derivative quotient, avoiding division by the formal variable. -/
def doubledQuotient (D : PowerSeries ℝ) : PowerSeries ℝ :=
  3 + 2 * X * derivative ℝ D * D⁻¹

/-- The linear denominator equation implies the quadratic quotient equation. -/
theorem doubledQuotient_riccati (D : PowerSeries ℝ)
    (hD : constantCoeff D = 1)
    (hode : 4 * X ^ 2 * derivative ℝ (derivative ℝ D) +
      (8 * X - 8) * derivative ℝ D - 3 * D = 0) :
    2 * X ^ 2 * derivative ℝ (doubledQuotient D) +
      X * (doubledQuotient D) ^ 2 - 4 * X * doubledQuotient D + 12 -
        4 * doubledQuotient D = 0 := by
  have hinv : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel D (by rw [hD]; norm_num)
  have htwo : derivative ℝ (2 : PowerSeries ℝ) = 0 :=
    (derivative ℝ).map_natCast 2
  have hthree : derivative ℝ (3 : PowerSeries ℝ) = 0 :=
    (derivative ℝ).map_natCast 3
  have hder : derivative ℝ (doubledQuotient D) =
      2 * derivative ℝ D * D⁻¹ + 2 * X * derivative ℝ (derivative ℝ D) * D⁻¹ -
        2 * X * (derivative ℝ D) ^ 2 * (D⁻¹) ^ 2 := by
    simp only [doubledQuotient, map_add, Derivation.leibniz, htwo, hthree, derivative_X,
      derivative_inv', smul_eq_mul]
    ring
  rw [hder]
  calc
    _ = X * D⁻¹ * (4 * X ^ 2 * derivative ℝ (derivative ℝ D) +
          (8 * X - 8) * derivative ℝ D - 3 * D) + 3 * X * (D * D⁻¹ - 1) := by
      unfold doubledQuotient
      ring
    _ = 0 := by rw [hode, hinv]; ring

/-- The constant coefficient of the actual formal quotient is forced. -/
theorem doubledQuotient_zero (D : PowerSeries ℝ) :
    coeff 0 (doubledQuotient D) = 3 := by
  simp [doubledQuotient, coeff_zero_eq_constantCoeff, ← map_ofNat C]

/-- Split the two boundary terms from the coefficient of a square. -/
theorem coeff_square_interior (R : PowerSeries ℝ) (n : ℕ) :
    coeff (n + 1) (R * R) = 2 * coeff 0 R * coeff (n + 1) R +
      ∑ i : Fin n, coeff (i.val + 1) R * coeff (n - i.val) R := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i R * coeff j R) (n + 1)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [Fin.sum_univ_eq_sum_range (fun i => coeff (i + 1) R * coeff (n - i) R) n]
  have hs : (∑ i ∈ Finset.range n, coeff (i + 1) R * coeff (n + 1 - (i + 1)) R) =
      ∑ i ∈ Finset.range n, coeff (i + 1) R * coeff (n - i) R := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_sub_add_right]
  rw [hs]
  ring

/-- Positive-degree coefficients of the doubled quotient equation. -/
theorem doubled_riccati_recurrence (R : PowerSeries ℝ) (hzero : coeff 0 R = 3)
    (h : 2 * X ^ 2 * derivative ℝ R + X * R ^ 2 - 4 * X * R + 12 - 4 * R = 0) (n : ℕ) :
    4 * coeff (n + 2) R = (2 * (n : ℝ) + 4) * coeff (n + 1) R +
      ∑ i : Fin n, coeff (i.val + 1) R * coeff (n - i.val) R := by
  have he : 2 * (X * (X * derivative ℝ R)) + X * (R * R) - 4 * (X * R) + 12 - 4 * R = 0 := by
    convert h using 1
    ring
  have hc := congrArg (coeff (n + 2)) he
  simp only [map_add, map_sub, map_zero, ← map_ofNat C, coeff_C_mul,
    coeff_succ_X_mul, coeff_derivative, coeff_C] at hc
  rw [if_neg (by omega : n + 2 ≠ 0), coeff_square_interior, hzero] at hc
  linarith

/-- The first coefficient is also forced by the equation. -/
theorem doubled_riccati_one (R : PowerSeries ℝ) (hzero : coeff 0 R = 3)
    (h : 2 * X ^ 2 * derivative ℝ R + X * R ^ 2 - 4 * X * R + 12 - 4 * R = 0) :
    coeff 1 R = -3 / 4 := by
  have he : 2 * (X * (X * derivative ℝ R)) + X * (R * R) - 4 * (X * R) + 12 - 4 * R = 0 := by
    convert h using 1
    ring
  have hc := congrArg (coeff 1) he
  simp only [map_add, map_sub, map_zero, ← map_ofNat C, coeff_C_mul, coeff_C,
    coeff_succ_X_mul, coeff_zero_X_mul, coeff_zero_eq_constantCoeff,
    map_mul] at hc
  rw [← coeff_zero_eq_constantCoeff_apply R, hzero] at hc
  norm_num at hc
  linarith

/-- Identification with the unique factorial-bounded Riccati sequence. -/
theorem doubledQuotient_coeff (D : PowerSeries ℝ)
    (hD : constantCoeff D = 1)
    (hode : 4 * X ^ 2 * derivative ℝ (derivative ℝ D) +
      (8 * X - 8) * derivative ℝ D - 3 * D = 0) (n : ℕ) :
    coeff n (doubledQuotient D) = 2 * SU2SourceCoefficients.coefficient n := by
  have hr := doubledQuotient_riccati D hD hode
  have hz := doubledQuotient_zero D
  have ho := doubled_riccati_one _ hz hr
  have hu : (fun i => coeff i (doubledQuotient D) / 2) =
      SU2SourceCoefficients.coefficient := by
    apply SU2SourceCoefficients.coefficient_unique
    · rw [hz]
    · rw [ho]; norm_num
    · intro k
      have h := doubled_riccati_recurrence _ hz hr k
      have hsum : (∑ i : Fin k,
          (coeff (i.val + 1) (doubledQuotient D) / 2) *
            (coeff (k - i.val) (doubledQuotient D) / 2)) =
          (∑ i : Fin k,
            coeff (i.val + 1) (doubledQuotient D) * coeff (k - i.val) (doubledQuotient D)) / 4 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      push_cast
      linarith
  have hn := congrFun hu n
  linarith

/-- Euler differentiation multiplies the nth coefficient by n. -/
theorem coeff_X_derivative (F : PowerSeries ℝ) (n : ℕ) :
    coeff n (X * derivative ℝ F) = (n : ℝ) * coeff n F := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The explicit Gamma denominator satisfies its formal differential equation. -/
theorem denominatorSeries_ode :
    4 * X ^ 2 * derivative ℝ (derivative ℝ denominatorSeries) +
      (8 * X - 8) * derivative ℝ denominatorSeries - 3 * denominatorSeries = 0 := by
  have he : 4 * X ^ 2 * derivative ℝ (derivative ℝ denominatorSeries) +
      (8 * X - 8) * derivative ℝ denominatorSeries - 3 * denominatorSeries =
      4 * (X * (X * derivative ℝ (derivative ℝ denominatorSeries))) +
        8 * (X * derivative ℝ denominatorSeries) -
          8 * derivative ℝ denominatorSeries - 3 * denominatorSeries := by ring
  rw [he]
  ext n
  cases n with
  | zero =>
    simp only [map_add, map_sub, map_zero, ← map_ofNat C, coeff_C_mul,
      coeff_zero_X_mul, coeff_derivative, denominatorSeries_coeff]
    norm_num
  | succ n =>
    simp only [map_add, map_sub, map_zero, ← map_ofNat C, coeff_C_mul,
      coeff_succ_X_mul, coeff_X_derivative, coeff_derivative, denominatorSeries_coeff]
    have h := denominatorCoefficient_recurrence (n + 1)
    push_cast at h ⊢
    linear_combination - 4 * h

/-- Exact finite coefficient convolution for the Gamma numerator and denominator.
This identifies the Riccati sequence with the formal quotient; no analytic
convergence of an infinite inverse-coupling expansion is asserted. -/
theorem coefficient_convolution (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      SU2SourceCoefficients.coefficient i * denominatorCoefficient (n - i)) =
        numeratorCoefficient n := by
  have hinv : denominatorSeries⁻¹ * denominatorSeries = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [denominatorSeries_constant]; norm_num)
  have hp : doubledQuotient denominatorSeries * denominatorSeries =
      3 * denominatorSeries + 2 * (X * derivative ℝ denominatorSeries) := by
    unfold doubledQuotient
    calc
      _ = 3 * denominatorSeries +
          2 * (X * derivative ℝ denominatorSeries) * (denominatorSeries⁻¹ * denominatorSeries) := by
        ring
      _ = _ := by rw [hinv]; ring
  have hc := congrArg (coeff n) hp
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (doubledQuotient denominatorSeries) * coeff j denominatorSeries) n] at hc
  simp only [map_add, ← map_ofNat C, coeff_C_mul, coeff_X_derivative,
    denominatorSeries_coeff] at hc
  simp_rw [doubledQuotient_coeff denominatorSeries denominatorSeries_constant
    denominatorSeries_ode, mul_assoc] at hc
  rw [← Finset.mul_sum] at hc
  unfold numeratorCoefficient
  linarith

end
end UnifiedTheory.Clay.YangMills.SU2SourceQuotient
