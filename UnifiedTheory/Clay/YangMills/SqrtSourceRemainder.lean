/- Elementary square-root source coefficients and finite truncation estimates.
The coefficients are the actual generalized binomial coefficients. No remainder
estimate or continuum source bound is introduced as an assumption. The Gamma
bridge below uses explicit Euler integrals and evaluates their moments. Identifying
a Wilson conditional SU(2) integral with this scalar representation is a separate
geometric step; this module makes no continuum or multiscale claim. -/
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SqrtSourceRemainder
noncomputable section
open Finset Filter
open scoped Topology
open MeasureTheory

/-- The coefficient of `x^n` in the expansion of `sqrt (1-x)`. -/
def coefficient (n : ℕ) : ℝ := (-1) ^ n * Ring.choose (1 / 2 : ℝ) n

/-- The finite polynomial containing degrees strictly less than `N`. -/
def truncation (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ range N, coefficient n * x ^ n

@[simp] theorem coefficient_zero : coefficient 0 = 1 := by
  simp [coefficient]

@[simp] theorem coefficient_one : coefficient 1 = -(1 / 2 : ℝ) := by
  simp [coefficient]

/-- The multiplicative recurrence avoids dividing by a coefficient. -/
theorem coefficient_recurrence (n : ℕ) :
    ((n : ℝ) + 1) * coefficient (n + 1) =
      ((n : ℝ) - 1 / 2) * coefficient n := by
  have h := Ring.choose_smul_choose (1 / 2 : ℝ) (n := n + 1) (k := n)
    (Nat.le_succ n)
  simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
    Ring.choose_one_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  dsimp [coefficient]
  rw [pow_succ]
  nlinarith [congrArg (fun t : ℝ => (-1 : ℝ) ^ n * t) h]

theorem coefficient_nonpos_succ (n : ℕ) : coefficient (n + 1) ≤ 0 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hr := coefficient_recurrence (n + 1)
      have hn : (0 : ℝ) ≤ (n + 1 : ℕ) - 1 / 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        linarith
      have hp : (0 : ℝ) < (n + 1 : ℕ) + 1 := by positivity
      have hm := mul_nonpos_of_nonneg_of_nonpos hn ih
      rw [← hr] at hm
      exact nonpos_of_mul_nonpos_right hm hp

theorem coefficient_nonpos {n : ℕ} (hn : 1 ≤ n) : coefficient n ≤ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact coefficient_nonpos_succ k

/-- Exact telescoping identity for the coefficients at the endpoint `x=1`. -/
theorem sum_coefficient (N : ℕ) :
    (∑ n ∈ range N, coefficient n) = -2 * (N : ℝ) * coefficient N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      have h := coefficient_recurrence N
      push_cast
      nlinarith

theorem sum_coefficient_nonneg (N : ℕ) :
    0 ≤ ∑ n ∈ range N, coefficient n := by
  cases N with
  | zero => simp
  | succ N =>
      rw [sum_coefficient]
      have h := coefficient_nonpos_succ N
      have hn : (0 : ℝ) ≤ (N + 1 : ℕ) := Nat.cast_nonneg _
      nlinarith

/-- All finite initial segments of the absolute coefficient series are bounded. -/
theorem sum_abs_coefficient_le_two (N : ℕ) :
    (∑ n ∈ range N, |coefficient n|) ≤ 2 := by
  cases N with
  | zero => simp
  | succ N =>
      have he : (∑ n ∈ range (N + 1), |coefficient n|) =
          2 - ∑ n ∈ range (N + 1), coefficient n := by
        rw [sum_range_succ', sum_range_succ']
        simp only [coefficient_zero, abs_one]
        have hneg : (∑ n ∈ range N, |coefficient (n + 1)|) =
            -(∑ n ∈ range N, coefficient (n + 1)) := by
          simp_rw [abs_of_nonpos (coefficient_nonpos_succ _), sum_neg_distrib]
        rw [hneg]
        ring
      rw [he]
      linarith [sum_coefficient_nonneg (N + 1)]

theorem coefficient_abs_summable : Summable (fun n => |coefficient n|) :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) sum_abs_coefficient_le_two

/-- The actual binomial series sums to the square root inside its disk. -/
theorem coefficient_hasSum_sqrt {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n => coefficient n * x ^ n) (Real.sqrt (1-x)) := by
  have hy : (-x : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Metric.mem_ball, Real.dist_eq, abs_neg, abs_of_nonneg hx] using hx1
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1/2 : ℝ))).hasSum hy
  convert hs using 1
  · ext n
    simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      coefficient]
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  · simp only [zero_add, sub_eq_add_neg, Real.sqrt_eq_rpow]

theorem sum_abs_coefficient_Ico_le_two (N M : ℕ) :
    (∑ n ∈ Ico N M, |coefficient n|) ≤ 2 := by
  calc
    _ ≤ ∑ n ∈ range M, |coefficient n| := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_range.mpr (mem_Ico.mp hn).2
      · intro n _ _
        exact abs_nonneg _
    _ ≤ 2 := sum_abs_coefficient_le_two M

/-- A finite tail estimate, proved before taking any limit. -/
theorem truncation_tail_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {N M : ℕ} (hNM : N ≤ M) :
    |truncation M x - truncation N x| ≤ 2 * x ^ N := by
  unfold truncation
  rw [sum_range_sub_sum_range hNM]
  have he : (range M).filter (fun n => N ≤ n) = Ico N M := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico, and_comm]
  rw [he]
  calc
    |∑ n ∈ Ico N M, coefficient n * x ^ n| ≤
        ∑ n ∈ Ico N M, |coefficient n * x ^ n| := abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Ico N M, |coefficient n| * x ^ n := by
      simp_rw [abs_mul, abs_of_nonneg (pow_nonneg hx _)]
    _ ≤ ∑ n ∈ Ico N M, |coefficient n| * x ^ N := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hx hx1 (mem_Ico.mp hn).1) (abs_nonneg _)
    _ = (∑ n ∈ Ico N M, |coefficient n|) * x ^ N := by rw [sum_mul]
    _ ≤ 2 * x ^ N := mul_le_mul_of_nonneg_right
      (sum_abs_coefficient_Ico_le_two N M) (pow_nonneg hx N)

/-- The polynomial remains controlled even beyond the branch point. -/
theorem truncation_bound_of_one_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    |truncation N x| ≤ 2 * x ^ N := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  unfold truncation
  calc
    |∑ n ∈ range N, coefficient n * x ^ n| ≤
        ∑ n ∈ range N, |coefficient n * x ^ n| := abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ range N, |coefficient n| * x ^ n := by
      simp_rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
    _ ≤ ∑ n ∈ range N, |coefficient n| * x ^ N := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (mem_range.mp hn).le)
        (abs_nonneg _)
    _ = (∑ n ∈ range N, |coefficient n|) * x ^ N := by rw [sum_mul]
    _ ≤ 2 * x ^ N := mul_le_mul_of_nonneg_right
      (sum_abs_coefficient_le_two N) (pow_nonneg hx0 N)

/-- Global pointwise remainder for the actual square-root Taylor coefficients.
The bound includes the branch point and the whole region beyond it. -/
theorem sqrt_truncation_remainder {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    |Real.sqrt (max (1-x) 0) - truncation N x| ≤ 2 * x ^ N := by
  by_cases hx1 : x < 1
  · have hs := coefficient_hasSum_sqrt hx hx1
    have hb : |Real.sqrt (1-x) - truncation N x| ≤ 2 * x ^ N := by
      apply le_of_tendsto ((hs.tendsto_sum_nat.sub tendsto_const_nhds).abs)
      filter_upwards [eventually_ge_atTop N] with M hM
      exact truncation_tail_bound hx hx1.le hM
    simpa only [max_eq_left (sub_nonneg.mpr hx1.le)] using hb
  · have hxge : 1 ≤ x := le_of_not_gt hx1
    rw [max_eq_right (sub_nonpos.mpr hxge), Real.sqrt_zero, zero_sub, abs_neg]
    exact truncation_bound_of_one_le hxge N

/-- The rescaled integrand estimate used in the Gamma representation. -/
theorem sqrt_scaled_remainder {u κ : ℝ} (hu : 0 ≤ u) (hκ : 0 < κ) (N : ℕ) :
    |Real.sqrt (max (1-u/(2*κ)) 0) - truncation N (u/(2*κ))| ≤
      2 * u ^ N / (2*κ) ^ N := by
  simpa only [div_pow, mul_div_assoc] using
    sqrt_truncation_remainder (div_nonneg hu (by positivity : 0 ≤ 2*κ)) N

/-- The cutoff factor in the exact one-link Gamma integral. -/
def cutoffSqrt (κ u : ℝ) : ℝ := Real.sqrt (max (1-u/(2*κ)) 0)

/-- The unnormalized, unit-rate Gamma density on the positive half-line. -/
def gammaWeight (α u : ℝ) : ℝ := Real.exp (-u) * u ^ (α-1)

/-- Euler integration; the restriction to the positive half-line is explicit. -/
def gammaIntegral (α : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Ioi 0, gammaWeight α u * f u

theorem gammaWeight_nonneg (α : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gammaWeight α u := by
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu _)

theorem gammaWeight_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (gammaWeight α) (Set.Ioi 0) :=
  Real.GammaIntegral_convergent hα

theorem integral_gammaWeight {α : ℝ} (hα : 0 < α) :
    (∫ u in Set.Ioi 0, gammaWeight α u) = Real.Gamma α :=
  (Real.Gamma_eq_integral hα).symm

/-- Multiplication by a natural moment shifts the actual Euler density. -/
theorem gammaWeight_mul_pow (α : ℝ) {u : ℝ} (hu : 0 < u) (n : ℕ) :
    gammaWeight α u * u ^ n = gammaWeight (α+n) u := by
  unfold gammaWeight
  rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hu]
  congr 2
  ring

theorem gamma_moment_integrable {α : ℝ} (hα : 0 < α) (n : ℕ) :
    IntegrableOn (fun u => gammaWeight α u * u ^ n) (Set.Ioi 0) := by
  have hshape : 0 < α + (n : ℝ) := by positivity
  apply (gammaWeight_integrable hshape).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact (gammaWeight_mul_pow α hu n).symm

/-- Exact moment evaluation, rather than an assumed moment bound. -/
theorem integral_gamma_moment {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (∫ u in Set.Ioi 0, gammaWeight α u * u ^ n) = Real.Gamma (α+n) := by
  calc
    _ = ∫ u in Set.Ioi 0, gammaWeight (α+n) u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => gammaWeight_mul_pow α hu n)
    _ = _ := integral_gammaWeight (by positivity)

theorem cutoffSqrt_continuous (κ : ℝ) : Continuous (cutoffSqrt κ) := by
  unfold cutoffSqrt
  fun_prop

theorem cutoffSqrt_le_one {κ u : ℝ} (hκ : 0 < κ) (hu : 0 ≤ u) :
    cutoffSqrt κ u ≤ 1 := by
  unfold cutoffSqrt
  apply Real.sqrt_le_one.mpr
  apply max_le
  · have : 0 ≤ u/(2*κ) := div_nonneg hu (by positivity)
    linarith
  · norm_num

theorem cutoffSqrt_lower {κ u : ℝ} (hκ : 0 < κ) (hu : 0 ≤ u) :
    1-u/(2*κ) ≤ cutoffSqrt κ u := by
  let x := u/(2*κ)
  have hx : 0 ≤ x := div_nonneg hu (by positivity)
  change 1-x ≤ Real.sqrt (max (1-x) 0)
  by_cases hx1 : x ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hx1)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  · have h := Real.sqrt_nonneg (max (1-x) 0)
    linarith

theorem gamma_cutoff_integrable {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) :
    IntegrableOn (fun u => gammaWeight α u * cutoffSqrt κ u) (Set.Ioi 0) := by
  apply (gammaWeight_integrable hα).mono'
  · exact (gammaWeight_integrable hα).aestronglyMeasurable.mul
      (cutoffSqrt_continuous κ).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hf : 0 ≤ cutoffSqrt κ u := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (gammaWeight_nonneg α hu.le), abs_of_nonneg hf]
    exact mul_le_of_le_one_right (gammaWeight_nonneg α hu.le) (cutoffSqrt_le_one hκ hu.le)

/-- A direct Euler-integral remainder using the proved pointwise estimate. -/
theorem gamma_integral_remainder {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (N : ℕ) :
    |gammaIntegral α (fun u => cutoffSqrt κ u - truncation N (u/(2*κ)))| ≤
      (2 / (2*κ)^N) * Real.Gamma (α+N) := by
  have hmajor := (gamma_moment_integrable hα N).const_mul (2 / (2*κ)^N)
  have hb : ∀ᵐ u : ℝ ∂volume.restrict (Set.Ioi 0),
      ‖gammaWeight α u * (cutoffSqrt κ u - truncation N (u/(2*κ)))‖ ≤
        (2 / (2*κ)^N) * (gammaWeight α u * u^N) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gammaWeight_nonneg α hu.le)]
    have h := mul_le_mul_of_nonneg_left (sqrt_scaled_remainder hu.le hκ N)
      (gammaWeight_nonneg α hu.le)
    change gammaWeight α u * |cutoffSqrt κ u - truncation N (u/(2*κ))| ≤ _ at h
    convert h using 1
    ring
  have h := norm_integral_le_of_norm_le hmajor hb
  rw [Real.norm_eq_abs, integral_const_mul, integral_gamma_moment hα N] at h
  exact h

theorem gamma_polynomial_term (α κ u : ℝ) (n : ℕ) :
    gammaWeight α u * (coefficient n * (u/(2*κ))^n) =
      (coefficient n / (2*κ)^n) * (gammaWeight α u * u^n) := by
  rw [div_pow]
  ring

theorem gamma_polynomial_term_integrable {α : ℝ} (hα : 0 < α) (κ : ℝ) (n : ℕ) :
    IntegrableOn (fun u => gammaWeight α u * (coefficient n * (u/(2*κ))^n))
      (Set.Ioi 0) := by
  simp_rw [gamma_polynomial_term]
  exact (gamma_moment_integrable hα n).const_mul _

theorem gamma_truncation_integrable {α : ℝ} (hα : 0 < α) (κ : ℝ) (N : ℕ) :
    IntegrableOn (fun u => gammaWeight α u * truncation N (u/(2*κ)))
      (Set.Ioi 0) := by
  simp_rw [truncation, mul_sum]
  exact integrable_finset_sum _ (fun n _ => gamma_polynomial_term_integrable hα κ n)

/-- The finite polynomial integrates term by term with exact Gamma moments. -/
theorem gamma_integral_truncation {α : ℝ} (hα : 0 < α) (κ : ℝ) (N : ℕ) :
    gammaIntegral α (fun u => truncation N (u/(2*κ))) =
      ∑ n ∈ range N, (coefficient n / (2*κ)^n) * Real.Gamma (α+n) := by
  unfold gammaIntegral
  simp_rw [truncation, mul_sum]
  rw [integral_finset_sum _ (fun n _ => gamma_polynomial_term_integrable hα κ n)]
  apply sum_congr rfl
  intro n _
  simp_rw [gamma_polynomial_term]
  rw [integral_const_mul, integral_gamma_moment hα n]

/-- A remainder between the actual integral and its explicit finite expansion. -/
theorem gamma_cutoff_expansion {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (N : ℕ) :
    |gammaIntegral α (cutoffSqrt κ) -
      ∑ n ∈ range N, (coefficient n / (2*κ)^n) * Real.Gamma (α+n)| ≤
        (2 / (2*κ)^N) * Real.Gamma (α+N) := by
  have h := gamma_integral_remainder hα hκ N
  unfold gammaIntegral at h
  simp_rw [mul_sub] at h
  rw [integral_sub (gamma_cutoff_integrable hα hκ)
    (gamma_truncation_integrable hα κ N)] at h
  change |gammaIntegral α (cutoffSqrt κ) -
    gammaIntegral α (fun u => truncation N (u/(2*κ)))| ≤ _ at h
  rw [gamma_integral_truncation hα κ N] at h
  exact h

/-- Division by the exact Gamma normalizer gives the unit-rate expectation. -/
def gammaAverage (α : ℝ) (f : ℝ → ℝ) : ℝ := gammaIntegral α f / Real.Gamma α

theorem gamma_average_expansion {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (N : ℕ) :
    |gammaAverage α (cutoffSqrt κ) -
      (∑ n ∈ range N, (coefficient n / (2*κ)^n) * Real.Gamma (α+n)) / Real.Gamma α| ≤
        ((2 / (2*κ)^N) * Real.Gamma (α+N)) / Real.Gamma α := by
  have h := div_le_div_of_nonneg_right (gamma_cutoff_expansion hα hκ N)
    (Real.Gamma_pos_of_pos hα).le
  simpa only [gammaAverage, ← sub_div, abs_div,
    abs_of_pos (Real.Gamma_pos_of_pos hα)] using h

/-- Gamma moments are the explicit rising product, with no moment premise. -/
theorem gamma_shift_eq_product {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Real.Gamma (α+n) = (∏ i ∈ range n, (α+(i : ℝ))) * Real.Gamma α := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < α + (n : ℝ) := by positivity
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Real.Gamma_add_one hp.ne', ih,
        prod_range_succ]
      ring

theorem gamma_affine_integrable {α : ℝ} (hα : 0 < α) (κ : ℝ) :
    IntegrableOn (fun u => gammaWeight α u * (1-u/(2*κ))) (Set.Ioi 0) := by
  have hm : IntegrableOn (fun u => gammaWeight α u * u) (Set.Ioi 0) := by
    simpa only [pow_one] using gamma_moment_integrable hα 1
  have he : (fun u => gammaWeight α u * (1-u/(2*κ))) =
      (fun u => gammaWeight α u - (1/(2*κ)) * (gammaWeight α u * u)) := by
    ext u
    ring
  rw [he]
  exact (gammaWeight_integrable hα).sub (hm.const_mul (1/(2*κ)))

theorem gamma_integral_affine {α : ℝ} (hα : 0 < α) (κ : ℝ) :
    gammaIntegral α (fun u => 1-u/(2*κ)) =
      Real.Gamma α - Real.Gamma (α+1)/(2*κ) := by
  have hm : IntegrableOn (fun u => gammaWeight α u * u) (Set.Ioi 0) := by
    simpa only [pow_one] using gamma_moment_integrable hα 1
  have he : (fun u => gammaWeight α u * (1-u/(2*κ))) =
      (fun u => gammaWeight α u - (1/(2*κ)) * (gammaWeight α u * u)) := by
    ext u
    ring
  have hi : (∫ u in Set.Ioi 0, gammaWeight α u * u) = Real.Gamma (α+1) := by
    simpa only [pow_one, Nat.cast_one] using integral_gamma_moment hα 1
  unfold gammaIntegral
  rw [he, integral_sub (gammaWeight_integrable hα) (hm.const_mul _),
    integral_gammaWeight hα, integral_const_mul, hi]
  ring

/-- The lower bound is derived from the actual cutoff integrand. -/
theorem gamma_average_lower {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) :
    1-α/(2*κ) ≤ gammaAverage α (cutoffSqrt κ) := by
  have hi : gammaIntegral α (fun u => 1-u/(2*κ)) ≤
      gammaIntegral α (cutoffSqrt κ) := by
    apply integral_mono_ae (gamma_affine_integrable hα κ) (gamma_cutoff_integrable hα hκ)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_left (cutoffSqrt_lower hκ hu.le)
      (gammaWeight_nonneg α hu.le)
  have h := div_le_div_of_nonneg_right hi (Real.Gamma_pos_of_pos hα).le
  rw [gamma_integral_affine hα κ, Real.Gamma_add_one hα.ne'] at h
  have he : (Real.Gamma α - α * Real.Gamma α / (2*κ)) / Real.Gamma α =
      1-α/(2*κ) := by
    field_simp [(Real.Gamma_pos_of_pos hα).ne', hκ.ne']
  rw [he] at h
  exact h

/-- A fixed lower bound permitting the subsequent finite quotient estimate. -/
theorem gamma_average_ge_half {α κ : ℝ} (hα : 0 < α) (hακ : α ≤ κ) :
    (1/2 : ℝ) ≤ gammaAverage α (cutoffSqrt κ) := by
  have hκ : 0 < κ := hα.trans_le hακ
  have hd : α/(2*κ) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*κ)).mpr
    linarith
  linarith [gamma_average_lower hα hκ]

/-- The denominator estimate for the SU(2) shape `3/2`. -/
theorem su2_denominator_lower {κ : ℝ} (hκ : 0 < κ) :
    1-3/(4*κ) ≤ gammaAverage (3/2) (cutoffSqrt κ) := by
  convert gamma_average_lower (by norm_num : (0 : ℝ) < 3/2) hκ using 1
  ring_nf

theorem su2_denominator_ge_half {κ : ℝ} (hκ : (3 / 2 : ℝ) ≤ κ) :
    (1/2 : ℝ) ≤ gammaAverage (3/2) (cutoffSqrt κ) :=
  gamma_average_ge_half (by norm_num) hκ

/-- Exact transport of a moment factor to a shifted Gamma shape. -/
theorem gamma_integral_moment_shift (α : ℝ) (q : ℕ) (f : ℝ → ℝ) :
    gammaIntegral α (fun u => u^q * f u) = gammaIntegral (α+q) f := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change gammaWeight α u * (u^q * f u) = gammaWeight (α+q) u * f u
  rw [← mul_assoc, gammaWeight_mul_pow α hu q]

/-- The numerator case is `q=1`; no moment or remainder bound is a premise. -/
theorem gamma_integral_moment_remainder {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (q N : ℕ) :
    |gammaIntegral α (fun u => u^q * (cutoffSqrt κ u - truncation N (u/(2*κ))))| ≤
      (2 / (2*κ)^N) * Real.Gamma (α+(q+N : ℕ)) := by
  rw [gamma_integral_moment_shift]
  convert gamma_integral_remainder (show 0 < α+(q : ℝ) by positivity) hκ N using 1
  push_cast
  ring_nf

/-- Moment-weighted finite expansions also integrate exactly. -/
theorem gamma_cutoff_moment_expansion {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (q N : ℕ) :
    |gammaIntegral α (fun u => u^q * cutoffSqrt κ u) -
      ∑ n ∈ range N, (coefficient n / (2*κ)^n) * Real.Gamma ((α+q)+n)| ≤
        (2 / (2*κ)^N) * Real.Gamma ((α+q)+N) := by
  rw [gamma_integral_moment_shift]
  exact gamma_cutoff_expansion (by positivity) hκ N

/-- Actual unit-rate moment-weighted expectation, with the original normalizer. -/
theorem gamma_average_moment_expansion {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (q N : ℕ) :
    |gammaAverage α (fun u => u^q * cutoffSqrt κ u) -
      (∑ n ∈ range N, (coefficient n / (2*κ)^n) * Real.Gamma ((α+q)+n)) /
        Real.Gamma α| ≤
        ((2 / (2*κ)^N) * Real.Gamma ((α+q)+N)) / Real.Gamma α := by
  have h := div_le_div_of_nonneg_right (gamma_cutoff_moment_expansion hα hκ q N)
    (Real.Gamma_pos_of_pos hα).le
  simpa only [gammaAverage, ← sub_div, abs_div,
    abs_of_pos (Real.Gamma_pos_of_pos hα)] using h

/-- The normalized moment coefficients are explicit finite rising products. -/
theorem gamma_normalized_moment_term {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (q n : ℕ) (c : ℝ) :
    ((c / (2*κ)^n) * Real.Gamma ((α+q)+n)) / Real.Gamma α =
      c * (∏ i ∈ range (q+n), (α+(i : ℝ))) / (2*κ)^n := by
  have he : (α+(q : ℝ))+(n : ℝ) = α+(q+n : ℕ) := by push_cast; ring
  rw [he, gamma_shift_eq_product hα (q+n)]
  field_simp [(Real.Gamma_pos_of_pos hα).ne', hκ.ne']

/-- Fully explicit Gamma expansion, including all natural numerator moments. -/
theorem gamma_average_moment_expansion_product {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (q N : ℕ) :
    |gammaAverage α (fun u => u^q * cutoffSqrt κ u) -
      ∑ n ∈ range N,
        coefficient n * (∏ i ∈ range (q+n), (α+(i : ℝ))) / (2*κ)^n| ≤
      2 * (∏ i ∈ range (q+N), (α+(i : ℝ))) / (2*κ)^N := by
  have h := gamma_average_moment_expansion hα hκ q N
  rw [sum_div] at h
  simp_rw [gamma_normalized_moment_term hα hκ] at h
  exact h

/-- The precise denominator expansion for the shape `3/2` source integral. -/
theorem su2_denominator_expansion {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    |gammaAverage (3/2) (cutoffSqrt κ) -
      ∑ n ∈ range N,
        coefficient n * (∏ i ∈ range n, ((3/2 : ℝ)+(i : ℝ))) / (2*κ)^n| ≤
      2 * (∏ i ∈ range N, ((3/2 : ℝ)+(i : ℝ))) / (2*κ)^N := by
  simpa only [zero_add, pow_zero, one_mul] using
    gamma_average_moment_expansion_product (by norm_num : (0 : ℝ) < 3/2) hκ 0 N

/-- The precise numerator expansion for the shape `3/2` source integral. -/
theorem su2_numerator_expansion {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    |gammaAverage (3/2) (fun u => u * cutoffSqrt κ u) -
      ∑ n ∈ range N,
        coefficient n * (∏ i ∈ range (1+n), ((3/2 : ℝ)+(i : ℝ))) / (2*κ)^n| ≤
      2 * (∏ i ∈ range (1+N), ((3/2 : ℝ)+(i : ℝ))) / (2*κ)^N := by
  simpa only [pow_one] using
    gamma_average_moment_expansion_product (by norm_num : (0 : ℝ) < 3/2) hκ 1 N

end
end UnifiedTheory.Clay.YangMills.SqrtSourceRemainder
