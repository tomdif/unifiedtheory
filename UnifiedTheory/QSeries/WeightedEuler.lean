/-
Weighted Euler products with certified, computable coefficients.

For any multiplicities `w : ℕ → ℕ`, the product
  ∏_{k ≥ 1} (1 - X^k)^(-w k)
is defined by coefficient stabilization. Every coefficient is computed by a finite
natural-number convolution. This is formal algebra; analytic convergence and an
interpretation as a physical state count are separate obligations.
-/
import UnifiedTheory.QSeries.Watson.Prod
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

namespace UnifiedTheory.QSeries

open PowerSeries Finset

/-- Coefficient of `(1-X^k)^(-m)` for positive `k`. -/
def eulerFactorCoeff (k m n : ℕ) : ℕ :=
  if m = 0 then (if n = 0 then 1 else 0)
  else if k ∣ n then (m - 1 + n / k).choose (m - 1) else 0

/-- The factor at size `k+1`, with arbitrary nonnegative multiplicity. -/
noncomputable def eulerFactor (w : ℕ → ℕ) (k : ℕ) : PowerSeries ℤ :=
  expand (k + 1) (by omega) (invOneSubPow ℤ (w (k + 1))).val

theorem coeff_eulerFactor (w : ℕ → ℕ) (k n : ℕ) :
    coeff n (eulerFactor w k) = (eulerFactorCoeff (k + 1) (w (k + 1)) n : ℤ) := by
  unfold eulerFactor eulerFactorCoeff
  by_cases hm : w (k + 1) = 0
  · simp [hm, invOneSubPow_zero, coeff_one]
  · rw [if_neg hm, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ _ (by omega),
      coeff_expand]
    split_ifs <;> simp

theorem eulerFactor_cancels (w : ℕ → ℕ) (k : ℕ) :
    eulerFactor w k * (1 - X ^ (k + 1)) ^ (w (k + 1)) = 1 := by
  have h := (invOneSubPow ℤ (w (k + 1))).val_inv
  rw [invOneSubPow_inv_eq_one_sub_pow] at h
  have he := congrArg (expand (k + 1) (by omega)) h
  simpa [eulerFactor, map_mul, map_pow, map_sub, expand_X] using he

theorem eulerFactor_sub_one_dvd (w : ℕ → ℕ) (k : ℕ) :
    (X : PowerSeries ℤ) ^ (k + 1) ∣ eulerFactor w k - 1 := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [map_sub, coeff_eulerFactor, coeff_one]
  by_cases hn0 : n = 0
  · subst n
    simp [eulerFactorCoeff]
  · have hnd : ¬ k + 1 ∣ n := by
      intro hd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
      omega
    simp [eulerFactorCoeff, hn0, hnd]

/-- Product through size `N`; factors of larger size cannot affect lower coefficients. -/
noncomputable def weightedEulerPartial (w : ℕ → ℕ) (N : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ range N, eulerFactor w k

theorem weightedEulerPartial_succ (w : ℕ → ℕ) (N : ℕ) :
    weightedEulerPartial w (N + 1) = weightedEulerPartial w N * eulerFactor w N := by
  simp [weightedEulerPartial, prod_range_succ]

theorem coeff_weightedEulerPartial_stable (w : ℕ → ℕ) {n N M : ℕ}
    (hn : n ≤ N) (hNM : N ≤ M) :
    coeff n (weightedEulerPartial w M) = coeff n (weightedEulerPartial w N) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    rw [weightedEulerPartial_succ,
      Watson.coeff_mul_of_dvd_sub_one (eulerFactor_sub_one_dvd w M) (by omega), ih]

/-- The genuine infinite weighted Euler product, as a formal power series. -/
noncomputable def weightedEuler (w : ℕ → ℕ) : PowerSeries ℤ :=
  mk fun n => coeff n (weightedEulerPartial w (n + 1))

theorem coeff_weightedEuler (w : ℕ → ℕ) {n N : ℕ} (hn : n ≤ N) :
    coeff n (weightedEuler w) = coeff n (weightedEulerPartial w N) := by
  rw [weightedEuler, coeff_mk]
  rcases le_total (n + 1) N with h | h
  · exact (coeff_weightedEulerPartial_stable w (by omega) h).symm
  · exact coeff_weightedEulerPartial_stable w hn h

/-- A finite convolution algorithm, with no table of precomputed coefficients. -/
def weightedEulerCoeff (w : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | N + 1, n => ∑ ij ∈ antidiagonal n,
      weightedEulerCoeff w N ij.1 * eulerFactorCoeff (N + 1) (w (N + 1)) ij.2

theorem coeff_weightedEulerPartial (w : ℕ → ℕ) (N n : ℕ) :
    coeff n (weightedEulerPartial w N) = (weightedEulerCoeff w N n : ℤ) := by
  induction N generalizing n with
  | zero => simp [weightedEulerPartial, weightedEulerCoeff, coeff_one]
  | succ N ih =>
    rw [weightedEulerPartial_succ, coeff_mul, weightedEulerCoeff]
    simp only [ih, coeff_eulerFactor, Nat.cast_sum, Nat.cast_mul]

theorem coeff_weightedEuler_computable (w : ℕ → ℕ) (n : ℕ) :
    coeff n (weightedEuler w) = (weightedEulerCoeff w n n : ℤ) := by
  rw [coeff_weightedEuler w le_rfl, coeff_weightedEulerPartial]

theorem coeff_weightedEuler_nonneg (w : ℕ → ℕ) (n : ℕ) :
    0 ≤ coeff n (weightedEuler w) := by
  rw [coeff_weightedEuler_computable]
  positivity

/-- MacMahon's solid-partition product uses triangular multiplicities.
This product does not enumerate solid partitions by their ordinary volume. -/
def macMahonMultiplicity (k : ℕ) : ℕ := k * (k + 1) / 2

def macMahonCoefficient (n : ℕ) : ℕ :=
  weightedEulerCoeff macMahonMultiplicity n n

noncomputable def macMahonProduct : PowerSeries ℤ := weightedEuler macMahonMultiplicity

theorem coeff_macMahonProduct (n : ℕ) :
    coeff n macMahonProduct = (macMahonCoefficient n : ℤ) :=
  coeff_weightedEuler_computable macMahonMultiplicity n

end UnifiedTheory.QSeries
