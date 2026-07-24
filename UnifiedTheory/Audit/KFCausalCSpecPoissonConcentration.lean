/-
  Audit/KFCausalCSpecPoissonConcentration.lean   (Volume sector — Poisson wiring, arc closure)

  The final wiring: lift the pmf-level Poisson moment series
  (`KFCausalCSpecPoissonMoments`) through the measure integral to `variance = r`, and
  drop it into the distribution-free Chebyshev bound
  (`KFCausalCSpecCountConcentration`).  This closes the statistical arc: a genuine
  Poisson count concentrates.

  Route (ℕ is countable with measurable singletons, so `poissonMeasure` is discrete):
    * `poissonMeasure_apply_singleton` : point mass = `ENNReal.ofReal (poissonPMFReal r n)`.
    * `poisson_integrable` : a nonneg `g` whose weighted series is summable is integrable
      (`lintegral_countable'` + `ENNReal.ofReal_tsum_of_nonneg`).
    * `poisson_integral` : `∫ g = sum_n poissonPMFReal r n * g n` (`PMF.integral_eq_tsum`).
    * `poisson_mean`      : `∫ n = r`.
    * `poisson_integral_sq` : `∫ n^2 = r^2 + r`  (from n^2 = n(n-1) + n).
    * `poisson_variance`  : `Var[n] = (r^2 + r) - r^2 = r`  (`variance_eq_sub`).
    * `poisson_count_concentration` : `Pr(|N/r - 1| >= eps) <= 1/(r eps^2)`.

  No Mathlib precedent existed for any named-distribution variance; this is the first.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecCountConcentration
import UnifiedTheory.Audit.KFCausalCSpecPoissonMoments

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real NNReal Nat
open UnifiedTheory.Audit.KFCausalCSpecPoissonMoments

namespace UnifiedTheory.Audit.KFCausalCSpecPoissonConcentration

/-- Point mass of the Poisson measure. -/
theorem poissonMeasure_apply_singleton (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n} = ENNReal.ofReal (poissonPMFReal r n) := by
  rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  rfl

/-- A nonnegative `g` with summable weighted series is integrable against `poissonMeasure`. -/
theorem poisson_integrable (r : ℝ≥0) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (hsum : Summable (fun n => poissonPMFReal r n * g n)) :
    Integrable g (poissonMeasure r) := by
  refine ⟨(measurable_of_countable g).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
  have hterm : ∀ n, ‖g n‖ₑ * poissonMeasure r {n}
      = ENNReal.ofReal (g n * poissonPMFReal r n) := by
    intro n
    rw [Real.enorm_of_nonneg (hg n), poissonMeasure_apply_singleton,
      ← ENNReal.ofReal_mul (hg n)]
  rw [tsum_congr hterm,
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (hg n) poissonPMFReal_nonneg)
      (by simpa [mul_comm] using hsum)]
  exact ENNReal.ofReal_lt_top

/-- The integral against `poissonMeasure` is the weighted pmf series. -/
theorem poisson_integral (r : ℝ≥0) (g : ℕ → ℝ) (hint : Integrable g (poissonMeasure r)) :
    ∫ n, g n ∂(poissonMeasure r) = ∑' n, poissonPMFReal r n * g n := by
  rw [poissonMeasure, PMF.integral_eq_tsum _ _ hint]
  refine tsum_congr (fun n => ?_)
  rw [smul_eq_mul]
  congr 1
  rw [poissonPMF]
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

/-- **Poisson mean.**  `∫ n = r`. -/
theorem poisson_mean (r : ℝ≥0) : ∫ n, (n : ℝ) ∂(poissonMeasure r) = (r : ℝ) := by
  rw [poisson_integral r _
    (poisson_integrable r _ (fun n => Nat.cast_nonneg n) (poissonPMFReal_mul_hasSum r).summable)]
  exact (poissonPMFReal_mul_hasSum r).tsum_eq

/-- The second-moment series `sum_n poissonPMFReal r n * n^2 = r^2 + r`, from
`n^2 = n(n-1) + n`. -/
theorem poisson_sq_hasSum (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + r) := by
  have h := (poissonPMFReal_descFactorialTwo_hasSum r).add (poissonPMFReal_mul_hasSum r)
  have key : (fun n => poissonPMFReal r n * (n : ℝ) ^ 2)
      = fun n => poissonPMFReal r n * ((n : ℝ) * ((n : ℝ) - 1)) + poissonPMFReal r n * (n : ℝ) := by
    ext n; ring
  rw [key]; exact h

/-- **Poisson second moment.**  `∫ n^2 = r^2 + r`. -/
theorem poisson_integral_sq (r : ℝ≥0) :
    ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  rw [poisson_integral r _
    (poisson_integrable r _ (fun n => sq_nonneg _) (poisson_sq_hasSum r).summable)]
  exact (poisson_sq_hasSum r).tsum_eq

/-- The count `n ↦ (n : ℝ)` is in `L²` of the Poisson measure. -/
theorem poisson_memLp (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  rw [memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable]
  exact poisson_integrable r _ (fun n => sq_nonneg _) (poisson_sq_hasSum r).summable

/-- **Poisson variance.**  `Var[n] = (r^2 + r) - r^2 = r`.  No Mathlib precedent existed
for a named-distribution variance. -/
theorem poisson_variance (r : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = (r : ℝ) := by
  rw [variance_eq_sub (poisson_memLp r)]
  have e1 : (poissonMeasure r)[(fun n : ℕ => (n : ℝ)) ^ 2] = (r : ℝ) ^ 2 + r :=
    poisson_integral_sq r
  have e2 : (poissonMeasure r)[fun n : ℕ => (n : ℝ)] = (r : ℝ) := poisson_mean r
  rw [e1, e2]; ring

/-- **Poisson count concentration (arc closure).**  A genuine Poisson count with rate
`r` concentrates: `Pr(|N/r - 1| >= eps) <= 1/(r eps^2)`.  Instantiates the
distribution-free `chebyshev_relative_error` with `mean = variance = r`. -/
theorem poisson_count_concentration (r : ℝ≥0) (ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    poissonMeasure r {n | ε ≤ |(n : ℝ) / (r : ℝ) - 1|}
      ≤ ENNReal.ofReal (1 / ((r : ℝ) * ε ^ 2)) :=
  KFCausalCSpecCountConcentration.chebyshev_relative_error (poisson_memLp r)
    (by exact_mod_cast hr) hε (poisson_mean r) (le_of_eq (poisson_variance r))

#print axioms poisson_mean
#print axioms poisson_variance
#print axioms poisson_count_concentration

end UnifiedTheory.Audit.KFCausalCSpecPoissonConcentration
