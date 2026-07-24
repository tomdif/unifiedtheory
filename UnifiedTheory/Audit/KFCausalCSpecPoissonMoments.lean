/-
  Audit/KFCausalCSpecPoissonMoments.lean   (Volume sector — Poisson moment series)

  The Poisson-specific input Mathlib lacks: the moment series of `poissonPMFReal`.
  These are the ONE hole flagged by `KFCausalCSpecCountConcentration` — instantiating
  its mean/variance hypotheses for a Poisson count.

  Mathlib has `poissonPMFReal r n = exp(-r) r^n / n!` and the exp series
  `expSeries_div_hasSum_exp`, but NO Poisson moments.  We derive them by index-shifts
  of the exp series:

    * `poissonPMFReal_mul_hasSum`      : sum_n pmf(n) * n       = r      (mean).
    * `poissonPMFReal_descFactorialTwo_hasSum` :
                                         sum_n pmf(n) * n(n-1)  = r^2    (2nd factorial
                                         moment; with the mean gives Var = r).

  Since Var[N] = E[N(N-1)] + E[N] - E[N]^2 = r^2 + r - r^2 = r, these two series ARE
  `Var(Poisson r) = r` at the level of the pmf.  Wiring them through the measure
  integral (`PMF.integral_eq_tsum`) into `variance ... = r` is the final assembly.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Real NNReal Nat

namespace UnifiedTheory.Audit.KFCausalCSpecPoissonMoments

open ProbabilityTheory

/-- **Poisson mean series.**  `sum_n poissonPMFReal r n * n = r`.  Proved by the shift
`n ↦ n+1`, which turns the summand into `(exp(-r) r) * (r^n / n!)`, an `exp` series. -/
theorem poissonPMFReal_mul_hasSum (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * (n : ℝ)) (r : ℝ) := by
  have hg : Function.Injective (fun n : ℕ => n + 1) := add_left_injective 1
  have hz : ∀ x ∉ Set.range (fun n : ℕ => n + 1),
      (fun n => poissonPMFReal r n * (n : ℝ)) x = 0 := by
    intro x hx
    have hx0 : x = 0 := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact h
      · exact absurd (Set.mem_range.mpr ⟨x - 1, by omega⟩) hx
    subst hx0; simp
  rw [← Function.Injective.hasSum_iff hg hz]
  have hterm : ∀ n : ℕ, poissonPMFReal r (n + 1) * ((n + 1 : ℕ) : ℝ)
      = (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    simp only [poissonPMFReal]
    rw [Nat.factorial_succ]
    push_cast
    have hn : ((Nat.factorial n : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring
  simp only [Function.comp_def, hterm]
  have hs := (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left
    (Real.exp (-(r : ℝ)) * (r : ℝ))
  convert hs using 1
  rw [← Real.exp_eq_exp_ℝ, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **Poisson second factorial moment series.**  `sum_n poissonPMFReal r n * n(n-1) = r^2`.
Proved by the double shift `n ↦ n+2`, turning the summand into `(exp(-r) r^2)(r^n/n!)`. -/
theorem poissonPMFReal_descFactorialTwo_hasSum (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  have hg : Function.Injective (fun n : ℕ => n + 2) := add_left_injective 2
  have hz : ∀ x ∉ Set.range (fun n : ℕ => n + 2),
      (fun n => poissonPMFReal r n * ((n : ℝ) * ((n : ℝ) - 1))) x = 0 := by
    intro x hx
    have hlt : x < 2 := by
      by_contra h
      push_neg at h
      exact hx (Set.mem_range.mpr ⟨x - 2, by omega⟩)
    interval_cases x <;> simp
  rw [← Function.Injective.hasSum_iff hg hz]
  have hterm : ∀ n : ℕ, poissonPMFReal r (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
      = (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    simp only [poissonPMFReal]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hn : ((Nat.factorial n : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have h1 : ((n : ℝ) + 1) ≠ 0 := (by positivity : (0:ℝ) < (n : ℝ) + 1).ne'
    have h2 : ((n : ℝ) + 2) ≠ 0 := (by positivity : (0:ℝ) < (n : ℝ) + 2).ne'
    field_simp
    ring
  simp only [Function.comp_def, hterm]
  have hs := (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2)
  convert hs using 1
  rw [← Real.exp_eq_exp_ℝ, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

#print axioms poissonPMFReal_mul_hasSum
#print axioms poissonPMFReal_descFactorialTwo_hasSum

end UnifiedTheory.Audit.KFCausalCSpecPoissonMoments
