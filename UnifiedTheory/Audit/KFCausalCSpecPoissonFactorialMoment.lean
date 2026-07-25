/-
  Audit/KFCausalCSpecPoissonFactorialMoment.lean   (Volume sector → goal B foothold)

  The general Poisson FACTORIAL-MOMENT identity:

      sum_n poissonPMFReal r n * (n)_k  =  r^k,       (n)_k = n(n-1)...(n-k+1),

  i.e. `E[(N)_k] = r^k` for `N ~ Poisson(r)`.  Proved by the shift `n ↦ n+k` that
  collapses the summand to `(exp(-r) r^k)(r^n/n!)`, an exp series.

  WHY THIS IS THE GOAL-B FOOTHOLD.  The Benincasa-Dowker-Glaser causal-set action and the
  causal-set d'Alembertian are built from LAYER COUNTS: the number of elements `y ≺ x`
  with exactly `i` elements in the order-interval `(y, x)`.  Under a Poisson sprinkling of
  density `ρ`, that layer index is `Poisson(ρ V(y,x))`, so the mean of any layer-weighted
  operator `sum_i b_i (·)` is governed by the Poisson moments of the layer index.  The
  BDG coefficients `b_i` are precisely those that make a chosen combination of these
  factorial moments cancel the volume-divergent orders and leave the curvature term.  This
  identity is the exact algebraic input that construction rests on.

  It also SUBSUMES the two moment lemmas used to close the count-concentration arc:
    * `k = 1` : `(n)_1 = n`      gives the mean `E[N] = r`;
    * `k = 2` : `(n)_2 = n(n-1)` gives `E[N(N-1)] = r^2`.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Real NNReal Nat ProbabilityTheory

namespace UnifiedTheory.Audit.KFCausalCSpecPoissonFactorialMoment

/-- **Poisson factorial moments.**  `E[(N)_k] = r^k` for `N ~ Poisson(r)`, at the level of
the pmf: `sum_n poissonPMFReal r n * descFactorial n k = r^k`.  The algebraic basis of the
BDG causal-set action / d'Alembertian coefficient construction. -/
theorem poissonPMFReal_descFactorial_hasSum (r : ℝ≥0) (k : ℕ) :
    HasSum (fun n => poissonPMFReal r n * (Nat.descFactorial n k : ℝ)) ((r : ℝ) ^ k) := by
  have hg : Function.Injective (fun n : ℕ => n + k) := add_left_injective k
  have hz : ∀ x ∉ Set.range (fun n : ℕ => n + k),
      (fun n => poissonPMFReal r n * (Nat.descFactorial n k : ℝ)) x = 0 := by
    intro x hx
    have hxk : x < k := by
      by_contra h
      push_neg at h
      exact hx (Set.mem_range.mpr ⟨x - k, by omega⟩)
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hxk]
  rw [← Function.Injective.hasSum_iff hg hz]
  have hterm : ∀ n : ℕ, poissonPMFReal r (n + k) * (Nat.descFactorial (n + k) k : ℝ)
      = (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    have hn : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hnk : (Nat.factorial (n + k) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + k)
    have hnat : Nat.factorial n * Nat.descFactorial (n + k) k = Nat.factorial (n + k) := by
      have h := Nat.factorial_mul_descFactorial (Nat.le_add_left k n)
      rwa [Nat.add_sub_cancel] at h
    have hdesc : (Nat.descFactorial (n + k) k : ℝ)
        = (Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ) := by
      rw [eq_div_iff hn, mul_comm]
      exact_mod_cast hnat
    simp only [poissonPMFReal]
    rw [hdesc, pow_add]
    field_simp
  simp only [Function.comp_def, hterm]
  have hs := (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k)
  convert hs using 1
  rw [← Real.exp_eq_exp_ℝ, mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- `k = 1` specialization: the Poisson mean `E[N] = r`. -/
theorem poissonPMFReal_mean (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * (n : ℝ)) (r : ℝ) := by
  have h := poissonPMFReal_descFactorial_hasSum r 1
  simpa using h

/-- `k = 2` specialization: `E[N(N-1)] = r^2`. -/
theorem poissonPMFReal_secondFactorial (r : ℝ≥0) :
    HasSum (fun n => poissonPMFReal r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  have h := poissonPMFReal_descFactorial_hasSum r 2
  have hrw : (fun n => poissonPMFReal r n * (Nat.descFactorial n 2 : ℝ))
      = fun n => poissonPMFReal r n * ((n : ℝ) * ((n : ℝ) - 1)) := by
    funext n
    rcases n with _ | m
    · simp
    · push_cast [Nat.descFactorial]
      ring
  rw [hrw] at h
  exact h

#print axioms poissonPMFReal_descFactorial_hasSum
#print axioms poissonPMFReal_mean
#print axioms poissonPMFReal_secondFactorial

end UnifiedTheory.Audit.KFCausalCSpecPoissonFactorialMoment
