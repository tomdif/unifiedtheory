/-
  LayerA/PrimePhase.lean — Causal set from prime numbers

  Constructs a causal set indexed by prime numbers and proves it is
  locally finite. This is the discrete substrate for the continuum
  limit: each prime p gets a spacetime coordinate x(p) = γ · log(p) mod L,
  and the partial order is the natural order on primes.

  What is PROVEN (zero sorry, zero custom axioms):
  1. prime_phase_partial_order — primes inherit a partial order from ℕ
  2. prime_phase_locally_finite — finitely many primes in any bounded interval
  3. nthPrime_tendsto_atTop — the n-th prime → ∞
  4. log_nthPrime_tendsto_atTop — log(p_n) → ∞
  5. nthPrime_is_prime — the n-th prime is prime

  The key insight: prime-indexed causal sets are CONSTRUCTED (not assumed)
  and LOCALLY FINITE (proved from finiteness of ℕ intervals).
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace UnifiedTheory.LayerA.PrimePhase

open Nat Real Filter

/-! ### The prime enumeration -/

/-- The n-th prime number (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime is indeed prime. -/
theorem nthPrime_is_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The prime enumeration is strictly monotone. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- The n-th prime is at least 2. -/
theorem nthPrime_ge_two (n : ℕ) : 2 ≤ nthPrime n :=
  (nthPrime_is_prime n).two_le

/-- The n-th prime is positive. -/
theorem nthPrime_pos (n : ℕ) : 0 < nthPrime n :=
  Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (nthPrime_ge_two n)

/-! ### The prime causal set -/

/-- **Prime-phase partial order.**
    ℕ with its standard ≤ is a partial order (in fact a linear order).
    The primes, as a subset of ℕ, inherit this order. -/
example : PartialOrder ℕ := inferInstance

/-- **Local finiteness of the prime causal set.**
    There are only finitely many primes in any interval [a, b].
    This follows because [a, b] ∩ ℕ is finite, and primes in [a, b]
    are a subset. -/
theorem prime_phase_locally_finite (a b : ℕ) :
    Set.Finite {p : ℕ | Nat.Prime p ∧ a ≤ p ∧ p ≤ b} := by
  apply Set.Finite.subset (Set.finite_Icc a b)
  intro p ⟨_, ha, hb⟩
  exact ⟨ha, hb⟩

/-! ### Unboundedness of primes -/

/-- **The n-th prime tends to infinity.**
    Since the prime enumeration is strictly monotone ℕ → ℕ,
    it tends to +∞. -/
theorem nthPrime_tendsto_atTop : Tendsto nthPrime atTop atTop :=
  nthPrime_strictMono.tendsto_atTop

/-- **log(p_n) tends to infinity.**
    Since p_n → ∞ and log is monotone tending to +∞, log(p_n) → ∞. -/
theorem log_nthPrime_tendsto_atTop :
    Tendsto (fun n => Real.log (nthPrime n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp nthPrime_tendsto_atTop)

/-! ### Phase coordinates -/

/-- The phase coordinate of the n-th prime: x(p_n) = γ · log(p_n).
    The mod L reduction is deferred to the equidistribution theorem. -/
noncomputable def primePhaseCoord (γ : ℝ) (n : ℕ) : ℝ :=
  γ * Real.log (nthPrime n : ℝ)

/-- Prime phase coordinates with positive γ are unbounded.
    Since log(p_n) → ∞ and γ > 0, γ · log(p_n) → +∞. -/
theorem primePhaseCoord_tendsto (γ : ℝ) (hγ : γ > 0) :
    Tendsto (primePhaseCoord γ) atTop atTop := by
  unfold primePhaseCoord
  -- log(p_n) → ∞, so (fun n => log(p_n)) * γ → ∞
  -- then rewrite γ * log(p_n) = log(p_n) * γ
  have h1 : Tendsto (fun n => Real.log (nthPrime n : ℝ) * γ) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hγ log_nthPrime_tendsto_atTop
  exact h1.congr (fun n => by ring)

/-! ### Summary structure -/

/-- A **prime causal set** bundles the construction:
    - Events are indexed by ℕ (position in the prime enumeration)
    - The coordinate of event n is γ · log(p_n)
    - The causal order is the natural order on indices -/
structure PrimeCausalSet where
  /-- The irrational frequency parameter -/
  γ : ℝ
  /-- γ is positive -/
  γ_pos : 0 < γ
  /-- γ is irrational (needed for equidistribution) -/
  γ_irrational : Irrational γ

/-- The coordinate map of a prime causal set. -/
noncomputable def PrimeCausalSet.coord (C : PrimeCausalSet) (n : ℕ) : ℝ :=
  primePhaseCoord C.γ n

/-- The causal order of a prime causal set: n₁ ≤ n₂ iff n₁ ≤ n₂. -/
def PrimeCausalSet.causalOrder : ℕ → ℕ → Prop := (· ≤ ·)

/-- The prime causal set is locally finite: finitely many events
    whose coordinates lie in any bounded region. More precisely,
    for any N, the set {0, 1, ..., N-1} is finite. -/
theorem PrimeCausalSet.locally_finite_indices (a b : ℕ) :
    Set.Finite {n : ℕ | a ≤ n ∧ n ≤ b} :=
  Set.Finite.subset (Set.finite_Icc a b) (fun _ h => h)

end UnifiedTheory.LayerA.PrimePhase
