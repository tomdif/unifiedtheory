/- The in-plane constant `K̄` of `TwistedFluxInduction` as a thermal excess (abstract form).

Doubling an in-plane direction of length `t` with fixed spatial box gives `Z(t) = Tr T^t`, and
`Kper = Z(t)² / Z(2t)`. Normalise the ground state to `E₀ = 0` and write `P(t) = Σ_{i>0} e^{-t E_i}` for the thermal
excess at temperature `1/t`, so `Z(t) = 1 + P(t)`.

* `excess_antitone`: with `E_i ≥ 0`, `P(2t) ≤ P(t)`.
* `kper_sandwich`: `0 ≤ P(2t) ≤ P(t)` gives `1 + P(t) ≤ Kper ≤ (1 + P(t))²`. So `log Kper` is a two-sided proxy for the
  thermal free energy, and `K̄` (Kper bounded) is EQUIVALENT to the thermal excess at `T = 1/L` being bounded.
* `k_le_two_kper`: with `0 ≤ z ≤ 1`, `0 ≤ z'`, the in-plane constant `K = Kper ((1+z)/2)² / ((1+z')/2)` obeys `K ≤ 2 Kper`.
* `log_z_telescope`: `f 0 - f n / 2^n = Σ_{k<n} (2 f k - f (k+1)) / 2^(k+1)`. With `f k = log Z(2^k t)` and the limit, the
  thermal free energy `log(1 + P(t))` equals `Σ_k 2^{-(k+1)} log Kper(2^k t)`, an exact sum of measured quantities.

The identification with lattice traces is by hand, as in the other Twisted files. The boundedness of `P` itself is NOT
proved here. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedThermalExcess

/-- With nonnegative excitation energies, the thermal excess decreases when the time extent doubles. -/
theorem excess_antitone {ι : Type*} (s : Finset ι) (E : ι → ℝ) (hE : ∀ i ∈ s, 0 ≤ E i) {t : ℝ} (ht : 0 ≤ t) :
    ∑ i ∈ s, Real.exp (-(2 * t) * E i) ≤ ∑ i ∈ s, Real.exp (-t * E i) := by
  apply Finset.sum_le_sum; intro i hi
  apply Real.exp_le_exp.mpr; nlinarith [hE i hi, mul_nonneg ht (hE i hi)]

/-- `0 ≤ P₂ ≤ P₁` gives `1 + P₁ ≤ (1 + P₁)² / (1 + P₂) ≤ (1 + P₁)²`. -/
theorem kper_sandwich {P₁ P₂ : ℝ} (h0 : 0 ≤ P₂) (h : P₂ ≤ P₁) :
    1 + P₁ ≤ (1 + P₁) ^ 2 / (1 + P₂) ∧ (1 + P₁) ^ 2 / (1 + P₂) ≤ (1 + P₁) ^ 2 := by
  have hp : 0 < 1 + P₂ := by linarith
  constructor
  · rw [le_div_iff₀ hp]; nlinarith
  · rw [div_le_iff₀ hp]; nlinarith [sq_nonneg (1 + P₁)]

/-- The in-plane constant is at most twice the bulk-free ratio `Kper`. -/
theorem k_le_two_kper {Kper z z' : ℝ} (hK : 0 ≤ Kper) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hz' : 0 ≤ z') :
    Kper * ((1 + z) / 2) ^ 2 / ((1 + z') / 2) ≤ 2 * Kper := by
  have hp : 0 < (1 + z') / 2 := by linarith
  rw [div_le_iff₀ hp]
  have h1 : ((1 + z) / 2) ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hK]

/-- Telescoping: `f 0 - f n / 2^n = Σ_{k<n} (2 f k - f (k+1)) / 2^(k+1)`. -/
theorem log_z_telescope (f : ℕ → ℝ) (n : ℕ) :
    f 0 - f n / 2 ^ n = ∑ k ∈ Finset.range n, (2 * f k - f (k + 1)) / 2 ^ (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    field_simp
    ring

end UnifiedTheory.Clay.YangMills.Twisted.TwistedThermalExcess
