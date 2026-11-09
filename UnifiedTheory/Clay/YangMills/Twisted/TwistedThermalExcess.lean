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

* `flux_projection_le` and `kper_flux_split`: split `Z = Σ_e Z_e` over the 8 electric-flux sectors `e ∈ (ℤ₂)³`, with
  `Z_e = 2⁻³ Σ_m (-1)^{e·m} Z(m)` over spatial twists `m`. Since every `Z(m) ≥ 0`, each `Z_e ≤ Z_0` (elementary), so
  `S = Σ_{e≠0} Z_e/Z_0 ∈ [0, 7]` (using `Z_e ≥ 0`, sector positivity, cited). Then
  `Kper = K₀ (1+S(t))²/(1+S(2t))` lies in `[K₀/8, 64 K₀]`, where `K₀` is the zero-flux ratio. So `K̄` is a statement
  about the zero-flux spectrum only; the flux sectors cost at most a factor 64.

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

/-- A signed sum of nonnegative terms is at most the plain sum (the flux projection `Z_e ≤ Z_0`). -/
theorem flux_projection_le {ι : Type*} (s : Finset ι) (Z ε : ι → ℝ) (hZ : ∀ m ∈ s, 0 ≤ Z m)
    (hε : ∀ m ∈ s, ε m = 1 ∨ ε m = -1) : ∑ m ∈ s, ε m * Z m ≤ ∑ m ∈ s, Z m := by
  apply Finset.sum_le_sum; intro m hm
  rcases hε m hm with h | h <;> rw [h] <;> nlinarith [hZ m hm]

/-- Flux split: `Kper = K₀ (1+a)²/(1+b)` with `0 ≤ a, b ≤ s` lies in `[K₀/(1+s), K₀ (1+s)²]`. -/
theorem kper_flux_split {K₀ a b s : ℝ} (hK : 0 ≤ K₀) (ha : 0 ≤ a) (has : a ≤ s) (hb : 0 ≤ b) (hbs : b ≤ s) :
    K₀ / (1 + s) ≤ K₀ * (1 + a) ^ 2 / (1 + b) ∧ K₀ * (1 + a) ^ 2 / (1 + b) ≤ K₀ * (1 + s) ^ 2 := by
  have hb1 : 0 < 1 + b := by linarith
  have hs1 : 0 < 1 + s := by linarith
  have h1 : 1 ≤ (1 + a) ^ 2 := by nlinarith
  have h2 : (1 + a) ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
  constructor
  · rw [div_le_div_iff₀ hs1 hb1]
    nlinarith [mul_le_mul_of_nonneg_left h1 hK, mul_nonneg hK (sub_nonneg.mpr hbs)]
  · rw [div_le_iff₀ hb1]
    nlinarith [mul_le_mul_of_nonneg_left h2 hK, mul_nonneg hK (sq_nonneg (1 + s)), mul_nonneg (mul_nonneg hK (sq_nonneg (1 + s))) hb]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedThermalExcess
