/- The flux-sector doubling inequality, in abstract form.

If `Z_e(t) = Σ λ^t` over the nonnegative eigenvalues of a positive operator in a sector, then
`Z_1(2t) ≤ Z_1(t)²`, so `y(2t) ≤ K(t) y(t)²` with `y = Z_1/Z_0` and `K(t) = Z_0(t)²/Z_0(2t)`.
Two doublings give the exponent 4 (`four_step`). A recursion `y' ≤ K y⁴` with `K y³ < 1` then decays doubly exponentially (`iterate_bound`).

None of this is tied to the lattice. The identification of `Z_0, Z_1` with sector traces of the periodic transfer operator is not formalized
here, and the constant `K` is not bounded. The twisted law itself is not reflection positive in direction 1 (`not_invariant_of_temporalFlux`);
the argument uses the periodic `T` with the center operator in the trace, and only `T ≥ 0`. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxRecursion

/-- A summable nonnegative family has sum of squares at most the square of the sum. -/
theorem tsum_sq_le {ι : Type*} (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (hs : Summable f) :
    ∑' i, f i ^ 2 ≤ (∑' i, f i) ^ 2 := by
  have hle : ∀ i, f i ≤ ∑' i, f i := fun i => hs.le_tsum i (fun j _ => h0 j)
  have hb : ∀ i, f i ^ 2 ≤ f i * ∑' i, f i := fun i => by
    rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (h0 i)
  by_cases hq : Summable (fun i => f i ^ 2)
  · calc ∑' i, f i ^ 2 ≤ ∑' i, f i * ∑' i, f i := hq.tsum_le_tsum hb (hs.mul_right _)
      _ = (∑' i, f i) ^ 2 := by rw [tsum_mul_right, sq]
  · rw [tsum_eq_zero_of_not_summable hq]; positivity

/-- The sector trace of `T^t`, from the eigenvalues in that sector. -/
noncomputable def sectorTrace {ι : Type*} (lam : ι → ℝ) (t : ℕ) : ℝ := ∑' i, lam i ^ t

theorem sectorTrace_double {ι : Type*} (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (t : ℕ)
    (hs : Summable fun i => lam i ^ t) :
    sectorTrace lam (2 * t) ≤ sectorTrace lam t ^ 2 := by
  have := tsum_sq_le (fun i => lam i ^ t) (fun i => pow_nonneg (h0 i) t) hs
  simpa [sectorTrace, pow_mul', pow_mul] using this

/-- One doubling. `A, A'` are `Z_1(t), Z_1(2t)` and `B, B'` are `Z_0(t), Z_0(2t)`. -/
theorem one_step {A A' B B' : ℝ} (hB : 0 < B) (hB' : 0 < B') (hA : A' ≤ A ^ 2) :
    A' / B' ≤ (B ^ 2 / B') * (A / B) ^ 2 := by
  have : (B ^ 2 / B') * (A / B) ^ 2 = A ^ 2 / B' := by field_simp
  rw [this]; exact div_le_div_of_nonneg_right hA hB'.le

/-- Two doublings give the exponent 4, with constant `K₁² K₂`. -/
theorem four_step {y y₁ y₂ K₁ K₂ : ℝ} (hy₁ : 0 ≤ y₁) (hK₂ : 0 ≤ K₂)
    (h₁ : y₁ ≤ K₁ * y ^ 2) (h₂ : y₂ ≤ K₂ * y₁ ^ 2) :
    y₂ ≤ K₁ ^ 2 * K₂ * y ^ 4 := by
  have : y₁ ^ 2 ≤ (K₁ * y ^ 2) ^ 2 := pow_le_pow_left₀ hy₁ h₁ 2
  calc y₂ ≤ K₂ * y₁ ^ 2 := h₂
    _ ≤ K₂ * (K₁ * y ^ 2) ^ 2 := mul_le_mul_of_nonneg_left this hK₂
    _ = K₁ ^ 2 * K₂ * y ^ 4 := by ring

/-- With a uniform constant `C = c³`, the recursion decays doubly exponentially once `c y₀ < 1`.
The uniform constant is a hypothesis. This is the open part. -/
theorem iterate_bound {y : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hy : ∀ k, 0 ≤ y k)
    (hstep : ∀ k, y (k + 1) ≤ c ^ 3 * y k ^ 4) (k : ℕ) :
    c * y k ≤ (c * y 0) ^ (4 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : c * y (k + 1) ≤ (c * y k) ^ 4 := by
      have := mul_le_mul_of_nonneg_left (hstep k) hc.le
      calc c * y (k + 1) ≤ c * (c ^ 3 * y k ^ 4) := this
        _ = (c * y k) ^ 4 := by ring
    have h2 : (c * y k) ^ 4 ≤ ((c * y 0) ^ (4 ^ k)) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hc.le (hy k)) ih 4
    calc c * y (k + 1) ≤ ((c * y 0) ^ (4 ^ k)) ^ 4 := h1.trans h2
      _ = (c * y 0) ^ (4 ^ (k + 1)) := by rw [← pow_mul, pow_succ 4 k]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxRecursion
