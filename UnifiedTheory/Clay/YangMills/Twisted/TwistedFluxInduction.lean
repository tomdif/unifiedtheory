/- The flux recursion as an induction on box size, with a MULTIPLICATIVE transverse step (abstract form).

`TwistedFluxThermal` showed the transverse doubling bound is additive, `y' ≤ 4y + κ`. Because `κ ≳ e^{-mL}` while
`y ~ e^{-σL²}`, an induction built on it gives at best a perimeter-type decay. This file isolates what a
multiplicative step needs, and what it buys.

* `F_double_le` (sector reduction). Along the doubled transverse direction, write the twist free energy as
  `F(t) = t Δ + D(t)`. Here `Δ ≥ 0` is the twisted-minus-untwisted ground-state gap and `D(t) = Φ_per(t) - Φ_tw(t)` is
  the difference of the two sectors' thermal excess free energies. If `D(2t) ≤ c D(t)` with `c ≥ 2` (no sign needed
  on D), then `F(2t) ≤ c F(t)`. This statement (S) about the excitation spectra of the two sectors is the one open
  input.
* `z_pow_of_F` and `transverse_mult`: with `z = e^{-F}`, `F' ≤ n F` gives `z' ≥ z^n`, and then
  `y' = (1 - z')/(1 + z') ≤ 2 n y`.
* `chain_step`: two in-plane steps `y ≤ K y²` and two multiplicative transverse steps give
  `y(2L) ≤ 4 n² K₁² K₂ y(L)⁴`. Only an upper bound on `K` is needed, not smallness, so the precision wall
  (κ resolved to the size of y) disappears.
* `area_law_iterate`: `y_{k+1} ≤ M y_k⁴` gives `M y_k³ ≤ (M y_0³)^(4^k)`. With `L_k = 2^k L_0`, `4^k = (L_k/L_0)²`,
  which is area-type decay of the flux ratio. Tomboulis–Yaffe then turns this into a Wilson-loop area law (cited, not
  formalized). The base case `M y_0³ < 1` is one finite-box condition.

The identification of `F, Δ, D, y, z, K` with lattice traces is by hand, as in `TwistedFluxRecursion` and
`TwistedFluxThermal`. Statement (S) is NOT proved here. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxInduction

/-- Sector reduction: `F(t) = tΔ + D(t)`, `F(2t) = 2tΔ + D(2t)`, `Δ, t ≥ 0`, `D(2t) ≤ c D(t)`, `c ≥ 2`
give `F(2t) ≤ c F(t)`. -/
theorem F_double_le {t Δ D₁ D₂ F₁ F₂ c : ℝ} (ht : 0 ≤ t) (hΔ : 0 ≤ Δ) (hc : 2 ≤ c)
    (hF₁ : F₁ = t * Δ + D₁) (hF₂ : F₂ = 2 * t * Δ + D₂) (hD₂ : D₂ ≤ c * D₁) :
    F₂ ≤ c * F₁ := by
  subst hF₁ hF₂
  have htΔ : 0 ≤ t * Δ := mul_nonneg ht hΔ
  nlinarith [mul_le_mul_of_nonneg_right hc htΔ]

/-- `F' ≤ n F` gives `e^{-F'} ≥ (e^{-F})^n`. -/
theorem z_pow_of_F {F F' : ℝ} (n : ℕ) (h : F' ≤ n * F) : Real.exp (-F) ^ n ≤ Real.exp (-F') := by
  rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; linarith

/-- Multiplicative transverse step: `0 ≤ z ≤ 1`, `0 ≤ z'`, `z' ≥ z^n` give
`(1 - z')/(1 + z') ≤ 2 n (1 - z)/(1 + z)`. -/
theorem transverse_mult {z z' : ℝ} (n : ℕ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hz'0 : 0 ≤ z') (h : z ^ n ≤ z') :
    (1 - z') / (1 + z') ≤ 2 * n * ((1 - z) / (1 + z)) := by
  have hb : 1 + (n : ℝ) * (z - 1) ≤ (1 + (z - 1)) ^ n :=
    one_add_mul_le_pow (by linarith) n
  simp only [add_sub_cancel] at hb
  have h1 : 1 - z' ≤ n * (1 - z) := by nlinarith
  have hpos : 0 < 1 + z := by linarith
  have hpos' : 0 < 1 + z' := by linarith
  have hy : (1 - z) / 2 ≤ (1 - z) / (1 + z) := by
    apply div_le_div_of_nonneg_left (by linarith) hpos (by linarith)
  have hl : (1 - z') / (1 + z') ≤ max (1 - z') 0 := by
    rcases le_total 0 (1 - z') with h0 | h0
    · rw [div_le_iff₀ hpos']; nlinarith [le_max_left (1 - z') 0]
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg h0 hpos'.le) (le_max_right _ _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmax : max (1 - z') 0 ≤ n * (1 - z) :=
    max_le h1 (mul_nonneg hn (by linarith))
  calc (1 - z') / (1 + z') ≤ n * (1 - z) := le_trans hl hmax
    _ = 2 * n * ((1 - z) / 2) := by ring
    _ ≤ 2 * n * ((1 - z) / (1 + z)) := mul_le_mul_of_nonneg_left hy (by positivity)

/-- One isotropic doubling: in-plane steps `y₁ ≤ K₁ y₀²`, `y₂ ≤ K₂ y₁²` and multiplicative transverse steps
`y₃ ≤ 2n y₂`, `y₄ ≤ 2n y₃` give `y₄ ≤ 4 n² K₁² K₂ y₀⁴`. -/
theorem chain_step {y₀ y₁ y₂ y₃ y₄ K₁ K₂ : ℝ} (n : ℕ) (hy₁ : 0 ≤ y₁) (hK₂ : 0 ≤ K₂)
    (h₁ : y₁ ≤ K₁ * y₀ ^ 2) (h₂ : y₂ ≤ K₂ * y₁ ^ 2) (h₃ : y₃ ≤ 2 * n * y₂) (h₄ : y₄ ≤ 2 * n * y₃) :
    y₄ ≤ 4 * n ^ 2 * K₁ ^ 2 * K₂ * y₀ ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : y₁ ^ 2 ≤ (K₁ * y₀ ^ 2) ^ 2 := pow_le_pow_left₀ hy₁ h₁ 2
  have h₂' : y₂ ≤ K₂ * (K₁ * y₀ ^ 2) ^ 2 := le_trans h₂ (mul_le_mul_of_nonneg_left hsq hK₂)
  have h₃' : y₃ ≤ 2 * n * (K₂ * (K₁ * y₀ ^ 2) ^ 2) :=
    le_trans h₃ (mul_le_mul_of_nonneg_left h₂' (by positivity))
  calc y₄ ≤ 2 * n * y₃ := h₄
    _ ≤ 2 * n * (2 * n * (K₂ * (K₁ * y₀ ^ 2) ^ 2)) := mul_le_mul_of_nonneg_left h₃' (by positivity)
    _ = 4 * n ^ 2 * K₁ ^ 2 * K₂ * y₀ ^ 4 := by ring

/-- Iteration: `0 ≤ y k`, `0 < M`, `y (k+1) ≤ M (y k)⁴` give `M (y k)³ ≤ (M (y 0)³)^(4^k)`. -/
theorem area_law_iterate (y : ℕ → ℝ) {M : ℝ} (hM : 0 < M) (hy : ∀ k, 0 ≤ y k)
    (hrec : ∀ k, y (k + 1) ≤ M * y k ^ 4) (k : ℕ) :
    M * y k ^ 3 ≤ (M * y 0 ^ 3) ^ (4 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hw : 0 ≤ M * y k ^ 3 := mul_nonneg hM.le (pow_nonneg (hy k) 3)
    have h3 : y (k + 1) ^ 3 ≤ (M * y k ^ 4) ^ 3 := pow_le_pow_left₀ (hy _) (hrec k) 3
    calc M * y (k + 1) ^ 3 ≤ M * (M * y k ^ 4) ^ 3 := mul_le_mul_of_nonneg_left h3 hM.le
      _ = (M * y k ^ 3) ^ 4 := by ring
      _ ≤ ((M * y 0 ^ 3) ^ (4 ^ k)) ^ 4 := pow_le_pow_left₀ hw ih 4
      _ = (M * y 0 ^ 3) ^ (4 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxInduction
