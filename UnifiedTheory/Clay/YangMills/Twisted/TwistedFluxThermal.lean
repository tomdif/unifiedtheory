/- What the flux-recursion constant is, and what transverse doubling costs (abstract form).

`TwistedFluxRecursion` gives `y(2t) ≤ K y(t)²` with `K = Z_0(t)²/Z_0(2t)` and leaves `K` unbounded.
Normalize the sector eigenvalues by the top one, so `0 ≤ λ_i ≤ 1` with some `λ_{i₀} = 1`, and write
`S(t) = Σ λ_i^t = exp Φ(t)`. `Φ(t) = log Σ exp(-t (E_i - E_0))` is the thermal excess free energy of the box at
temperature `1/t` (its pressure times volume over temperature, vacuum subtracted).

* `thermal_two_sided`: `S(t) ≤ K ≤ S(t)²`, i.e. `Φ(t) ≤ log K ≤ 2 Φ(t)`. A uniform bound on `K` is therefore
  equivalent to a uniform bound on the thermal free energy of the box at temperature of order its inverse size, a
  Stefan-Boltzmann-type statement that holds in a massless phase too. `K → 1` iff the box is cold, `Φ → 0`.
* `transverse_ratio`, `transverse_y`, `transverse_y_linear`: doubling a direction transverse to the flux plane, viewed
  as the time of the twisted (magnetic-sector) transfer operator, gives `z' ≥ z²/K_B` and so
  `y' ≤ (K_B - z²)/(K_B + z²) ≤ 4 y + κ` with `K_B = 1 + κ` the same thermal constant for that sector.

So a transverse doubling can only be controlled when `κ`, the box thermal free energy, is small: a cold box, i.e. a
gap at that scale of order `log(volume)/size`. The identification of `A, B, A', B'` with lattice traces is by hand,
as in `TwistedFluxRecursion`. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxThermal

/-- Pure form: if `1 ≤ S₂ ≤ S₁` then `S₁ ≤ S₁²/S₂ ≤ S₁²`. -/
theorem two_sided_of {S₁ S₂ : ℝ} (h1 : 1 ≤ S₂) (h2 : S₂ ≤ S₁) :
    S₁ ≤ S₁ ^ 2 / S₂ ∧ S₁ ^ 2 / S₂ ≤ S₁ ^ 2 := by
  have hS₂ : 0 < S₂ := lt_of_lt_of_le one_pos h1
  have hS₁ : 0 < S₁ := lt_of_lt_of_le hS₂ h2
  constructor
  · rw [le_div_iff₀ hS₂]; nlinarith
  · rw [div_le_iff₀ hS₂]; nlinarith [sq_nonneg S₁]

/-- Spectral form: eigenvalues in `[0,1]` with a top eigenvalue `1`. Then `K = S(t)²/S(2t)` lies in
`[S(t), S(t)²]`. -/
theorem thermal_two_sided {ι : Type*} (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1)
    (i₀ : ι) (htop : lam i₀ = 1) (t : ℕ) (hs : Summable fun i => lam i ^ t) :
    (∑' i, lam i ^ t) ≤ (∑' i, lam i ^ t) ^ 2 / (∑' i, lam i ^ (2 * t)) ∧
      (∑' i, lam i ^ t) ^ 2 / (∑' i, lam i ^ (2 * t)) ≤ (∑' i, lam i ^ t) ^ 2 := by
  have hle : ∀ i, lam i ^ (2 * t) ≤ lam i ^ t := fun i =>
    pow_le_pow_of_le_one (h0 i) (h1 i) (by omega)
  have hnn : ∀ i, 0 ≤ lam i ^ (2 * t) := fun i => pow_nonneg (h0 i) _
  have hs2 : Summable fun i => lam i ^ (2 * t) := hs.of_nonneg_of_le hnn hle
  have hS2le : (∑' i, lam i ^ (2 * t)) ≤ ∑' i, lam i ^ t := hs2.tsum_le_tsum hle hs
  have hone : (1 : ℝ) ≤ ∑' i, lam i ^ (2 * t) := by
    have := hs2.le_tsum i₀ (fun j _ => hnn j)
    simpa [htop] using this
  exact two_sided_of hone hS2le

/-- Transverse doubling, ratio form: `A' ≤ A²` (untwisted sector, `sectorTrace_double`) and `B² ≤ K B'`
(twisted sector, definition of its thermal constant) give `z' = B'/A' ≥ (B/A)²/K`. -/
theorem transverse_ratio {A A' B B' K : ℝ} (hA : 0 < A) (hA' : 0 < A') (hK : 0 < K)
    (hAA : A' ≤ A ^ 2) (hBB : B ^ 2 ≤ K * B') :
    (B / A) ^ 2 / K ≤ B' / A' := by
  have hKB : 0 ≤ K * B' := le_trans (sq_nonneg B) hBB
  rw [div_pow, div_div, div_le_div_iff₀ (by positivity) hA']
  calc B ^ 2 * A' ≤ (K * B') * A ^ 2 := mul_le_mul hBB hAA hA'.le hKB
    _ = B' * (A ^ 2 * K) := by ring

/-- `y = (1 - z)/(1 + z)` is decreasing in `z ≥ 0`, so `z' ≥ z²/K` gives `y' ≤ (K - z²)/(K + z²)`. -/
theorem transverse_y {z z' K : ℝ} (hK : 0 < K) (hz' : z ^ 2 / K ≤ z') :
    (1 - z') / (1 + z') ≤ (K - z ^ 2) / (K + z ^ 2) := by
  have hw : 0 ≤ z ^ 2 / K := div_nonneg (sq_nonneg z) hK.le
  have hpos : 0 < 1 + z' := by linarith
  have hKz : 0 < K + z ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos hKz]
  have : z ^ 2 ≤ K * z' := by rwa [div_le_iff₀ hK, mul_comm] at hz'
  nlinarith

/-- Linear form: with `z = (1 - y)/(1 + y)`, `y ≥ 0` and `K = 1 + κ`, `κ ≥ 0`, the bound is at most `4 y + κ`. -/
theorem transverse_y_linear {y κ : ℝ} (hy : 0 ≤ y) (hκ : 0 ≤ κ) :
    ((1 + κ) - ((1 - y) / (1 + y)) ^ 2) / ((1 + κ) + ((1 - y) / (1 + y)) ^ 2) ≤ 4 * y + κ := by
  set z := (1 - y) / (1 + y) with hz
  have hy1 : 0 < 1 + y := by linarith
  have h1z : 1 - z ^ 2 = 4 * y / (1 + y) ^ 2 := by
    rw [hz]; field_simp; ring
  have h4 : 1 - z ^ 2 ≤ 4 * y := by
    rw [h1z, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hy (by nlinarith : (0:ℝ) ≤ 2 * y + y ^ 2)]
  have hden : 1 ≤ (1 + κ) + z ^ 2 := by nlinarith [sq_nonneg z]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg z, mul_nonneg (by linarith : (0:ℝ) ≤ 4 * y + κ) (by nlinarith [sq_nonneg z] : (0:ℝ) ≤ κ + z ^ 2)]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxThermal
