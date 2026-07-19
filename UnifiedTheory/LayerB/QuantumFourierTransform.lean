/-
# The Quantum Fourier Transform is Unitary

This module formalizes the Quantum Fourier Transform (QFT) matrix on `ℂ^N`,
```
  F_{jk} = (1/√N) · ω^{jk},   ω = exp(2πi/N),
```
and proves the headline fact that it is **unitary**: `Fᴴ * F = 1`.

The mathematical crux is **root-of-unity orthogonality**.  Writing
`ζ = conj(ω^j) · ω^l` for the (j,l) entry of `Fᴴ * F`, we get a pure geometric
sum `(1/N) ∑_{k<N} ζ^k`, and:

* if `j = l` then `ζ = |ω^j|² = 1` so the sum is `N`, giving `1` after the `1/N`;
* if `j ≠ l` then `ζ ≠ 1` while `ζ^N = 1`, so the geometric series
  `∑_{k<N} ζ^k = (ζ^N - 1)/(ζ - 1) = 0`.

Everything is proved unconditionally (`N ≥ 1`) for **general** `N`, reusing
Mathlib's primitive-root machinery (`Complex.isPrimitiveRoot_exp`) and the
finite geometric sum `geom_sum_eq`.

Zero `sorry`, zero custom `axiom`.
-/
import Mathlib

open Complex Finset
open scoped BigOperators Matrix

namespace UnifiedTheory.LayerB.QuantumFourierTransform

noncomputable section

/-! ## The primitive root of unity `ω = exp(2πi/N)` -/

/-- The primitive `N`-th root of unity `ω = exp(2πi/N)`. -/
noncomputable def omega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- `ω` is a primitive `N`-th root of unity (Mathlib's `isPrimitiveRoot_exp`). -/
theorem omega_isPrimitiveRoot (N : ℕ) (hN : 0 < N) :
    IsPrimitiveRoot (omega N) N := by
  have h : omega N = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N) := rfl
  rw [h]
  exact Complex.isPrimitiveRoot_exp N hN.ne'

/-- `ωᴺ = 1`. -/
theorem omega_pow_N (N : ℕ) (hN : 0 < N) : (omega N) ^ N = 1 :=
  (omega_isPrimitiveRoot N hN).pow_eq_one

/-- `ω` has modulus one. -/
theorem omega_norm (N : ℕ) (hN : 0 < N) : ‖omega N‖ = 1 := by
  have h : omega N = Complex.exp (2 * Real.pi * Complex.I / N) := rfl
  rw [h]
  -- write the argument as `x * I` with `x : ℝ` and use `norm_exp_ofReal_mul_I`.
  have hrw : (2 : ℂ) * Real.pi * Complex.I / N
      = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrw, Complex.norm_exp_ofReal_mul_I]

/-- Powers of `ω` have modulus one. -/
theorem omega_pow_norm (N : ℕ) (hN : 0 < N) (a : ℕ) : ‖(omega N) ^ a‖ = 1 := by
  rw [norm_pow, omega_norm N hN, one_pow]

/-- `ω ≠ 0`. -/
theorem omega_ne_zero (N : ℕ) (hN : 0 < N) : omega N ≠ 0 := by
  intro h
  have := omega_norm N hN
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-- `conj(ω^a) · ω^a = 1`, i.e. powers of `ω` are unitary scalars. -/
theorem conj_omega_pow_mul (N : ℕ) (hN : 0 < N) (a : ℕ) :
    (starRingEnd ℂ) ((omega N) ^ a) * (omega N) ^ a = 1 := by
  have h : (starRingEnd ℂ) ((omega N) ^ a) * (omega N) ^ a
      = (↑(Complex.normSq ((omega N) ^ a)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [h, Complex.normSq_eq_norm_sq, omega_pow_norm N hN]
  norm_num

/-! ## The QFT matrix -/

/-- The Quantum Fourier Transform matrix `F_{jk} = (1/√N) · ω^{jk}`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (1 / (Real.sqrt N : ℂ)) * (omega N) ^ ((j : ℕ) * (k : ℕ))

/-- Each QFT entry has modulus `1/√N`. -/
theorem qftMatrix_entry_norm (N : ℕ) (hN : 0 < N) (j k : Fin N) :
    ‖qftMatrix N j k‖ = 1 / Real.sqrt N := by
  unfold qftMatrix
  rw [norm_mul, omega_pow_norm N hN, mul_one, norm_div, norm_one]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ## Root-of-unity orthogonality (the crux) -/

/-- `ζ := conj(ω^j) · ω^l` is the base of the geometric sum for entry `(j,l)`.

    The diagonal case `j = l` gives `ζ = 1`. -/
theorem zeta_diag (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (j : ℕ) = 1 :=
  conj_omega_pow_mul N hN (j : ℕ)

/-- The base `ζ = conj(ω^j) · ω^l` is an `N`-th root of unity. -/
theorem zeta_pow_N (N : ℕ) (hN : 0 < N) (j l : Fin N) :
    ((starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (l : ℕ)) ^ N = 1 := by
  rw [mul_pow]
  rw [← map_pow, ← pow_mul, ← pow_mul]
  rw [mul_comm (j : ℕ) N, mul_comm (l : ℕ) N, pow_mul, pow_mul]
  rw [omega_pow_N N hN, one_pow, one_pow, map_one, mul_one]

/-- Off-diagonal: when `j ≠ l`, the base `ζ = conj(ω^j) · ω^l ≠ 1`.

    Indeed `ζ = ω^l / ω^j` (since `conj(ω^j) = (ω^j)⁻¹`), and `ω^l = ω^j`
    would force `j = l` by primitivity of `ω`. -/
theorem zeta_ne_one (N : ℕ) (hN : 0 < N) (j l : Fin N) (hjl : j ≠ l) :
    (starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (l : ℕ) ≠ 1 := by
  -- `conj(ω^j) = (ω^j)⁻¹` because `conj(ω^j) · ω^j = 1`.
  have hinv : (starRingEnd ℂ) ((omega N) ^ (j : ℕ)) = ((omega N) ^ (j : ℕ))⁻¹ := by
    have h1 := conj_omega_pow_mul N hN (j : ℕ)
    have hne : (omega N) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (omega_ne_zero N hN)
    field_simp at h1 ⊢
    rw [h1]
  intro hcontra
  rw [hinv] at hcontra
  -- `(ω^j)⁻¹ · ω^l = 1` ⇒ `ω^l = ω^j`.
  have hne : (omega N) ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (omega_ne_zero N hN)
  have heq : (omega N) ^ (l : ℕ) = (omega N) ^ (j : ℕ) := by
    field_simp at hcontra
    linear_combination hcontra
  -- primitivity ⇒ `l = j`.
  have := (omega_isPrimitiveRoot N hN).pow_inj l.isLt j.isLt heq
  exact hjl (Fin.ext this.symm)

/-- **Root-of-unity orthogonality / geometric sum.**

    For the (j,l) base `ζ = conj(ω^j) · ω^l`:
    `∑_{k<N} ζ^k = N` if `j = l`, and `= 0` if `j ≠ l`. -/
theorem rootSum (N : ℕ) (hN : 0 < N) (j l : Fin N) :
    ∑ k : Fin N,
        ((starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (l : ℕ)) ^ (k : ℕ)
      = if j = l then (N : ℂ) else 0 := by
  set ζ : ℂ := (starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (l : ℕ) with hζ
  -- Re-index the `Fin N` sum as a `range N` sum of `ζ^k`.
  have hsum : ∑ k : Fin N, ζ ^ (k : ℕ) = ∑ k ∈ Finset.range N, ζ ^ k := by
    rw [Finset.sum_range fun k => ζ ^ k]
  rw [hsum]
  by_cases hjl : j = l
  · -- diagonal: ζ = 1, sum of ones is N.
    have hone : ζ = 1 := by
      rw [hζ, hjl]; exact zeta_diag N hN l
    rw [hone]
    simp [hjl]
  · -- off-diagonal: ζ ≠ 1, ζ^N = 1, geometric series telescopes to 0.
    have hζne : ζ ≠ 1 := by rw [hζ]; exact zeta_ne_one N hN j l hjl
    have hζN : ζ ^ N = 1 := by rw [hζ]; exact zeta_pow_N N hN j l
    rw [geom_sum_eq hζne N, hζN]
    simp [hjl]

/-! ## Unitarity of the QFT -/

/-- **The QFT matrix is unitary:** `Fᴴ * F = 1`.

    `(Fᴴ * F)_{j,l} = ∑_k conj(F_{k,j}) · F_{k,l}
        = (1/N) ∑_k conj(ω^{kj}) · ω^{kl}
        = (1/N) ∑_k (conj(ω^j) · ω^l)^k
        = (1/N) · (N · δ_{jl}) = δ_{jl}.` -/
theorem qftMatrix_unitary (N : ℕ) (hN : 0 < N) :
    (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext j l
  rw [Matrix.mul_apply]
  -- expand each summand.
  have hsqrt_pos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsqrt_ne : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsqrt_pos)
  have hsqrt_sq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    have : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    exact_mod_cast this
  -- Rewrite the matrix product entry as (1/N) ∑_k ζ^k.
  have hentry : ∀ k : Fin N,
      (qftMatrix N)ᴴ j k * qftMatrix N k l
        = (1 / (N : ℂ)) *
          ((starRingEnd ℂ) ((omega N) ^ (j : ℕ)) * (omega N) ^ (l : ℕ)) ^ (k : ℕ) := by
    intro k
    -- Expand the conjugate transpose entry and the matrix entries.
    simp only [Matrix.conjTranspose_apply, qftMatrix, star_mul', star_div₀, star_one]
    -- conj of the real scalar `√N` (and of `ω^{kj}`).
    have hreal : star ((Real.sqrt N : ℂ)) = (Real.sqrt N : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hconjpow : star ((omega N) ^ ((k : ℕ) * (j : ℕ)))
        = (starRingEnd ℂ) ((omega N) ^ (j : ℕ)) ^ (k : ℕ) := by
      rw [Complex.star_def, ← map_pow, ← pow_mul, Nat.mul_comm]
    rw [hreal, hconjpow]
    -- rewrite `ω^{kl} = (ω^l)^k` and split the RHS power.
    have hpow_kl : (omega N) ^ ((k : ℕ) * (l : ℕ)) = ((omega N) ^ (l : ℕ)) ^ (k : ℕ) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpow_kl, mul_pow]
    -- both sides now share the factor `(conj(ω^j))^k * (ω^l)^k`; reduce scalars.
    rw [show (1 / (N : ℂ))
          = (1 / (Real.sqrt N : ℂ)) * (1 / (Real.sqrt N : ℂ)) by
        rw [div_mul_div_comm, one_mul, ← hsqrt_sq]]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hentry k)]
  rw [← Finset.mul_sum]
  rw [rootSum N hN j l]
  -- finish: 1/N * (if j=l then N else 0) = (1 : Matrix ...) j l.
  rw [Matrix.one_apply]
  by_cases hjl : j = l
  · rw [if_pos hjl, if_pos hjl, one_div, inv_mul_cancel₀]
    exact_mod_cast (ne_of_gt hN)
  · rw [if_neg hjl, if_neg hjl, mul_zero]

/-! ## Inverse QFT statement -/

/-- The inverse QFT is the conjugate transpose: `Fᴴ` is a left inverse of `F`. -/
def QFT_Inverse_Target (N : ℕ) : Prop :=
  (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ)

/-- `Fᴴ` is indeed the inverse of `F` (for `N ≥ 1`). -/
theorem qft_inverse (N : ℕ) (hN : 0 < N) : QFT_Inverse_Target N :=
  qftMatrix_unitary N hN

/-! ## Small explicit cases -/

/-- For `N = 1`, the QFT is the `1×1` identity. -/
theorem qft_one_eq_one : qftMatrix 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext j k
  fin_cases j; fin_cases k
  simp only [qftMatrix, Matrix.one_apply_eq]
  norm_num

/-- For `N = 2`, the QFT is the Hadamard gate `(1/√2)·[[1,1],[1,-1]]`.
    Here `ω = exp(πi) = -1`, so `F_{11} = (1/√2)·ω = -1/√2`. -/
theorem qft_two_omega : omega 2 = -1 := by
  unfold omega
  have : (2 : ℂ) * Real.pi * Complex.I / (2 : ℕ) = Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

/-- The (1,1) entry of the `N = 2` QFT equals `-1/√2`, i.e. the Hadamard sign. -/
theorem qft_two_hadamard_sign :
    qftMatrix 2 ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ = -(1 / (Real.sqrt 2 : ℂ)) := by
  simp only [qftMatrix]
  rw [qft_two_omega]
  norm_num

/-- The `N = 2` QFT is unitary (special case of the general theorem). -/
theorem qft_two_unitary :
    (qftMatrix 2)ᴴ * qftMatrix 2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  qftMatrix_unitary 2 (by norm_num)

/-! ## Master theorem -/

/-- **Master theorem.**  The QFT matrix `F_{jk} = (1/√N) ω^{jk}` on `ℂ^N` is
    unitary for every `N ≥ 1`: its conjugate transpose is a left inverse,
    each entry has modulus `1/√N`, and `ω = exp(2πi/N)` is a primitive `N`-th
    root of unity with `ωᴺ = 1`. -/
theorem qft_master (N : ℕ) (hN : 0 < N) :
    IsPrimitiveRoot (omega N) N ∧
    (omega N) ^ N = 1 ∧
    ‖omega N‖ = 1 ∧
    (∀ j k : Fin N, ‖qftMatrix N j k‖ = 1 / Real.sqrt N) ∧
    (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ) :=
  ⟨omega_isPrimitiveRoot N hN, omega_pow_N N hN, omega_norm N hN,
   qftMatrix_entry_norm N hN, qftMatrix_unitary N hN⟩

end

end UnifiedTheory.LayerB.QuantumFourierTransform
