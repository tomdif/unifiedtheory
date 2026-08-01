/-
  Audit/KFCausalMAdicLaw.lean
  — THE M-ADIC MODULUS LAW, DIMENSION-BLIND

  For the Dowker–Glaser smeared weight of interval size k,

    W(k) = pref · ε · (1−ε)^k · Σ_i C_i · binom(k, i) · (ε/(1−ε))^i,

  with ANY integer coefficient system C (2D: (1, −2, 1) with pref = 2;
  4D: (1, −9, 16, −8) with pref = 1; any other dimension with integer
  weights) and rational smearing ε = p/m, the key identity is

    m^(k+1) · W(k) = pref · Σ_i C_i · binom(k, i) · p^(i+1) · (m−p)^(k−i),

  whose right side is an INTEGER.  Hence the denominator of the
  resonant per-link phase contribution c_k = 2q·W(k) divides m^(k+1):
  every congruence modulus of the resonant web at ε = p/m has prime
  support contained in the primes of m — the m-adic law
  (modulus_law.py, verified m = 3..12 in 2D; the 4D instance at
  ε = 1/4, φ = 8π gave the mod-16 web of closure_and_jurisdiction.py).
  The coefficient system C never enters the denominator: the law is
  dimension-blind.  (Dimensions with non-integer C, e.g. 3D with
  C₂ = −35/8, extend by multiplying through by the common denominator
  D: prime support ⊆ primes(m) ∪ primes(D).)

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalMAdicLaw

open Finset

/-- The smeared interval weight: pref · ε · (1−ε)^k · Σ C_i binom(k,i) x^i
with x = ε/(1−ε), coefficients C read as C 0, C 1, … (layer i). -/
noncomputable def smearedW (pref : ℤ) (C : ℕ → ℤ) (k : ℕ) (ε : ℚ) : ℚ :=
  (pref : ℚ) * ε * ((1 - ε) ^ k *
    ∑ i ∈ range (k + 1), (C i : ℚ) * (k.choose i : ℚ) * (ε / (1 - ε)) ^ i)

/-- **The m-adic numerator identity.**  At ε = p/m,
m^(k+1)·W(k) equals the integer
pref · Σ_i C_i · binom(k, i) · p^(i+1) · (m−p)^(k−i). -/
theorem madic_numerator (pref p m : ℤ) (C : ℕ → ℤ) (k : ℕ)
    (hm : (m : ℚ) ≠ 0) (hmp : (m : ℚ) - (p : ℚ) ≠ 0) :
    (m : ℚ) ^ (k + 1) * smearedW pref C k ((p : ℚ) / (m : ℚ))
      = ((pref * ∑ i ∈ range (k + 1),
          C i * (k.choose i : ℤ) * p ^ (i + 1) * (m - p) ^ (k - i) : ℤ) : ℚ) := by
  unfold smearedW
  have h1 : (1 : ℚ) - (p : ℚ) / (m : ℚ) = ((m : ℚ) - p) / m := by
    field_simp
  rw [h1]
  have h2 : ((p : ℚ) / m) / (((m : ℚ) - p) / m) = (p : ℚ) / ((m : ℚ) - p) := by
    field_simp
  rw [h2]
  push_cast
  rw [show ((m : ℚ) ^ (k + 1) * ((pref : ℚ) * ((p : ℚ) / m) *
      ((((m : ℚ) - p) / m) ^ k * ∑ i ∈ range (k + 1),
        (C i : ℚ) * (k.choose i : ℚ) * ((p : ℚ) / ((m : ℚ) - p)) ^ i)))
      = ((m : ℚ) ^ (k + 1) * (pref : ℚ) * ((p : ℚ) / m) *
        (((m : ℚ) - p) / m) ^ k) * ∑ i ∈ range (k + 1),
        (C i : ℚ) * (k.choose i : ℚ) * ((p : ℚ) / ((m : ℚ) - p)) ^ i
      from by ring]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [pow_sub₀ ((m : ℚ) - p) hmp hik, div_pow, div_pow]
  have e1 : ((m : ℚ) - p) ^ i ≠ 0 := pow_ne_zero _ hmp
  have e2 : (m : ℚ) ^ k ≠ 0 := pow_ne_zero _ hm
  field_simp
  ring

/-- **The m-adic law.**  The resonant per-link contribution
c_k = 2q·W(k) at ε = p/m has denominator dividing m^(k+1): there is an
integer z with m^(k+1)·c_k = z.  Every congruence modulus of the
resonant web is therefore supported on the primes of m, in every
dimension with integer weights. -/
theorem madic_law (pref p m q : ℤ) (C : ℕ → ℤ) (k : ℕ)
    (hm : (m : ℚ) ≠ 0) (hmp : (m : ℚ) - (p : ℚ) ≠ 0) :
    ∃ z : ℤ, (m : ℚ) ^ (k + 1)
      * (2 * (q : ℚ) * smearedW pref C k ((p : ℚ) / (m : ℚ))) = (z : ℚ) := by
  refine ⟨2 * q * (pref * ∑ i ∈ range (k + 1),
    C i * (k.choose i : ℤ) * p ^ (i + 1) * (m - p) ^ (k - i)), ?_⟩
  have h := madic_numerator pref p m C k hm hmp
  push_cast
  push_cast at h
  linear_combination (2 : ℚ) * (q : ℚ) * h

#print axioms madic_numerator
#print axioms madic_law

end UnifiedTheory.Audit.KFCausalMAdicLaw
