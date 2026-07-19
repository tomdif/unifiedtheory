/-
  LayerB/LieTrotterProduct.lean
  ─────────────────────────────

  **The Lie product (Trotter) formula for the Banach-algebra exponential.**

      `(NormedSpace.exp (A/n) · NormedSpace.exp (B/n))^n  →  NormedSpace.exp (A + B)`.

  This is the single irreducible analytic core that the whole
  Golden–Thompson → Lieb-1973 → strong-subadditivity chain bottoms out on,
  in the CFC-stripped form `LieTrotter_NormedExp_Target` proved in
  `LiebSubgateProgress.lean`.

  Mathlib provides **no** Lie/Trotter product formula and **no**
  Banach-algebra-level remainder bound for `NormedSpace.exp` (only the
  scalar `ℂ`/`ℝ` versions `Complex.norm_exp_sub_one_sub_id_le`).  So we
  build the genuine analytic estimates here from the power series.

  ## What is proven here (zero `sorry`, zero custom axiom)

    * `norm_exp_sub_one_le`        — `‖exp x − 1‖ ≤ ‖x‖ · Real.exp ‖x‖`
                                       in any complete normed `ℝ`-algebra.
    * `norm_exp_sub_one_sub_le`    — `‖exp x − 1 − x‖ ≤ ‖x‖² · Real.exp ‖x‖`.
    * `norm_expMul_sub_one_sub_add_le`
                                   — `‖exp a · exp b − 1 − a − b‖` quadratic.
    * `telescope_norm_pow_sub_pow` — `‖x^n − y^n‖ ≤ n · M^{n-1} · ‖x−y‖`
                                       (`M = max ‖x‖ ‖y‖`) in a normed ring.
    * `Tn_pow_eq`                  — `(exp ((1/n)•(A+B)))^n = exp (A+B)`.
    * `lieTrotter_normedExp`       — the **full Lie product formula**.
    * `LieTrotter_NormedExp_Target_holds`
                                   — discharges the named target.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-02.
-/

import UnifiedTheory.LayerB.LiebSubgateProgress
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 1000000

namespace UnifiedTheory.LayerB.LieTrotterProduct

open Filter Topology NormedSpace
open scoped Nat

/-! ## 1. Banach-algebra remainder bounds for the exponential.

We work in an arbitrary complete normed `ℝ`-algebra `𝔸`.  The two bounds
below are the quantitative content Mathlib is missing at this generality. -/

section Remainder

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `Real.exp t = ∑' n, t^n / n!`. -/
private lemma real_exp_eq_tsum_div (t : ℝ) :
    Real.exp t = ∑' n : ℕ, t ^ n / n ! := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) t

/-- The exponential series for `x`, written as `∑' n, (n!)⁻¹ • x^n`, sums to
    `exp x`. -/
private lemma exp_hasSum (x : 𝔸) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • x ^ n) (NormedSpace.exp x) :=
  NormedSpace.exp_series_hasSum_exp' x

/-- `HasSum` form of `Real.exp ‖x‖ = ∑' n, ‖x‖^n / n!`. -/
private lemma real_exp_norm_hasSum (x : 𝔸) :
    HasSum (fun n : ℕ => ‖x‖ ^ n / n !) (Real.exp ‖x‖) := by
  have h := (Real.summable_pow_div_factorial ‖x‖).hasSum
  rwa [← real_exp_eq_tsum_div ‖x‖] at h

/-- **First remainder bound.**  `‖exp x − 1‖ ≤ ‖x‖ · Real.exp ‖x‖`. -/
theorem norm_exp_sub_one_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  -- exp x − 1 = ∑' n, (1/(n+1)!) • x^(n+1)
  have hsplit : NormedSpace.exp x - 1
      = ∑' n : ℕ, ((n + 1)!⁻¹ : ℝ) • x ^ (n + 1) := by
    have hsum := exp_hasSum x
    rw [← hsum.tsum_eq,
        (NormedSpace.expSeries_summable' (𝕂 := ℝ) x).tsum_eq_zero_add]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
      add_sub_cancel_left]
  rw [hsplit]
  -- termwise bound by ‖x‖ * (‖x‖^n / n!)
  refine tsum_of_norm_bounded
    (g := fun n : ℕ => ‖x‖ * (‖x‖ ^ n / n !))
    (a := ‖x‖ * Real.exp ‖x‖) ?_ ?_
  · exact (real_exp_norm_hasSum x).mul_left ‖x‖
  · intro n
    rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((n + 1)! : ℝ))⁻¹)]
    have hpow : ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_pow_le' x (Nat.succ_pos n)
    have hfac : (((n + 1)! : ℝ))⁻¹ ≤ ((n ! : ℝ))⁻¹ := by
      have h1 : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have h2 : (n ! : ℝ) ≤ ((n + 1)! : ℝ) := by
        exact_mod_cast Nat.factorial_le (Nat.le_succ n)
      rw [inv_le_inv₀ (by exact_mod_cast Nat.factorial_pos (n + 1)) h1]
      exact h2
    calc (((n + 1)! : ℝ))⁻¹ * ‖x ^ (n + 1)‖
        ≤ ((n ! : ℝ))⁻¹ * ‖x‖ ^ (n + 1) := by
          apply mul_le_mul hfac hpow (norm_nonneg _) (by positivity)
      _ = ‖x‖ * (‖x‖ ^ n / n !) := by
          rw [pow_succ]; ring

/-- **Second remainder bound.**  `‖exp x − 1 − x‖ ≤ ‖x‖² · Real.exp ‖x‖`. -/
theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  -- exp x − 1 − x = ∑' n, (1/(n+2)!) • x^(n+2)
  -- `g n = (1/(n+1)!) • x^(n+1)`; `∑' g = exp x - 1`, `g 0 = x`.
  set g : ℕ → 𝔸 := fun n => (((n + 1)! : ℝ))⁻¹ • x ^ (n + 1) with hg
  have hgsummable : Summable g := by
    have hsummable := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
    have := (hsummable.comp_injective (add_left_injective 1))
    simpa [hg, Function.comp] using this
  have hgtsum : ∑' n, g n = NormedSpace.exp x - 1 := by
    have hsum := exp_hasSum x
    rw [← hsum.tsum_eq, (NormedSpace.expSeries_summable' (𝕂 := ℝ) x).tsum_eq_zero_add]
    simp only [hg, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
      add_sub_cancel_left]
  have hg0 : g 0 = x := by
    simp [hg]
  have hsplit : NormedSpace.exp x - 1 - x
      = ∑' n : ℕ, (((n + 2)! : ℝ))⁻¹ • x ^ (n + 2) := by
    rw [← hgtsum, hgsummable.tsum_eq_zero_add, hg0]
    simp only [add_sub_cancel_left, hg]
  rw [hsplit]
  refine tsum_of_norm_bounded
    (g := fun n : ℕ => ‖x‖ ^ 2 * (‖x‖ ^ n / n !))
    (a := ‖x‖ ^ 2 * Real.exp ‖x‖) ?_ ?_
  · exact (real_exp_norm_hasSum x).mul_left (‖x‖ ^ 2)
  · intro n
    rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((n + 2)! : ℝ))⁻¹)]
    have hpow : ‖x ^ (n + 2)‖ ≤ ‖x‖ ^ (n + 2) := norm_pow_le' x (by positivity)
    have hfac : (((n + 2)! : ℝ))⁻¹ ≤ ((n ! : ℝ))⁻¹ := by
      have h1 : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have h2 : (n ! : ℝ) ≤ ((n + 2)! : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 2)
      rw [inv_le_inv₀ (by exact_mod_cast Nat.factorial_pos (n + 2)) h1]
      exact h2
    calc (((n + 2)! : ℝ))⁻¹ * ‖x ^ (n + 2)‖
        ≤ ((n ! : ℝ))⁻¹ * ‖x‖ ^ (n + 2) := by
          apply mul_le_mul hfac hpow (norm_nonneg _) (by positivity)
      _ = ‖x‖ ^ 2 * (‖x‖ ^ n / n !) := by
          rw [pow_add]; ring

end Remainder

/-! ## 2. The quadratic cross-term bound.

`‖exp a · exp b − 1 − a − b‖` is `O((‖a‖+‖b‖)²)`, using the algebraic
identity
  `exp a · exp b − 1 − a − b
      = (exp a − 1)(exp b − 1) + (exp a − 1 − a) + (exp b − 1 − b)`. -/

section CrossTerm

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Algebraic identity underlying the cross-term bound. -/
private lemma expMul_decomp (a b : 𝔸) :
    NormedSpace.exp a * NormedSpace.exp b - 1 - a - b
      = (NormedSpace.exp a - 1) * (NormedSpace.exp b - 1)
        + (NormedSpace.exp a - 1 - a) + (NormedSpace.exp b - 1 - b) := by
  noncomm_ring

/-- **Cross-term bound.**
    `‖exp a · exp b − 1 − a − b‖
        ≤ ‖a‖·e^{‖a‖}·‖b‖·e^{‖b‖} + ‖a‖²·e^{‖a‖} + ‖b‖²·e^{‖b‖}`. -/
theorem norm_expMul_sub_one_sub_add_le (a b : 𝔸) :
    ‖NormedSpace.exp a * NormedSpace.exp b - 1 - a - b‖
      ≤ (‖a‖ * Real.exp ‖a‖) * (‖b‖ * Real.exp ‖b‖)
        + ‖a‖ ^ 2 * Real.exp ‖a‖ + ‖b‖ ^ 2 * Real.exp ‖b‖ := by
  rw [expMul_decomp a b]
  refine (norm_add₃_le).trans ?_
  gcongr
  · exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_sub_one_le b)
        (norm_nonneg _) (by positivity))
  · exact norm_exp_sub_one_sub_le a
  · exact norm_exp_sub_one_sub_le b

end CrossTerm

/-! ## 3. The telescoping (geometric) bound in a normed ring.

`‖x^(n+1) − y^(n+1)‖ ≤ (n+1) · M^n · ‖x − y‖` where `M = max ‖x‖ ‖y‖`,
proved by induction via `x^(k+1) − y^(k+1) = x(x^k − y^k) + (x − y)y^k`. -/

section Telescope

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- **Telescoping bound.**  `‖x^(n+1) − y^(n+1)‖ ≤ (n+1)·M^n·‖x−y‖`,
    `M = max ‖x‖ ‖y‖`. -/
theorem telescope_norm_pow_sub_pow (x y : 𝔸) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖
      ≤ (n + 1 : ℝ) * (max ‖x‖ ‖y‖) ^ n * ‖x - y‖ := by
  set M : ℝ := max ‖x‖ ‖y‖ with hM
  have hxM : ‖x‖ ≤ M := le_max_left _ _
  have hyM : ‖y‖ ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg x) hxM
  induction n with
  | zero => simp
  | succ k ih =>
    have hid : x ^ (k + 1 + 1) - y ^ (k + 1 + 1)
        = x * (x ^ (k + 1) - y ^ (k + 1)) + (x - y) * y ^ (k + 1) := by
      have e1 : x ^ (k + 1 + 1) = x * x ^ (k + 1) := by rw [pow_succ']
      have e2 : y ^ (k + 1 + 1) = y * y ^ (k + 1) := by rw [pow_succ']
      rw [e1, e2, mul_sub, sub_mul]
      abel
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    have hbound1 : ‖x * (x ^ (k + 1) - y ^ (k + 1))‖
        ≤ M * ((k + 1 : ℝ) * M ^ k * ‖x - y‖) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul hxM ih (norm_nonneg _) hM0
    have hbound2 : ‖(x - y) * y ^ (k + 1)‖ ≤ ‖x - y‖ * M ^ (k + 1) := by
      refine (norm_mul_le _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_pow_le' y (Nat.succ_pos k)).trans ?_
      exact pow_le_pow_left₀ (norm_nonneg _) hyM _
    refine (add_le_add hbound1 hbound2).trans ?_
    have : M * ((k + 1 : ℝ) * M ^ k * ‖x - y‖) + ‖x - y‖ * M ^ (k + 1)
        = ((k + 1 : ℝ) + 1) * M ^ (k + 1) * ‖x - y‖ := by
      rw [pow_succ]; ring
    rw [this]
    apply le_of_eq
    push_cast
    ring

/-- Telescoping bound for `k ≥ 1`: `‖x^k − y^k‖ ≤ k·M^(k−1)·‖x−y‖`. -/
theorem telescope_norm_pow_sub_pow' (x y : 𝔸) {k : ℕ} (hk : 1 ≤ k) :
    ‖x ^ k - y ^ k‖
      ≤ (k : ℝ) * (max ‖x‖ ‖y‖) ^ (k - 1) * ‖x - y‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have := telescope_norm_pow_sub_pow x y m
  simpa using this

end Telescope

/-! ## 4. Submultiplicative norm bound `‖exp x‖ ≤ Real.exp ‖x‖`. -/

section NormExp

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

/-- `‖exp x‖ ≤ Real.exp ‖x‖`. -/
theorem norm_exp_le (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hsum : HasSum (fun n : ℕ => ‖x‖ ^ n / n !) (Real.exp ‖x‖) :=
    real_exp_norm_hasSum x
  have hexp : NormedSpace.exp x = ∑' n : ℕ, (n !⁻¹ : ℝ) • x ^ n :=
    (exp_hasSum x).tsum_eq.symm
  rw [hexp]
  refine tsum_of_norm_bounded hsum ?_
  intro n
  rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n !⁻¹ : ℝ))]
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact norm_pow_le x n

end NormExp

/-! ## 5. The Lie product formula.

We assemble the pieces.  We work in a complete normed `ℂ`-algebra that is
also a normed `ℝ`-algebra with `ℝ → ℂ` scalar tower (the matrix algebra
`Matrix (Fin n) (Fin n) ℂ` with its C*-norm is such an algebra). -/

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
  [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℂ 𝔸]
  [IsScalarTower ℝ ℂ 𝔸] [CompleteSpace 𝔸]

/-- `exp (n • y) = (exp y)^n`, proved from `exp_add_of_commute` (no `ℚ`
    scalar structure required). -/
private lemma exp_add_commute' {x y : 𝔸} (hxy : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hxy
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

private lemma exp_nsmul' (n : ℕ) (y : 𝔸) :
    NormedSpace.exp (n • y) = NormedSpace.exp y ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, NormedSpace.exp_zero]
  | succ n ih =>
      rw [succ_nsmul, pow_succ,
        exp_add_commute' ((Commute.refl y).smul_left n), ih]

/-- `(exp ((1/k)•(A+B)))^k = exp (A+B)` for `k ≥ 1`. -/
theorem Tn_pow_eq (C : 𝔸) {k : ℕ} (hk : 1 ≤ k) :
    (NormedSpace.exp ((1 / (k : ℂ)) • C)) ^ k = NormedSpace.exp C := by
  have hk0 : (k : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  rw [← exp_nsmul' k ((1 / (k : ℂ)) • C)]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [mul_one_div, div_self hk0, one_smul]

/-- `‖(1/(k:ℂ)) • A‖ = (1/k) * ‖A‖` for `k ≥ 1`. -/
private lemma norm_invNat_smul (A : 𝔸) {k : ℕ} (hk : 1 ≤ k) :
    ‖(1 / (k : ℂ)) • A‖ = (1 / k) * ‖A‖ := by
  rw [norm_smul]
  congr 1
  rw [norm_div, norm_one, Complex.norm_natCast]

/-- The key per-step bound: `‖S_k − T_k‖ ≤ E / k²` for an explicit
    constant `E`, valid for `k ≥ 1`.  Here
    `S_k = exp(A/k)·exp(B/k)`, `T_k = exp((A+B)/k)`. -/
theorem Sn_sub_Tn_bound (A B : 𝔸) {k : ℕ} (hk : 1 ≤ k) :
    ‖(NormedSpace.exp ((1 / (k : ℂ)) • A)
        * NormedSpace.exp ((1 / (k : ℂ)) • B))
      - NormedSpace.exp ((1 / (k : ℂ)) • (A + B))‖
      ≤ (((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)
            + ‖A‖ ^ 2 * Real.exp ‖A‖ + ‖B‖ ^ 2 * Real.exp ‖B‖)
          + ‖A + B‖ ^ 2 * Real.exp ‖A + B‖) / (k : ℝ) ^ 2 := by
  set a : 𝔸 := (1 / (k : ℂ)) • A with ha
  set b : 𝔸 := (1 / (k : ℂ)) • B with hb
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hab : a + b = (1 / (k : ℂ)) • (A + B) := by
    rw [ha, hb, smul_add]
  -- decompose S_k - T_k = (S_k - 1 - a - b) - (T_k - 1 - (a+b))
  have hdecomp :
      (NormedSpace.exp a * NormedSpace.exp b)
        - NormedSpace.exp (a + b)
        = (NormedSpace.exp a * NormedSpace.exp b - 1 - a - b)
          - (NormedSpace.exp (a + b) - 1 - (a + b)) := by
    abel
  rw [← hab, hdecomp]
  refine (norm_sub_le _ _).trans ?_
  -- norm facts
  have hna : ‖a‖ = (1 / k) * ‖A‖ := norm_invNat_smul A hk
  have hnb : ‖b‖ = (1 / k) * ‖B‖ := norm_invNat_smul B hk
  have hnab : ‖a + b‖ = (1 / k) * ‖A + B‖ := by
    rw [hab]; exact norm_invNat_smul (A + B) hk
  have hone_div_le : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_one hk0]; exact_mod_cast hk
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  -- `‖a‖ ≤ ‖A‖`, etc., and the squared-rescaling identities
  have hsmall : ∀ A : 𝔸, (1 / (k : ℝ)) * ‖A‖ ≤ ‖A‖ := by
    intro A
    nlinarith [norm_nonneg A, hone_div_le]
  have haA : ‖a‖ ≤ ‖A‖ := hna ▸ hsmall A
  have hbB : ‖b‖ ≤ ‖B‖ := hnb ▸ hsmall B
  have habAB : ‖a + b‖ ≤ ‖A + B‖ := hnab ▸ hsmall (A + B)
  have hExpa : Real.exp ‖a‖ ≤ Real.exp ‖A‖ := Real.exp_le_exp.mpr haA
  have hExpb : Real.exp ‖b‖ ≤ Real.exp ‖B‖ := Real.exp_le_exp.mpr hbB
  have hExpab : Real.exp ‖a + b‖ ≤ Real.exp ‖A + B‖ := Real.exp_le_exp.mpr habAB
  -- norm-over-k bounds
  have hkpos : (0 : ℝ) < (k : ℝ) := hk0
  have haA' : ‖a‖ ≤ ‖A‖ / k := le_of_eq (by rw [hna]; ring)
  have hbB' : ‖b‖ ≤ ‖B‖ / k := le_of_eq (by rw [hnb]; ring)
  have habAB' : ‖a + b‖ ≤ ‖A + B‖ / k := le_of_eq (by rw [hnab]; ring)
  have hanon : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
  have hbnon : (0:ℝ) ≤ ‖b‖ := norm_nonneg _
  have habnon : (0:ℝ) ≤ ‖a + b‖ := norm_nonneg _
  -- bound the cross piece
  have hcross : ‖NormedSpace.exp a * NormedSpace.exp b - 1 - a - b‖
      ≤ ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)
          + ‖A‖ ^ 2 * Real.exp ‖A‖ + ‖B‖ ^ 2 * Real.exp ‖B‖) / (k : ℝ) ^ 2 := by
    refine (norm_expMul_sub_one_sub_add_le a b).trans ?_
    have t1 : (‖a‖ * Real.exp ‖a‖) * (‖b‖ * Real.exp ‖b‖)
        ≤ ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)) / (k : ℝ) ^ 2 := by
      have e1 : ‖a‖ * Real.exp ‖a‖ ≤ (‖A‖ * Real.exp ‖A‖) / k := by
        calc ‖a‖ * Real.exp ‖a‖
            ≤ (‖A‖ / k) * Real.exp ‖A‖ :=
              mul_le_mul haA' hExpa (Real.exp_nonneg _) (by positivity)
          _ = (‖A‖ * Real.exp ‖A‖) / k := by ring
      have e2 : ‖b‖ * Real.exp ‖b‖ ≤ (‖B‖ * Real.exp ‖B‖) / k := by
        calc ‖b‖ * Real.exp ‖b‖
            ≤ (‖B‖ / k) * Real.exp ‖B‖ :=
              mul_le_mul hbB' hExpb (Real.exp_nonneg _) (by positivity)
          _ = (‖B‖ * Real.exp ‖B‖) / k := by ring
      calc (‖a‖ * Real.exp ‖a‖) * (‖b‖ * Real.exp ‖b‖)
          ≤ ((‖A‖ * Real.exp ‖A‖) / k) * ((‖B‖ * Real.exp ‖B‖) / k) :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)) / (k : ℝ) ^ 2 := by
            rw [div_mul_div_comm, sq]
    have t2 : ‖a‖ ^ 2 * Real.exp ‖a‖ ≤ (‖A‖ ^ 2 * Real.exp ‖A‖) / (k : ℝ) ^ 2 := by
      have hsq : ‖a‖ ^ 2 ≤ ‖A‖ ^ 2 / (k : ℝ) ^ 2 := by
        rw [← div_pow]; exact pow_le_pow_left₀ hanon haA' 2
      calc ‖a‖ ^ 2 * Real.exp ‖a‖
          ≤ (‖A‖ ^ 2 / (k : ℝ) ^ 2) * Real.exp ‖A‖ :=
            mul_le_mul hsq hExpa (Real.exp_nonneg _) (by positivity)
        _ = (‖A‖ ^ 2 * Real.exp ‖A‖) / (k : ℝ) ^ 2 := by ring
    have t3 : ‖b‖ ^ 2 * Real.exp ‖b‖ ≤ (‖B‖ ^ 2 * Real.exp ‖B‖) / (k : ℝ) ^ 2 := by
      have hsq : ‖b‖ ^ 2 ≤ ‖B‖ ^ 2 / (k : ℝ) ^ 2 := by
        rw [← div_pow]; exact pow_le_pow_left₀ hbnon hbB' 2
      calc ‖b‖ ^ 2 * Real.exp ‖b‖
          ≤ (‖B‖ ^ 2 / (k : ℝ) ^ 2) * Real.exp ‖B‖ :=
            mul_le_mul hsq hExpb (Real.exp_nonneg _) (by positivity)
        _ = (‖B‖ ^ 2 * Real.exp ‖B‖) / (k : ℝ) ^ 2 := by ring
    calc (‖a‖ * Real.exp ‖a‖) * (‖b‖ * Real.exp ‖b‖)
          + ‖a‖ ^ 2 * Real.exp ‖a‖ + ‖b‖ ^ 2 * Real.exp ‖b‖
        ≤ ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)) / (k : ℝ) ^ 2
          + (‖A‖ ^ 2 * Real.exp ‖A‖) / (k : ℝ) ^ 2
          + (‖B‖ ^ 2 * Real.exp ‖B‖) / (k : ℝ) ^ 2 := by
          exact add_le_add (add_le_add t1 t2) t3
      _ = _ := by rw [div_add_div_same, div_add_div_same]
  -- bound the T piece
  have hT : ‖NormedSpace.exp (a + b) - 1 - (a + b)‖
      ≤ (‖A + B‖ ^ 2 * Real.exp ‖A + B‖) / (k : ℝ) ^ 2 := by
    refine (norm_exp_sub_one_sub_le (a + b)).trans ?_
    have hsq : ‖a + b‖ ^ 2 ≤ ‖A + B‖ ^ 2 / (k : ℝ) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ habnon habAB' 2
    calc ‖a + b‖ ^ 2 * Real.exp ‖a + b‖
        ≤ (‖A + B‖ ^ 2 / (k : ℝ) ^ 2) * Real.exp ‖A + B‖ :=
          mul_le_mul hsq hExpab (Real.exp_nonneg _) (by positivity)
      _ = (‖A + B‖ ^ 2 * Real.exp ‖A + B‖) / (k : ℝ) ^ 2 := by ring
  -- combine
  calc ‖NormedSpace.exp a * NormedSpace.exp b - 1 - a - b‖
        + ‖NormedSpace.exp (a + b) - 1 - (a + b)‖
      ≤ ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)
          + ‖A‖ ^ 2 * Real.exp ‖A‖ + ‖B‖ ^ 2 * Real.exp ‖B‖) / (k : ℝ) ^ 2
        + (‖A + B‖ ^ 2 * Real.exp ‖A + B‖) / (k : ℝ) ^ 2 :=
        add_le_add hcross hT
    _ = _ := by rw [← add_div]

/-- Norm bound on the factor: `‖S_k‖, ‖T_k‖ ≤ exp((‖A‖+‖B‖)/k)`. -/
private lemma norm_factor_le (A B : 𝔸) {k : ℕ} (hk : 1 ≤ k) :
    ‖NormedSpace.exp ((1 / (k : ℂ)) • A)
        * NormedSpace.exp ((1 / (k : ℂ)) • B)‖
      ≤ Real.exp ((‖A‖ + ‖B‖) / k)
    ∧ ‖NormedSpace.exp ((1 / (k : ℂ)) • (A + B))‖
      ≤ Real.exp ((‖A‖ + ‖B‖) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hna : ‖(1 / (k : ℂ)) • A‖ = (1 / k) * ‖A‖ := norm_invNat_smul A hk
  have hnb : ‖(1 / (k : ℂ)) • B‖ = (1 / k) * ‖B‖ := norm_invNat_smul B hk
  have hnab : ‖(1 / (k : ℂ)) • (A + B)‖ = (1 / k) * ‖A + B‖ :=
    norm_invNat_smul (A + B) hk
  constructor
  · calc ‖NormedSpace.exp ((1 / (k : ℂ)) • A)
            * NormedSpace.exp ((1 / (k : ℂ)) • B)‖
        ≤ ‖NormedSpace.exp ((1 / (k : ℂ)) • A)‖
          * ‖NormedSpace.exp ((1 / (k : ℂ)) • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖(1 / (k : ℂ)) • A‖ * Real.exp ‖(1 / (k : ℂ)) • B‖ :=
          mul_le_mul (norm_exp_le _) (norm_exp_le _) (norm_nonneg _)
            (Real.exp_nonneg _)
      _ = Real.exp ((‖A‖ + ‖B‖) / k) := by
          rw [← Real.exp_add, hna, hnb]; congr 1; ring
  · calc ‖NormedSpace.exp ((1 / (k : ℂ)) • (A + B))‖
        ≤ Real.exp ‖(1 / (k : ℂ)) • (A + B)‖ := norm_exp_le _
      _ ≤ Real.exp ((‖A‖ + ‖B‖) / k) := by
          apply Real.exp_le_exp.mpr
          rw [hnab]
          have hadd : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
          calc (1 / (k:ℝ)) * ‖A + B‖
              ≤ (1 / (k:ℝ)) * (‖A‖ + ‖B‖) :=
                mul_le_mul_of_nonneg_left hadd (by positivity)
            _ = (‖A‖ + ‖B‖) / k := by ring

/-- **The Lie product formula** (Banach-algebra / matrix form).

    `(exp(A/k) · exp(B/k))^k  →  exp(A + B)`  as `k → ∞`. -/
theorem lieTrotter_normedExp (A B : 𝔸) :
    Filter.Tendsto
      (fun k : ℕ =>
        (NormedSpace.exp ((1 / (k : ℂ)) • A)
          * NormedSpace.exp ((1 / (k : ℂ)) • B)) ^ k)
      Filter.atTop
      (nhds (NormedSpace.exp (A + B))) := by
  -- abbreviations
  set D : ℝ := ‖A‖ + ‖B‖ with hD
  set E : ℝ := ((‖A‖ * Real.exp ‖A‖) * (‖B‖ * Real.exp ‖B‖)
        + ‖A‖ ^ 2 * Real.exp ‖A‖ + ‖B‖ ^ 2 * Real.exp ‖B‖)
      + ‖A + B‖ ^ 2 * Real.exp ‖A + B‖ with hE
  -- reduce to the norm-difference tending to 0
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- upper bound the norm difference by (E·exp D)/k, eventually
  apply squeeze_zero'
    (g := fun k : ℕ => (E * Real.exp D) / k)
  · -- nonnegativity, eventually
    filter_upwards with k using norm_nonneg _
  · -- the key bound, eventually for k ≥ 1
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkRpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    -- rewrite exp(A+B) = T_k^k
    rw [← Tn_pow_eq (A + B) hk]
    -- telescoping bound (k ≥ 1 form)
    refine (telescope_norm_pow_sub_pow' _ _ hk).trans ?_
    -- bound the max-of-norms factor
    obtain ⟨hSf, hTf⟩ := norm_factor_le A B hk
    set S : 𝔸 := NormedSpace.exp ((1 / (k : ℂ)) • A)
      * NormedSpace.exp ((1 / (k : ℂ)) • B) with hS
    set T : 𝔸 := NormedSpace.exp ((1 / (k : ℂ)) • (A + B)) with hT
    set Mb : ℝ := Real.exp (D / k) with hMb
    have hmaxle : max ‖S‖ ‖T‖ ≤ Mb := by
      rw [hMb, hD]; exact max_le hSf hTf
    have hmaxnn : (0 : ℝ) ≤ max ‖S‖ ‖T‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    -- M^(k-1) ≤ exp D
    have hpowMb : Mb ^ (k - 1) ≤ Real.exp D := by
      rw [hMb, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [hD]
      calc ((k - 1 : ℕ) : ℝ) * ((‖A‖ + ‖B‖) / k)
          ≤ (k : ℝ) * ((‖A‖ + ‖B‖) / k) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
              rw [Nat.cast_sub hk]; simp
            exact this
        _ = ‖A‖ + ‖B‖ := by field_simp
    have hpowmax : (max ‖S‖ ‖T‖) ^ (k - 1) ≤ Real.exp D :=
      le_trans (pow_le_pow_left₀ hmaxnn hmaxle (k - 1)) hpowMb
    -- the per-step difference bound
    have hstep : ‖S - T‖ ≤ E / (k : ℝ) ^ 2 := by
      rw [hS, hT, hE]; exact Sn_sub_Tn_bound A B hk
    -- assemble:  k · max^(k-1) · ‖S-T‖ ≤ k · exp D · (E/k²)
    have hEnn : (0 : ℝ) ≤ E := by
      rw [hE]; positivity
    calc (k : ℝ) * (max ‖S‖ ‖T‖) ^ (k - 1) * ‖S - T‖
        ≤ (k : ℝ) * Real.exp D * (E / (k : ℝ) ^ 2) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hpowmax (by positivity)
          · exact hstep
          · exact norm_nonneg _
          · positivity
      _ = (E * Real.exp D) / (k : ℝ) := by
          have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkRpos
          rw [eq_div_iff hkne]
          field_simp
  · -- (E·exp D)/k → 0
    simpa using tendsto_const_div_atTop_nhds_zero_nat (E * Real.exp D)

end Trotter

/-! ## 6. Discharge of the named CFC-free target.

Instantiate `lieTrotter_normedExp` at the matrix C*-algebra to close
`LiebSubgateProgress.LieTrotter_NormedExp_Target`, and propagate the
discharge up the Golden–Thompson chain as far as the existing reductions
allow. -/

section Discharge

open scoped Matrix.Norms.L2Operator
open UnifiedTheory.LayerB.LiebSubgateProgress
open UnifiedTheory.LayerB.GoldenThompsonNonCommuting
open UnifiedTheory.LayerB.GoldenThompsonInequality
open UnifiedTheory.LayerB.LiebGoldenThompson

/-- **The CFC-free Lie–Trotter target holds.**

    Instantiates the general Banach-algebra Lie product formula at the
    matrix C*-algebra `Matrix (Fin n) (Fin n) ℂ`.  For `n = 0` the matrix
    algebra is trivial and the statement holds by `Subsingleton`; for
    `n ≥ 1` the algebra is a unital C*-algebra (hence `NormOneClass`) and
    we apply `lieTrotter_normedExp`. -/
theorem LieTrotter_NormedExp_Target_holds : LieTrotter_NormedExp_Target := by
  intro n A B _hA _hB
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton: limit is trivial.
    subst hn
    have hss : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := by
      constructor; intro a b; ext i; exact i.elim0
    have hconst : (fun k : ℕ =>
        (NormedSpace.exp ((1 / (k : ℂ)) • A)
          * NormedSpace.exp ((1 / (k : ℂ)) • B)) ^ k)
        = fun _ => NormedSpace.exp (A + B) := by
      funext k; exact Subsingleton.elim _ _
    rw [hconst]
    exact tendsto_const_nhds
  · -- `n ≥ 1`: `Fin n` is nonempty, so the algebra is nontrivial.
    have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hnt : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    have hnoc : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    exact lieTrotter_normedExp A B

/-! ### Propagation up the Golden–Thompson / Lieb chain.

`LieTrotter_NormedExp_Target_holds` discharges the **first** of the two
sharpened residuals of the GT route.  The **second**,
`PerStep_TraceInequality_NormedExp_Target` (the finite-`k` Re-trace
bound), is not proved here — it is an independent Schatten/Hölder trace
estimate.  We record the conditional propagation: once that single
remaining target is supplied, the non-commuting GT subgate, the GT
target, and the bundled route target all follow **unconditionally**
(the Lie–Trotter half is now closed). -/

/-- **Non-commuting Golden–Thompson subgate from the (now unconditional)
    Lie–Trotter target plus the still-open per-step trace target.** -/
theorem goldenThompson_nonCommuting_of_perStep
    (hPer : PerStep_TraceInequality_NormedExp_Target) :
    GoldenThompson_NonCommuting_Subgate :=
  goldenThompson_nonCommuting_from_normedExp_subgates
    LieTrotter_NormedExp_Target_holds hPer

/-- **Golden–Thompson target from the per-step trace target** (Lie–Trotter
    half discharged). -/
theorem goldenThompson_target_of_perStep
    (hPer : PerStep_TraceInequality_NormedExp_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_from_normedExp_route ⟨LieTrotter_NormedExp_Target_holds, hPer⟩

end Discharge

/-! ## 7. Axiom audit (commented). -/

-- #print axioms lieTrotter_normedExp
-- #print axioms LieTrotter_NormedExp_Target_holds
-- #print axioms goldenThompson_target_of_perStep
-- All three depend only on [propext, Classical.choice, Quot.sound]
-- (standard Mathlib axioms); no `sorryAx`, no custom axioms.

end UnifiedTheory.LayerB.LieTrotterProduct
