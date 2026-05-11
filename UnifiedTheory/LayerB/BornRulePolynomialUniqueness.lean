/-
  LayerB/BornRulePolynomialUniqueness.lean — Born rule unique among
  polynomial radial observables (closes the integer-power gap).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — AUDIT FINDING

  `LayerB/BornRuleQuadratic.lean` proves Born rule uniqueness within
  the one-parameter family `(Q² + P²)^n` with `n ∈ ℕ`. The audit (this
  conversation) found that this does NOT rule out polynomial mixtures
  like `c₀ + c₁(Q²+P²) + c₂(Q²+P²)²`.

  This file STRENGTHENS the uniqueness from the integer-power family
  to ALL finite-degree polynomials in (Q² + P²).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (rigorously, zero sorry)

  A polynomial radial observable is `polyRadObs cs deg Q P :=
  ∑_{n=0}^{deg} cs(n) · (Q² + P²)^n`. Orthogonal additivity at the
  pair `(a, 0) ⊥ (0, b)` reads `polyRadObs(a, 0) + polyRadObs(0, b) =
  polyRadObs(a, b)`, equivalent (via `Real.sq_sqrt`) to Cauchy's
  equation `g(u + v) = g(u) + g(v)` on `[0, ∞)` for the radial poly.

  Setting `v = u` gives `g(2u) = 2 g(u)`, which means the polynomial
  `q(u) := ∑ cs(n) · (2^n − 2) · u^n` vanishes for all `u ≥ 0`. By
  `Polynomial.eq_zero_of_infinite_isRoot` (Mathlib), `q` is the zero
  polynomial. Hence `cs(n) · (2^n − 2) = 0` for all `n ≤ deg`. Since
  `2^n − 2 ≠ 0` for `n ≠ 1`, this forces `cs(n) = 0` for all `n ≠ 1`.

  Conclusion: every polynomial radial observable that is orthogonally
  additive equals `cs(1) · (Q² + P²)` — the Born rule, up to scale.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  CLOSED in this file:
    * Polynomial radial observables of any degree.
    * The "polynomial vanishing on [0, ∞) ⟹ zero polynomial" step
      (`Polynomial.eq_zero_of_infinite_isRoot`, applied to ℕ ↪ ℝ).

  REMAINING OPEN:
    * Smooth-but-non-polynomial g(Q²+P²): same Cauchy argument
      reduces to "continuous + Cauchy on [0, ∞) ⟹ linear", a
      separate analysis fact (Mathlib has it; not bridged here).
    * Full Gleason for ≥ 3-dim Hilbert spaces: a measure-theoretic
      structure theorem requiring projection-lattice machinery
      (multi-week formalization, not in scope here).

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BornRulePolynomialUniqueness

open Polynomial Finset

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: POLYNOMIAL RADIAL OBSERVABLES (COEFFICIENT FORM)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The radial polynomial `g(t) = ∑_{n ≤ deg} cs n · t^n`. -/
noncomputable def polyRad (cs : ℕ → ℝ) (deg : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ range (deg + 1), cs n * t ^ n

/-- The polynomial radial observable `(Q, P) ↦ g(Q² + P²)`. -/
noncomputable def polyRadObs (cs : ℕ → ℝ) (deg : ℕ) (Q P : ℝ) : ℝ :=
  polyRad cs deg (Q ^ 2 + P ^ 2)

/-- Orthogonal additivity for the polynomial radial observable. -/
def IsOrthogRadAdditive (cs : ℕ → ℝ) (deg : ℕ) : Prop :=
  ∀ a b : ℝ,
    polyRadObs cs deg a 0 + polyRadObs cs deg 0 b = polyRadObs cs deg a b

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: CAUCHY BRIDGE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Orthogonal additivity ⟺ Cauchy's equation for `polyRad` on `[0, ∞)`. -/
theorem orthogRad_iff_cauchy (cs : ℕ → ℝ) (deg : ℕ) :
    IsOrthogRadAdditive cs deg ↔
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
       polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v)) := by
  constructor
  · intro h u v hu hv
    have h' := h (Real.sqrt u) (Real.sqrt v)
    unfold polyRadObs at h'
    have h0 : Real.sqrt u ^ 2 + (0 : ℝ) ^ 2 = u := by rw [Real.sq_sqrt hu]; ring
    have h1 : (0 : ℝ) ^ 2 + Real.sqrt v ^ 2 = v := by rw [Real.sq_sqrt hv]; ring
    have h2 : Real.sqrt u ^ 2 + Real.sqrt v ^ 2 = u + v := by
      rw [Real.sq_sqrt hu, Real.sq_sqrt hv]
    rw [h0, h1, h2] at h'
    exact h'
  · intro h a b
    unfold polyRadObs
    have hab := h (a^2) (b^2) (sq_nonneg a) (sq_nonneg b)
    have e1 : a^2 + (0:ℝ)^2 = a^2 := by ring
    have e2 : (0:ℝ)^2 + b^2 = b^2 := by ring
    rw [e1, e2]
    exact hab

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE DOUBLING-DIFFERENCE POLYNOMIAL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `cauchyDoublePoly cs deg = ∑ n ≤ deg, C (cs n · (2^n − 2)) · X^n`.
    Its evaluation at u is `polyRad cs deg (2u) − 2 · polyRad cs deg u`.
    Setting `v = u` in Cauchy's equation forces this poly to vanish on
    `[0, ∞)`, hence (by `Polynomial.eq_zero_of_infinite_isRoot`) it
    is the zero polynomial.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The doubling-difference polynomial in explicit coefficient form. -/
noncomputable def cauchyDoublePoly (cs : ℕ → ℝ) (deg : ℕ) : Polynomial ℝ :=
  ∑ n ∈ range (deg + 1), C (cs n * (2 ^ n - 2)) * X ^ n

/-- Evaluation of `cauchyDoublePoly` at `u` equals
    `polyRad cs deg (2u) − 2 · polyRad cs deg u`. -/
theorem cauchyDoublePoly_eval (cs : ℕ → ℝ) (deg : ℕ) (u : ℝ) :
    (cauchyDoublePoly cs deg).eval u =
    polyRad cs deg (2 * u) - 2 * polyRad cs deg u := by
  unfold cauchyDoublePoly polyRad
  rw [eval_finset_sum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have h2u : (2 * u) ^ n = 2 ^ n * u ^ n := by rw [mul_pow]
  rw [h2u]
  ring

/-- If Cauchy's equation holds on `[0, ∞)`, the doubling-difference
    polynomial vanishes at every nonneg real. -/
theorem cauchyDoublePoly_vanishes_nonneg
    (cs : ℕ → ℝ) (deg : ℕ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v))
    (u : ℝ) (hu : 0 ≤ u) :
    (cauchyDoublePoly cs deg).eval u = 0 := by
  rw [cauchyDoublePoly_eval]
  have hsum := hC u u hu hu
  have h2u : u + u = 2 * u := by ring
  rw [h2u] at hsum
  linarith

/-- A polynomial in `ℝ[X]` that vanishes at every natural number is
    the zero polynomial (uses `Polynomial.eq_zero_of_infinite_isRoot`). -/
theorem polynomial_zero_of_eval_nat_zero {p : Polynomial ℝ}
    (h : ∀ k : ℕ, p.eval (k : ℝ) = 0) : p = 0 := by
  apply eq_zero_of_infinite_isRoot
  -- Show {x | IsRoot p x} is infinite by exhibiting an injective
  -- ℕ → ℝ landing in it.
  have h_inj : Function.Injective ((↑) : ℕ → ℝ) := Nat.cast_injective
  have h_inf_range : (Set.range ((↑) : ℕ → ℝ)).Infinite :=
    Set.infinite_range_of_injective h_inj
  apply h_inf_range.mono
  intro x hx
  obtain ⟨k, hk⟩ := hx
  show (p.eval x = 0)
  rw [← hk]
  exact h k

/-- The doubling-difference polynomial is the zero polynomial when
    Cauchy's equation holds on `[0, ∞)`. -/
theorem cauchyDoublePoly_eq_zero (cs : ℕ → ℝ) (deg : ℕ)
    (hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v)) :
    cauchyDoublePoly cs deg = 0 := by
  apply polynomial_zero_of_eval_nat_zero
  intro k
  exact cauchyDoublePoly_vanishes_nonneg cs deg hC (k : ℝ) (Nat.cast_nonneg k)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: COEFFICIENT EXTRACTION ⟹ HIGHER COEFFS VANISH
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The coefficient at `k ≤ deg` of `cauchyDoublePoly cs deg` equals
    `cs k · (2^k − 2)`. -/
theorem cauchyDoublePoly_coeff (cs : ℕ → ℝ) (deg k : ℕ) (hk : k ≤ deg) :
    (cauchyDoublePoly cs deg).coeff k = cs k * (2 ^ k - 2) := by
  unfold cauchyDoublePoly
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro n _ hnk
    rw [coeff_C_mul, coeff_X_pow, if_neg hnk.symm, mul_zero]
  · intro hk_not
    exfalso
    apply hk_not
    rw [Finset.mem_range]; omega

/-- For `n ≠ 1`, the factor `2^n − 2` is non-zero. -/
theorem two_pow_sub_two_ne_zero {n : ℕ} (hn : n ≠ 1) : (2 : ℝ) ^ n - 2 ≠ 0 := by
  rcases eq_or_ne n 0 with rfl | h0
  · -- n = 0: 2^0 - 2 = -1
    norm_num
  · -- n ≠ 0 and n ≠ 1, so n ≥ 2
    have hge2 : n ≥ 2 := by omega
    intro habs
    have h2pow_eq : (2 : ℝ) ^ n = 2 := by linarith
    have h2pow_ge : (2 : ℝ) ^ n ≥ (2 : ℝ) ^ 2 := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hge2
    have : (2 : ℝ) ^ 2 = 4 := by norm_num
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE STRENGTHENED UNIQUENESS THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **STRENGTHENED BORN RULE UNIQUENESS** (over polynomial radial
    observables of any degree). -/
theorem polynomial_born_uniqueness (cs : ℕ → ℝ) (deg : ℕ)
    (h : IsOrthogRadAdditive cs deg) :
    ∀ k ≤ deg, k ≠ 1 → cs k = 0 := by
  intro k hk hk1
  -- Convert to Cauchy
  have hC := (orthogRad_iff_cauchy cs deg).mp h
  -- Doubling-difference poly is zero
  have hzero := cauchyDoublePoly_eq_zero cs deg hC
  -- Extract coefficient at k
  have hcoeff := cauchyDoublePoly_coeff cs deg k hk
  -- Coefficient of zero polynomial is zero
  have hcoeff_zero : (cauchyDoublePoly cs deg).coeff k = 0 := by
    rw [hzero, coeff_zero]
  rw [hcoeff_zero] at hcoeff
  -- cs k · (2^k − 2) = 0; since 2^k − 2 ≠ 0 for k ≠ 1, cs k = 0
  have hne := two_pow_sub_two_ne_zero hk1
  have : cs k * (2 ^ k - 2) = 0 := hcoeff.symm
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hne

/-- **THE BORN RULE IS THE UNIQUE ORTHOGONALLY ADDITIVE POLYNOMIAL
    RADIAL OBSERVABLE** (for `1 ≤ deg`): for any orthogonally additive
    polynomial radial observable `polyRadObs cs deg`, it equals
    `cs 1 · (Q² + P²)`.

    The `1 ≤ deg` hypothesis is genuine: at `deg = 0` the conclusion
    references `cs 1`, which is not in the polynomial's coefficient
    list and so isn't constrained by orthogonal additivity. -/
theorem polynomial_born_form (cs : ℕ → ℝ) (deg : ℕ) (hdeg : 1 ≤ deg)
    (h : IsOrthogRadAdditive cs deg) :
    ∀ Q P : ℝ, polyRadObs cs deg Q P = cs 1 * (Q ^ 2 + P ^ 2) := by
  intro Q P
  unfold polyRadObs polyRad
  have hkill := polynomial_born_uniqueness cs deg h
  have h1mem : (1 : ℕ) ∈ range (deg + 1) := by rw [mem_range]; omega
  rw [← Finset.sum_erase_add _ _ h1mem]
  have h_others : ∀ n ∈ (range (deg + 1)).erase 1,
      cs n * (Q ^ 2 + P ^ 2) ^ n = 0 := by
    intro n hn
    rw [Finset.mem_erase, Finset.mem_range] at hn
    obtain ⟨hn1, hnle⟩ := hn
    have : cs n = 0 := hkill n (by omega) hn1
    rw [this, zero_mul]
  rw [Finset.sum_eq_zero h_others, zero_add, pow_one]

/-- **The framework's master strengthened-Born-rule theorem** —
    bundles the bridge, the polynomial-vanishing closure, and the
    uniqueness conclusion. -/
theorem strengthened_born_master (cs : ℕ → ℝ) (deg : ℕ) :
    -- (1) The bridge
    (IsOrthogRadAdditive cs deg ↔
     ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
       polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v))
    -- (2) Cauchy ⟹ doubling poly vanishes nonneg
    ∧ (∀ _hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
               polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v),
        ∀ u : ℝ, 0 ≤ u → (cauchyDoublePoly cs deg).eval u = 0)
    -- (3) Cauchy ⟹ doubling poly is the zero polynomial
    ∧ (∀ _hC : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
               polyRad cs deg u + polyRad cs deg v = polyRad cs deg (u + v),
        cauchyDoublePoly cs deg = 0)
    -- (4) Coefficients of cauchyDoublePoly
    ∧ (∀ k ≤ deg, (cauchyDoublePoly cs deg).coeff k = cs k * (2 ^ k - 2))
    -- (5) THE STRENGTHENED UNIQUENESS: orth. add. ⟹ cs n = 0 for n ≠ 1
    ∧ (IsOrthogRadAdditive cs deg → ∀ k ≤ deg, k ≠ 1 → cs k = 0) :=
  ⟨orthogRad_iff_cauchy cs deg,
   fun hC u hu => cauchyDoublePoly_vanishes_nonneg cs deg hC u hu,
   fun hC => cauchyDoublePoly_eq_zero cs deg hC,
   fun k hk => cauchyDoublePoly_coeff cs deg k hk,
   polynomial_born_uniqueness cs deg⟩

end UnifiedTheory.LayerB.BornRulePolynomialUniqueness
