/-
  Audit/KFCausalCSpecLoopHolonomyBand.lean   (Volume sector — deterministic good-event band)

  The DETERMINISTIC half of the Poisson unit.  On the good event where every edge's
  two relative count errors are bounded, `|delta| <= eps < 1`, the loop holonomy is
  squeezed into an explicit multiplicative band.  With `U = (1+eps)/(1-eps)` and an
  `m`-edge loop:

        U^(-m/d)  <=  H_gamma  <=  U^(m/d).

  This propagates the per-edge two-count band (`ratio_band`) through the exact-part
  cancellation of `noisy_loop_holonomy`.  No independence is used.

  THE REMAINING (probabilistic) HALF, honestly flagged.  The probability of the good
  event is, per count, `Pr(|N/lambda - 1| >= eps) <= 1/(lambda*eps^2)` by Chebyshev
  with `Var(Poisson lambda) = lambda`, and per edge `<= 1/(lambda_u eps^2) +
  1/(lambda_v eps^2)` by a union bound (no independence), summed over loop edges.
  Mathlib HAS Chebyshev (`meas_ge_le_variance_div_sq`) but DOES NOT have the Poisson
  mean or variance -- `Poisson.lean` stops at the PMF sum.  Proving `Var(Poisson
  lambda) = lambda` from the series is the one genuinely open piece; it is NOT done
  here and must not be conflated with the deterministic band below.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecEdgeScaleDefect

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecLoopHolonomyBand

open UnifiedTheory.Audit.KFCausalCSpecEdgeScaleDefect

variable {V : Type*}

/-! ## Chain-product bounds -/

theorem chainProduct_nonneg (e : V → V → ℝ) (he : ∀ a b, 0 ≤ e a b) (u : V) (l : List V) :
    0 ≤ chainProduct e u l := by
  induction l generalizing u with
  | nil => simp
  | cons v rest ih => rw [chainProduct_cons]; exact mul_nonneg (he u v) (ih v)

theorem chainProduct_le (e : V → V → ℝ) (R : ℝ) (heR : ∀ a b, e a b ≤ R)
    (he0 : ∀ a b, 0 ≤ e a b) (hR : 0 ≤ R) (u : V) (l : List V) :
    chainProduct e u l ≤ R ^ l.length := by
  induction l generalizing u with
  | nil => simp
  | cons v rest ih =>
      rw [chainProduct_cons, List.length_cons, pow_succ']
      exact mul_le_mul (heR u v) (ih v) (chainProduct_nonneg e he0 v rest) hR

theorem chainProduct_ge (e : V → V → ℝ) (L : ℝ) (heL : ∀ a b, L ≤ e a b) (hL : 0 ≤ L)
    (u : V) (l : List V) :
    L ^ l.length ≤ chainProduct e u l := by
  induction l generalizing u with
  | nil => simp
  | cons v rest ih =>
      rw [chainProduct_cons, List.length_cons, pow_succ']
      exact mul_le_mul (heL u v) (ih v) (pow_nonneg hL _) (le_trans hL (heL u v))

/-! ## Two-count ratio band -/

/-- **Two-count ratio band.**  A single edge compares two counts.  If both relative
errors are `<= eps < 1`, the error factor `((1+delta_u)/(1+delta_v))^(1/d)` sits in
the explicit band `[((1-eps)/(1+eps))^(1/d), ((1+eps)/(1-eps))^(1/d)]`. -/
theorem ratio_band (d : ℕ) (δu δv ε : ℝ) (hε1 : ε < 1) (hu : |δu| ≤ ε) (hv : |δv| ≤ ε) :
    ((1 - ε) / (1 + ε)) ^ ((d : ℝ)⁻¹) ≤ ((1 + δu) / (1 + δv)) ^ ((d : ℝ)⁻¹)
    ∧ ((1 + δu) / (1 + δv)) ^ ((d : ℝ)⁻¹) ≤ ((1 + ε) / (1 - ε)) ^ ((d : ℝ)⁻¹) := by
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  obtain ⟨hv1, hv2⟩ := abs_le.mp hv
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg δu) hu
  have hz : (0:ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  refine ⟨Real.rpow_le_rpow (div_nonneg (by linarith) (by linarith)) ?_ hz,
    Real.rpow_le_rpow (div_nonneg (by linarith) (by linarith)) ?_ hz⟩
  · rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + ε), div_mul_eq_mul_div,
      le_div_iff₀ (by linarith : (0:ℝ) < 1 + δv)]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  · rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + δv), div_mul_eq_mul_div,
      le_div_iff₀ (by linarith : (0:ℝ) < 1 - ε)]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

/-! ## The loop holonomy band -/

/-- **Loop holonomy band.**  Along a closed loop, with each edge's error factor in
`[L, R]`, the noisy loop holonomy is squeezed into `[L^m, R^m]` (`m` = loop length):
the exact scale potential cancels (`noisy_loop_holonomy`) and only the bounded
error product survives.  With `L = ((1-eps)/(1+eps))^(1/d) = U^(-1/d)` and
`R = U^(1/d)` from `ratio_band`, this is `U^(-m/d) <= H_gamma <= U^(m/d)`. -/
theorem loop_holonomy_band (f : V → ℝ) (hf : ∀ v, 0 < f v) (e : V → V → ℝ)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (heL : ∀ a b, L ≤ e a b) (heR : ∀ a b, e a b ≤ R)
    (u : V) (l : List V) (hclosed : l.getLastD u = u) :
    L ^ l.length ≤ chainProduct (fun a b => (f a / f b) * e a b) u l
    ∧ chainProduct (fun a b => (f a / f b) * e a b) u l ≤ R ^ l.length := by
  rw [noisy_loop_holonomy f hf e u l hclosed]
  exact ⟨chainProduct_ge e L heL hL u l,
    chainProduct_le e R heR (fun a b => le_trans hL (heL a b)) hR u l⟩

#print axioms chainProduct_le
#print axioms chainProduct_ge
#print axioms ratio_band
#print axioms loop_holonomy_band

end UnifiedTheory.Audit.KFCausalCSpecLoopHolonomyBand
