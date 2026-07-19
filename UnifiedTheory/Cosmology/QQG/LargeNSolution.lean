/-
  Cosmology/QQG/LargeNSolution.lean
  ────────────────────────────────────────

  The closed-form large-N solution of the β-functions of eq (2), written
  as in eq (4) of arXiv:2510.18733v2 (Liu–Quintin–Afshordi).

  Define the running variable  u := ln(μ/μ₀)  and the 't Hooft-like
  coupling  lam_tH := λ₀ N / (4π)².  Eq (4) is:

      λ(u)  =  λ₀ / (1 + lam_tH · u)
      ξ(u)  =  (35 λ₀² / (8 π²)) · u / (1 + lam_tH · u) .

  We treat the "small-ξ, large-N" simplification of eq (2), under which
  these are EXACT solutions:

      dλ/du  =  − (N / (4π)²) · λ²                    (large-N β_λ)
      dξ/du  =  + (70 / (4π)²) · λ²                   (small-ξ β_ξ)

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `lambdaLargeN` has the expected derivative — the large-N β_λ
       relation holds exactly.
    2. `xiLargeN` has the expected derivative — the small-ξ β_ξ relation
       holds exactly.

  SCOPE CAVEAT (matches paper §4 discussion):
    The full β-functions of eq (2) are NOT exactly satisfied by this
    closed form — the paper's "≃" symbol is doing real work.  What we
    prove is satisfaction of the *truncated* large-N + small-ξ system.
-/

import UnifiedTheory.Cosmology.QQG.Couplings
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG

open Real

/-! ## 1. The 't Hooft-like coupling -/

/-- The 't Hooft-like coupling of eq (4):  lam_tH = λ₀ N / (4π)². -/
noncomputable def tHooft (lam₀ N : ℝ) : ℝ :=
  lam₀ * N / (4 * Real.pi)^2

/-- `lam_tH · (4π)² = λ₀ · N`. -/
theorem tHooft_mul_pi_sq (lam₀ N : ℝ) :
    tHooft lam₀ N * (4 * Real.pi)^2 = lam₀ * N := by
  unfold tHooft
  have hpi : (4 * Real.pi)^2 ≠ 0 := by
    have : (0 : ℝ) < (4 * Real.pi)^2 := by
      have : (0 : ℝ) < 4 * Real.pi := by positivity
      positivity
    exact ne_of_gt this
  field_simp

/-! ## 2. The closed-form running -/

/-- The large-N closed-form solution for λ(u), with u = ln(μ/μ₀). -/
noncomputable def lambdaLargeN (lam₀ lam_tH u : ℝ) : ℝ :=
  lam₀ / (1 + lam_tH * u)

/-- The closed-form solution for ξ(u) in the small-ξ regime, eq (4). -/
noncomputable def xiLargeN (lam₀ lam_tH u : ℝ) : ℝ :=
  (35 * lam₀^2 / (8 * Real.pi^2)) * (u / (1 + lam_tH * u))

/-! ## 3. Derivative of the running denominator -/

/-- The denominator `w(u) = 1 + lam_tH · u` has derivative `lam_tH`. -/
theorem hasDerivAt_w (lam_tH u : ℝ) :
    HasDerivAt (fun s => 1 + lam_tH * s) lam_tH u := by
  have h_id : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  have h_mul : HasDerivAt (fun s : ℝ => lam_tH * s) (lam_tH * 1) u :=
    h_id.const_mul lam_tH
  have h_add : HasDerivAt (fun s : ℝ => 1 + lam_tH * s) (0 + lam_tH * 1) u :=
    (hasDerivAt_const u (1 : ℝ)).add h_mul
  simpa using h_add

/-! ## 4. Large-N β_λ relation -/

/-- **Main lemma for λ.**  The closed form `lambdaLargeN` satisfies the
    large-N truncation of β_λ exactly:

        d/du  λ(u)  =  − (N/(4π)²) · λ(u)² . -/
theorem hasDerivAt_lambdaLargeN
    (lam₀ N u : ℝ) (h_w : 1 + tHooft lam₀ N * u ≠ 0) :
    HasDerivAt (fun s => lambdaLargeN lam₀ (tHooft lam₀ N) s)
      (-(N / (4 * Real.pi)^2) * (lambdaLargeN lam₀ (tHooft lam₀ N) u)^2)
      u := by
  -- Build the quotient derivative directly.
  have h_num : HasDerivAt (fun _ : ℝ => lam₀) 0 u := hasDerivAt_const u lam₀
  have h_den : HasDerivAt (fun s => 1 + tHooft lam₀ N * s) (tHooft lam₀ N) u :=
    hasDerivAt_w (tHooft lam₀ N) u
  have h_div := h_num.div h_den h_w
  -- h_div : HasDerivAt (fun y => lam₀ / (1 + tHooft lam₀ N * y))
  --                    ((0 * (1 + tHooft lam₀ N * u) - lam₀ * tHooft lam₀ N)
  --                      / (1 + tHooft lam₀ N * u) ^ 2) u
  -- (after beta reduction)
  have h_drv :
      (0 * (1 + tHooft lam₀ N * u) - lam₀ * tHooft lam₀ N)
        / (1 + tHooft lam₀ N * u) ^ 2
      = -(N / (4 * Real.pi)^2)
        * (lambdaLargeN lam₀ (tHooft lam₀ N) u)^2 := by
    unfold lambdaLargeN tHooft
    have h_pi_pow : (4 * Real.pi)^2 ≠ 0 := pow_ne_zero 2 (by positivity)
    field_simp
    ring
  -- Massage the function shape and apply h_div.
  have h_fun :
      (fun s => lambdaLargeN lam₀ (tHooft lam₀ N) s)
        = (fun y => (fun _ : ℝ => lam₀) y / (fun s => 1 + tHooft lam₀ N * s) y) := by
    funext s
    simp [lambdaLargeN]
  rw [h_fun, ← h_drv]
  exact h_div

/-! ## 5. Small-ξ β_ξ relation -/

/-- The function `u ↦ u / (1 + lam_tH · u)` has derivative `1 / w²`. -/
theorem hasDerivAt_u_over_w
    (lam_tH u : ℝ) (h_w : 1 + lam_tH * u ≠ 0) :
    HasDerivAt (fun s => s / (1 + lam_tH * s))
      (1 / (1 + lam_tH * u)^2) u := by
  have h_num : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
  have h_den := hasDerivAt_w lam_tH u
  have h_div := h_num.div h_den h_w
  have h_drv :
      (1 * (1 + lam_tH * u) - u * lam_tH) / (1 + lam_tH * u) ^ 2
        = 1 / (1 + lam_tH * u) ^ 2 := by
    have h1 : 1 * (1 + lam_tH * u) - u * lam_tH = 1 := by ring
    rw [h1]
  have h_fun :
      (fun s : ℝ => s / (1 + lam_tH * s))
        = (fun y : ℝ => (fun s : ℝ => s) y / (fun s : ℝ => 1 + lam_tH * s) y) := by
    funext s
    rfl
  rw [h_fun, ← h_drv]
  exact h_div

/-- **Main lemma for ξ.**  The closed form `xiLargeN` satisfies the
    small-ξ truncation of β_ξ exactly:

        d/du  ξ(u)  =  + (70/(4π)²) · λ(u)² . -/
theorem hasDerivAt_xiLargeN
    (lam₀ N u : ℝ) (h_w : 1 + tHooft lam₀ N * u ≠ 0) :
    HasDerivAt (fun s => xiLargeN lam₀ (tHooft lam₀ N) s)
      ((70 / (4 * Real.pi)^2) *
        (lambdaLargeN lam₀ (tHooft lam₀ N) u)^2)
      u := by
  have h_uw := hasDerivAt_u_over_w (tHooft lam₀ N) u h_w
  have h_scaled : HasDerivAt
      (fun s => (35 * lam₀^2 / (8 * Real.pi^2))
                  * (s / (1 + tHooft lam₀ N * s)))
      ((35 * lam₀^2 / (8 * Real.pi^2))
        * (1 / (1 + tHooft lam₀ N * u)^2))
      u := h_uw.const_mul _
  have h_drv :
      (35 * lam₀^2 / (8 * Real.pi^2)) * (1 / (1 + tHooft lam₀ N * u)^2)
        = (70 / (4 * Real.pi)^2)
          * (lambdaLargeN lam₀ (tHooft lam₀ N) u)^2 := by
    unfold lambdaLargeN tHooft
    have h_pi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have h_fun :
      (fun s => xiLargeN lam₀ (tHooft lam₀ N) s)
        = (fun s => (35 * lam₀^2 / (8 * Real.pi^2))
                      * (s / (1 + tHooft lam₀ N * s))) := by
    funext s
    simp [xiLargeN]
  rw [h_fun, ← h_drv]
  exact h_scaled

end UnifiedTheory.Cosmology.QQG
