/-
  Audit/KFCausalCSpecCurvatureVolumeBound.lean   (Volume sector — Step 1, the β input)

  The bounded-curvature small-diamond volume inequality that discharges the curvature
  error `β` assumed by the F3-bypass (`KFCausalCSpecTwoEmbeddingProperTime`).

  DIVISION OF LABOR.  The Riemann-normal-coordinate expansion of a small causal-diamond
  volume (Roy-Sinha-Surya, arXiv:1212.0631) is genuine Lorentzian differential geometry,
  not formalized here.  What IS supplied by that geometry, and taken here as explicit
  hypotheses, is the STRUCTURE of the volume-faithfulness defect:

      Vol / (C_d τ^d) - 1  =  c₁ τ²  +  rem,

  a leading curvature term whose coefficient is bounded by the curvature radius,
  `|c₁| ≤ A / λ²`, plus a UNIFORM higher-order remainder `|rem| ≤ D τ⁴ / λ⁴` (this
  uniform bound is exactly the ingredient Madsen's programme flags as "needed").

  What is PROVED here, rigorously, is that under the sub-curvature condition `τ ≤ λ`
  these combine into the clean small-diamond bound

      |Vol / (C_d τ^d) - 1|  ≤  (A + D) τ² / λ²,

  i.e. `β = (A+D) τ²/λ²`, which -> 0 as the diamonds shrink (high density).  This is the
  quantity the two-embedding proper-time band consumes.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecCurvatureVolumeBound

/-- **Bounded-curvature small-diamond volume bound (Step 1).**  Given the Roy-Sinha-Surya
expansion structure of the volume-faithfulness defect -- a leading curvature term with
coefficient bounded by the curvature radius (`|c₁| ≤ A/λ²`) plus a uniform higher-order
remainder (`|rem| ≤ D τ⁴/λ⁴`) -- the defect is bounded by `(A+D) τ²/λ²` whenever the
diamond is below the curvature scale (`τ ≤ λ`).  This is the `β` the F3-bypass assumes. -/
theorem smallDiamond_volumeFaithful
    (Cd A D τ lam Vol : ℝ) (d : ℕ)
    (hτ : 0 < τ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hsub : τ ≤ lam)
    (c₁ rem : ℝ)
    (hexp : Vol / (Cd * τ ^ d) - 1 = c₁ * τ ^ 2 + rem)
    (hc₁ : |c₁| ≤ A / lam ^ 2)
    (hrem : |rem| ≤ D * τ ^ 4 / lam ^ 4) :
    |Vol / (Cd * τ ^ d) - 1| ≤ (A + D) * τ ^ 2 / lam ^ 2 := by
  have hlamne : lam ≠ 0 := hlam.ne'
  have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
  have hlam4 : (0:ℝ) < lam ^ 4 := by positivity
  have hsub2 : τ ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ hτ.le hsub 2
  rw [hexp]
  calc |c₁ * τ ^ 2 + rem|
      ≤ |c₁ * τ ^ 2| + |rem| := abs_add_le _ _
    _ = |c₁| * τ ^ 2 + |rem| := by rw [abs_mul, abs_of_nonneg (sq_nonneg τ)]
    _ ≤ A / lam ^ 2 * τ ^ 2 + D * τ ^ 4 / lam ^ 4 :=
        add_le_add (mul_le_mul_of_nonneg_right hc₁ (sq_nonneg τ)) hrem
    _ ≤ (A + D) * τ ^ 2 / lam ^ 2 := by
        have expand : (A + D) * τ ^ 2 / lam ^ 2 - (A / lam ^ 2 * τ ^ 2 + D * τ ^ 4 / lam ^ 4)
            = D * τ ^ 2 * (lam ^ 2 - τ ^ 2) / lam ^ 4 := by field_simp; ring
        have hnn : (0:ℝ) ≤ D * τ ^ 2 * (lam ^ 2 - τ ^ 2) / lam ^ 4 :=
          div_nonneg (mul_nonneg (mul_nonneg hD (sq_nonneg τ)) (by linarith)) hlam4.le
        linarith [expand, hnn]

/-- **High-density collapse.**  The small-diamond bound `β = (A+D) τ²/λ²` is monotone in
`τ`: shrinking the diamond (as sprinkling density increases) shrinks the curvature error,
so `β -> 0`.  Combined with the F3-bypass, this drives the proper-time distortion to `1`. -/
theorem smallDiamond_beta_antitone
    (A D lam τ τ' : ℝ) (hAD : 0 ≤ A + D) (hlam : 0 < lam)
    (hτ' : 0 ≤ τ') (hτ : τ' ≤ τ) :
    (A + D) * τ' ^ 2 / lam ^ 2 ≤ (A + D) * τ ^ 2 / lam ^ 2 := by
  have hnum : (A + D) * τ' ^ 2 ≤ (A + D) * τ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ' hτ 2) hAD
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (pow_pos hlam 2).le)

#print axioms smallDiamond_volumeFaithful
#print axioms smallDiamond_beta_antitone

end UnifiedTheory.Audit.KFCausalCSpecCurvatureVolumeBound
