/-
  Layer A.1 — Renormalization rigidity: α = 2 fixed point

  The renormalization operator acts on power-law potentials as:
    (R_ℓ B)(r) = ℓ^(-2) B(r/ℓ)

  For B_α(r) = c r^(-α):
    R_ℓ(B_α) = ℓ^(α-2) B_α

  Therefore:
    R_ℓ(B_α) = B_α  ⟺  α = 2

  This is the cleanest Layer A target: pure algebra on scaling exponents.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace UnifiedTheory.LayerA

open Real

/-- A power-law potential B_α(r) = c * r^(-α) for r > 0. -/
noncomputable def powerLawPotential (c α : ℝ) (r : ℝ) : ℝ :=
  c * r ^ (-α)

/-- The renormalization operator R_ℓ acting on a radial function:
    (R_ℓ B)(r) = ℓ^(-2) B(r/ℓ). -/
noncomputable def renormOp (ℓ : ℝ) (B : ℝ → ℝ) (r : ℝ) : ℝ :=
  ℓ ^ ((-2 : ℝ)) * B (r / ℓ)

/-- R_ℓ applied to B_α yields ℓ^(α-2) · B_α.
    That is: (R_ℓ B_α)(r) = ℓ^(α-2) * c * r^(-α). -/
theorem renormOp_powerLaw (c α ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) :
    renormOp ℓ (powerLawPotential c α) r =
    ℓ ^ (α - 2) * powerLawPotential c α r := by
  simp only [renormOp, powerLawPotential]
  -- Goal: ℓ^(-2) * (c * (r/ℓ)^(-α)) = ℓ^(α-2) * (c * r^(-α))
  -- Step 1: rewrite r/ℓ = r * ℓ⁻¹ and split the rpow
  rw [div_eq_mul_inv]
  rw [mul_rpow hr.le (inv_nonneg.mpr hℓ.le)]
  -- Goal: ℓ^(-2) * (c * (r^(-α) * ℓ⁻¹^(-α))) = ℓ^(α-2) * (c * r^(-α))
  -- Step 2: simplify ℓ⁻¹^(-α) = ℓ^α
  have hinv : (ℓ⁻¹ : ℝ) ^ (-α) = ℓ ^ α := by
    rw [inv_rpow hℓ.le, rpow_neg hℓ.le, inv_inv]
  rw [hinv]
  -- Goal: ℓ^(-2) * (c * (r^(-α) * ℓ^α)) = ℓ^(α-2) * (c * r^(-α))
  -- Step 3: rearrange multiplications
  have hrearr : ℓ ^ ((-2 : ℝ)) * (c * (r ^ (-α) * ℓ ^ α)) =
                c * r ^ (-α) * (ℓ ^ ((-2 : ℝ)) * ℓ ^ α) := by ring
  rw [hrearr]
  -- Step 4: combine ℓ^(-2) * ℓ^α = ℓ^(α-2)
  rw [← rpow_add hℓ]
  -- Goal: c * r^(-α) * ℓ^(-2 + α) = ℓ^(α-2) * (c * r^(-α))
  have hexp : (-2 : ℝ) + α = α - 2 := by ring
  rw [hexp]
  ring

/-- The fixed-point theorem: R_ℓ(B_α) = B_α for all ℓ > 0
    if and only if α = 2. -/
theorem renorm_fixedPoint_iff (c : ℝ) (hc : c ≠ 0) (α : ℝ) :
    (∀ ℓ > 0, ∀ r > 0, renormOp ℓ (powerLawPotential c α) r =
      powerLawPotential c α r) ↔ α = 2 := by
  constructor
  · -- Forward: fixed point ⟹ α = 2
    intro h
    -- Specialize to ℓ = 2, r = 1
    have h21 := h 2 (by norm_num : (0 : ℝ) < 2) 1 (by norm_num : (0 : ℝ) < 1)
    rw [renormOp_powerLaw c α 2 1 (by norm_num) (by norm_num)] at h21
    -- h21 : 2^(α-2) * powerLawPotential c α 1 = powerLawPotential c α 1
    simp only [powerLawPotential, one_rpow, mul_one] at h21
    -- h21 : 2^(α-2) * c = c
    -- Extract 2^(α-2) = 1 using c ≠ 0
    have hpow : (2 : ℝ) ^ (α - 2) = 1 := by
      have h1 : (2 : ℝ) ^ (α - 2) * c = 1 * c := by rw [one_mul]; exact h21
      exact mul_right_cancel₀ hc h1
    -- Use logarithm: 2^(α-2) = 1 ⟹ (α-2) * log 2 = 0 ⟹ α-2 = 0
    have hlog := Real.log_rpow (show (0 : ℝ) < 2 by norm_num) (α - 2)
    rw [hpow, Real.log_one] at hlog
    -- hlog : 0 = (α - 2) * Real.log 2
    have hlog2 : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hα : α - 2 = 0 := (mul_eq_zero.mp hlog.symm).resolve_right hlog2
    linarith
  · -- Backward: α = 2 ⟹ fixed point
    intro hα
    subst hα
    intro ℓ hℓ r hr
    rw [renormOp_powerLaw c 2 ℓ r hℓ hr]
    norm_num

end UnifiedTheory.LayerA
