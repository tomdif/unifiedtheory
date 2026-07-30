/-
  Audit/KFCausalMinkowski4DRealModes.lean
  — REAL MODES OF THE RETARDED SYMBOL (Hermite–Biehler rung 1)

  The Hermite–Biehler program asks whether the physically forced Mellin
  zeros of the BDG kernel are compatible with a retarded symbol that is
  zero-free in the upper half plane (stability).  This file formalizes the
  first rung: the REAL exponential modes.

  On a real growing test mode `e^{st}` (s > 0), the mean retarded symbol at
  the origin is `(4/√6)ℓ⁻²·(G(s) − 1)` with

      G(s) = ∫_{past cone} f4D((π/24)τ⁴)·e^{−s|t|} d⁴y
           = 4π ∫₀^∞ e^{−st} ∫₀^t r²·f4D((π/24)(t²−r²)²) dr dt

  (kernel units).  A real growing mode exists iff G(s) = 1.  Known anchors:
  G(0) = 1 exactly (constants are zero modes — the committed operator
  theorem), and numerically G(s) < 1 strictly on all of (0, ∞) with
  G(s) ≈ 1 − 0.6·s² near zero (the continuum −s² limit).

  Proved here, rigorously:

  1.  `f4D_abs_le`:  |f4D(ξ)| ≤ 9 for ξ ≥ 0 (via the committed quartic
      exponential lower bound and an explicit SOS decomposition).
  2.  `realModeSymbol_UV`:  |G(s)| ≤ 216π/s⁴, hence  G(s) < 1  for every
      s ≥ 6:  **no real growing modes above the discreteness frequency** —
      any instability of the 4D operator is necessarily oscillatory-growing
      (complex), sharpening the Aslanbeigi–Saravani–Sorkin observation.

  The remaining window s ∈ (0, 6) is numerically verified (max G = 0.9998,
  attained at s → 0⁺) and is the target for interval-arithmetic closure; the
  full Hermite–Biehler no-go (complex zeros forced) remains the open
  conjecture.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate

set_option autoImplicit false

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate

namespace UnifiedTheory.Audit.KFCausalMinkowski4DRealModes

/-- **Global kernel bound**: `|f4D(ξ)| ≤ 9` for `ξ ≥ 0`. -/
theorem f4D_abs_le (ξ : ℝ) (hξ : 0 ≤ ξ) : |f4D ξ| ≤ 9 := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hP : |1 - 9*ξ + 8*ξ^2 - (4/3)*ξ^3| ≤ 1 + 9*ξ + 8*ξ^2 + (4/3)*ξ^3 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg ξ, mul_nonneg hξ (sq_nonneg ξ), hξ]
    · nlinarith [sq_nonneg ξ, mul_nonneg hξ (sq_nonneg ξ), hξ]
  have hexp := exp_quartic_lower ξ hξ
  have hkey : 1 + 9*ξ + 8*ξ^2 + (4/3)*ξ^3 ≤ 9 * Real.exp ξ := by
    nlinarith [hexp, sq_nonneg (ξ^2 - 4), mul_nonneg hξ (sq_nonneg (ξ - 2)),
      sq_nonneg (ξ - 2)]
  calc Real.exp (-ξ) * |1 - 9*ξ + 8*ξ^2 - (4/3)*ξ^3|
      ≤ Real.exp (-ξ) * (9 * Real.exp ξ) :=
        mul_le_mul_of_nonneg_left (le_trans hP hkey) (Real.exp_pos _).le
    _ = 9 := by
        rw [show Real.exp (-ξ) * (9 * Real.exp ξ)
            = 9 * (Real.exp (-ξ) * Real.exp ξ) from by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The real-mode symbol: the mean of the retarded kernel on the growing
test mode `e^{st}`, kernel units.  `G(0) = 1` (constants are zero modes);
a real growing instability at rate `s` exists iff `G(s) = 1`. -/
noncomputable def realModeSymbol (s : ℝ) : ℝ :=
  4*π * ∫ t in Ioi (0:ℝ), Real.exp (-(s*t)) *
    ∫ r in (0:ℝ)..t, r^2 * f4D ((π/24)*(t^2 - r^2)^2)

/-- **No real growing modes above the discreteness frequency**:
`|G(s)| ≤ 216π/s⁴ < 1` for `s ≥ 6`. -/
theorem realModeSymbol_UV (s : ℝ) (hs : 6 ≤ s) : realModeSymbol s < 1 := by
  have hs0 : (0:ℝ) < s := by linarith
  -- dominator: 9·e^{−st}·t³, integrable with integral 54/s⁴
  have hdom : IntegrableOn (fun t : ℝ => 9 * (Real.exp (-(s*t)) * t^3))
      (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1:ℝ) < 3) (le_refl (1:ℝ)) hs0
    have h9 := h.const_mul (9:ℝ)
    apply MeasureTheory.IntegrableOn.congr_fun h9 ?_ measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [Real.rpow_one, show (x:ℝ)^(3:ℝ) = x^(3:ℕ) from by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast],
      neg_mul]
    ring
  have hval : (∫ t in Ioi (0:ℝ), 9 * (Real.exp (-(s*t)) * t^3)) = 54/s^4 := by
    rw [MeasureTheory.integral_const_mul]
    have hcongr : (∫ t in Ioi (0:ℝ), Real.exp (-(s*t)) * t^3)
        = ∫ t in Ioi (0:ℝ), t^((4:ℝ)-1) * Real.exp (-(s*t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [mem_Ioi] at ht
      dsimp only
      rw [show (4:ℝ)-1 = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
      ring
    rw [hcongr, Real.integral_rpow_mul_exp_neg_mul_Ioi
      (by norm_num : (0:ℝ) < 4) hs0]
    rw [show ((1:ℝ)/s)^(4:ℝ) = (1/s)^(4:ℕ) from by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast],
      show Real.Gamma 4 = 6 from by
        rw [show (4:ℝ) = (2:ℝ)+2 from by norm_num]
        exact G_2_2]
    field_simp
    ring
  -- the outer integrand is dominated
  have hbound : ∀ t ∈ Ioi (0:ℝ),
      ‖Real.exp (-(s*t)) * ∫ r in (0:ℝ)..t,
        r^2 * f4D ((π/24)*(t^2 - r^2)^2)‖
      ≤ 9 * (Real.exp (-(s*t)) * t^3) := by
    intro t ht
    rw [mem_Ioi] at ht
    have hinner : ‖∫ r in (0:ℝ)..t, r^2 * f4D ((π/24)*(t^2 - r^2)^2)‖
        ≤ 9*t^2 * |t - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      rw [Set.uIoc_of_le ht.le] at hr
      have hr0 : 0 < r := hr.1
      have hrt : r ≤ t := hr.2
      have hz : (0:ℝ) ≤ (π/24)*(t^2 - r^2)^2 := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
      calc r^2 * |f4D ((π/24)*(t^2 - r^2)^2)|
          ≤ r^2 * 9 := mul_le_mul_of_nonneg_left (f4D_abs_le _ hz) (sq_nonneg r)
        _ ≤ t^2 * 9 := by nlinarith [hr0, hrt]
        _ = 9*t^2 := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [Real.norm_eq_abs] at hinner
    rw [show |t - 0| = t from by rw [sub_zero, abs_of_pos ht]] at hinner
    calc Real.exp (-(s*t)) * |∫ r in (0:ℝ)..t,
          r^2 * f4D ((π/24)*(t^2 - r^2)^2)|
        ≤ Real.exp (-(s*t)) * (9*t^2*t) :=
          mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
      _ = 9 * (Real.exp (-(s*t)) * t^3) := by ring
  have hG : |∫ t in Ioi (0:ℝ), Real.exp (-(s*t)) *
      ∫ r in (0:ℝ)..t, r^2 * f4D ((π/24)*(t^2 - r^2)^2)| ≤ 54/s^4 := by
    rw [← Real.norm_eq_abs, ← hval]
    exact MeasureTheory.norm_integral_le_of_norm_le hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  unfold realModeSymbol
  have hπ : (0:ℝ) < π := Real.pi_pos
  calc 4*π * ∫ t in Ioi (0:ℝ), Real.exp (-(s*t)) *
        ∫ r in (0:ℝ)..t, r^2 * f4D ((π/24)*(t^2 - r^2)^2)
      ≤ 4*π * (54/s^4) :=
        mul_le_mul_of_nonneg_left
          (le_trans (le_abs_self _) hG) (by positivity)
    _ < 1 := by
        rw [show 4*π*(54/s^4) = 216*π/s^4 from by ring,
          div_lt_one (by positivity)]
        have hs4 : (1296:ℝ) ≤ s^4 := by
          calc (1296:ℝ) = 6^4 := by norm_num
            _ ≤ s^4 := pow_le_pow_left₀ (by norm_num) hs 4
        nlinarith [Real.pi_le_four, hs4]

/-- **The rung-1 statement**: for `s ≥ 6` the retarded symbol on real
growing modes is strictly negative — any instability of the 4D BDG operator
is necessarily oscillatory-growing (complex-frequency), never a pure real
exponential runaway at super-discreteness rates. -/
theorem no_real_growing_modes_UV (s : ℝ) (hs : 6 ≤ s) :
    realModeSymbol s - 1 < 0 := by
  have := realModeSymbol_UV s hs
  linarith

#print axioms f4D_abs_le
#print axioms realModeSymbol_UV
#print axioms no_real_growing_modes_UV

end UnifiedTheory.Audit.KFCausalMinkowski4DRealModes
