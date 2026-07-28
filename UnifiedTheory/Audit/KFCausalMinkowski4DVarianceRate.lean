/-
  Audit/KFCausalMinkowski4DVarianceRate.lean — THE DIAGONAL VARIANCE RATE
  (fluctuation campaign, rung b: the masses and the generic substitution)

  The diagonal (Campbell) variance object at profile level is
  `√a·∬ (v−u)²·f4Dsq(au²v²)·F`.  Splitting `(v−u)² = u² + v² − 2uv`:
  the square channels converge to the fluctuation w-mass `(315/4)√π` times the
  edge integrals `∫u·F(u,0)du`, `∫v·F(0,v)dv`; the cross channel dies as
  `ln a/√a`.  This file provides the kernel-agnostic substitution and the
  `f4Dsq` masses; the channel limits and assembly follow.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder
import UnifiedTheory.Audit.KFCausalMinkowski4DLogRate

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder

namespace UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate

/-- The kernel-agnostic boost substitution (the `inner_sub` mechanism is pure
change of variables — no property of the kernel is used). -/
theorem inner_sub_generic (h : ℝ → ℝ) (G : ℝ → ℝ) (a u : ℝ)
    (ha : 0 < a) (hu : 0 < u) :
    Real.sqrt a * ∫ v in Ioi (0:ℝ), h (a*u^2*v^2) * G v
      = u⁻¹ * ∫ w in Ioi (0:ℝ), h (w^2) * G (w/(Real.sqrt a * u)) := by
  set c := Real.sqrt a * u with hcdef
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr ha) hu
  have hc2 : c^2 = a * u^2 := by rw [hcdef, mul_pow, Real.sq_sqrt ha.le]
  have hcomp := integral_comp_mul_left_Ioi
    (fun w => h (w^2) * G (w/c)) 0 hc
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcancel : (∫ x in Ioi (0:ℝ), (fun w => h (w^2) * G (w/c)) (c * x))
      = ∫ x in Ioi (0:ℝ), h (a*u^2*x^2) * G x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    show h ((c*x)^2) * G ((c*x)/c) = h (a*u^2*x^2) * G x
    rw [mul_div_cancel_left₀ x hc.ne', mul_pow, hc2]
  rw [hcancel] at hcomp
  dsimp only at hcomp
  rw [hcomp, hcdef]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  try ring

/-- `f4Dsq(w²)` is integrable on `(0,∞)` (Gaussian-type decay). -/
theorem f4Dsq_sq_integrable :
    IntegrableOn (fun w => f4Dsq (w^2)) (Ioi (0:ℝ)) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (0:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (0:ℝ))).integrableOn
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (2:ℝ))).integrableOn
  have h4 : IntegrableOn (fun x : ℝ => x ^ (4:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (4:ℝ))).integrableOn
  have h6 : IntegrableOn (fun x : ℝ => x ^ (6:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (6:ℝ))).integrableOn
  have hsum := ((h0.const_mul 1).add ((h2.const_mul 81).add
    ((h4.const_mul 128).add (h6.const_mul (32/3)))))
  apply MeasureTheory.IntegrableOn.congr_fun hsum ?_ measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  have e0 : w ^ (0:ℝ) = 1 := Real.rpow_zero w
  have e2 : w ^ (2:ℝ) = w ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e4 : w ^ (4:ℝ) = w ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e6 : w ^ (6:ℝ) = w ^ 6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  simp only [Pi.add_apply]
  rw [e0, e2, e4, e6]
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
  rw [show -(w^2) = -(1:ℝ) * w^2 from by ring]
  ring

/-- **The fluctuation w-mass**: `∫₀^∞ f4Dsq(w²) dw = (315/4)·√π` — one half of
the (nonzero!) Mellin mass at `s = ½`. -/
theorem f4Dsq_w_mass :
    (∫ w in Ioi (0:ℝ), f4Dsq (w^2)) = (315/4) * Real.sqrt π := by
  have hsub := integral_comp_rpow_Ioi
    (fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4Dsq ξ) (p := 2) (by norm_num)
  rw [f4Dsq_mass_half] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4Dsq ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * f4Dsq (x^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    have h21 : x ^ ((2:ℝ)-1) = x := by
      rw [show (2:ℝ)-1 = (1:ℝ) from by norm_num, Real.rpow_one]
    have hpow : (x ^ (2:ℝ)) ^ ((1:ℝ)/2 - 1) = x⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hx),
        show (2:ℝ) * ((1:ℝ)/2 - 1) = -1 from by norm_num, Real.rpow_neg_one]
    have hx2 : x ^ (2:ℝ) = x^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [h21, hpow, hx2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

#print axioms inner_sub_generic
#print axioms f4Dsq_w_mass

end UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate
