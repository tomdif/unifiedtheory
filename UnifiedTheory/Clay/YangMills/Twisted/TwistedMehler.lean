/- The free transfer kernel of one mode with stiffness `κ`, with explicit eigenfunctions.
The Gaussian and the Gaussian times `x` are eigenfunctions with ratio `ρ`, where
`ρ + 1/ρ = κ + 2`, independent of the coupling. At `κ = 4 sin²(π/2N)` this gives
`√2/N ≤ -log ρ ≤ π/N`. These are eigenfunction identities for a model, not a spectral theorem for
the Wilson operator, and they do not show these are the two top eigenvalues. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler
noncomputable section
open MeasureTheory Real

/-- Shifted Gaussian integral. -/
theorem gaussian_shift (A m : ℝ) (hA : 0 < A) :
    ∫ y, Real.exp (-A * (y - m) ^ 2) = Real.sqrt (Real.pi / A) := by
  rw [integral_sub_right_eq_self (fun y => Real.exp (-A * y ^ 2)) m]
  exact integral_gaussian A

theorem integrable_shift (A m : ℝ) (hA : 0 < A) :
    Integrable fun y => Real.exp (-A * (y - m) ^ 2) :=
  (integrable_exp_neg_mul_sq hA).comp_sub_right m

/-- The first moment of a shifted Gaussian. -/
theorem gaussian_moment (A m : ℝ) (hA : 0 < A) :
    ∫ y, y * Real.exp (-A * (y - m) ^ 2) = m * Real.sqrt (Real.pi / A) := by
  have hodd : ∫ y, y * Real.exp (-A * y ^ 2) = 0 := by
    have h := integral_neg_eq_self (fun y : ℝ => y * Real.exp (-A * y ^ 2)) volume
    have e : ∫ y, (-y) * Real.exp (-A * (-y) ^ 2) = -∫ y, y * Real.exp (-A * y ^ 2) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [neg_sq]
    rw [e] at h
    linarith only [h]
  have hint : Integrable fun y : ℝ => y * Real.exp (-A * y ^ 2) := by
    have := integrable_mul_exp_neg_mul_sq hA
    exact this
  have hsplit : ∀ y : ℝ, (y + m) * Real.exp (-A * y ^ 2) =
      y * Real.exp (-A * y ^ 2) + m * Real.exp (-A * y ^ 2) := fun y => by ring
  calc ∫ y, y * Real.exp (-A * (y - m) ^ 2)
      = ∫ y, (y + m) * Real.exp (-A * y ^ 2) := by
        rw [← integral_sub_right_eq_self (fun y => (y + m) * Real.exp (-A * y ^ 2)) m]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp
    _ = _ := by
        simp only [hsplit]
        rw [integral_add hint ((integrable_exp_neg_mul_sq hA).const_mul m), hodd, zero_add,
          integral_const_mul, integral_gaussian]

/-- The free one-mode kernel. -/
def kernel (β κ x y : ℝ) : ℝ :=
  Real.exp (-(β * κ / 4) * x ^ 2 - (β * κ / 4) * y ^ 2 - β / 2 * (x - y) ^ 2)

/-- The Gaussian exponent attached to the ratio `ρ`. -/
def expo (β ρ : ℝ) : ℝ := β * (1 - ρ ^ 2) / (4 * ρ)

/-- The eigenvalue of the ground mode. -/
def lam (β ρ : ℝ) : ℝ := Real.sqrt (Real.pi / (β / (2 * ρ)))

variable (β κ ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hrel : ρ + 1 / ρ = κ + 2)

include hβ hρ hrel

/-- Completing the square in the exponent. -/
theorem exponent_identity (x y : ℝ) :
    -(β * κ / 4) * x ^ 2 - (β * κ / 4) * y ^ 2 - β / 2 * (x - y) ^ 2 - expo β ρ * y ^ 2 =
      -(β / (2 * ρ)) * (y - ρ * x) ^ 2 - expo β ρ * x ^ 2 := by
  have hκ : κ = ρ + 1 / ρ - 2 := by linarith only [hrel]
  subst hκ
  unfold expo
  field_simp
  ring

/-- **The ground mode.** -/
theorem eigen_ground (x : ℝ) :
    ∫ y, kernel β κ x y * Real.exp (-expo β ρ * y ^ 2) = lam β ρ * Real.exp (-expo β ρ * x ^ 2) := by
  have hA : 0 < β / (2 * ρ) := by positivity
  have he (y : ℝ) : kernel β κ x y * Real.exp (-expo β ρ * y ^ 2) =
      Real.exp (-expo β ρ * x ^ 2) * Real.exp (-(β / (2 * ρ)) * (y - ρ * x) ^ 2) := by
    unfold kernel
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have := exponent_identity β κ ρ hβ hρ hrel x y
    linarith only [this]
  simp only [he]
  rw [integral_const_mul, gaussian_shift _ _ hA]
  unfold lam
  ring

/-- **The first excited mode.** The eigenvalue ratio is exactly `ρ`. -/
theorem eigen_excited (x : ℝ) :
    ∫ y, kernel β κ x y * (y * Real.exp (-expo β ρ * y ^ 2)) =
      (ρ * lam β ρ) * (x * Real.exp (-expo β ρ * x ^ 2)) := by
  have hA : 0 < β / (2 * ρ) := by positivity
  have he (y : ℝ) : kernel β κ x y * (y * Real.exp (-expo β ρ * y ^ 2)) =
      Real.exp (-expo β ρ * x ^ 2) * (y * Real.exp (-(β / (2 * ρ)) * (y - ρ * x) ^ 2)) := by
    unfold kernel
    have h2 : Real.exp (-(β * κ / 4) * x ^ 2 - (β * κ / 4) * y ^ 2 - β / 2 * (x - y) ^ 2) *
        Real.exp (-expo β ρ * y ^ 2) = Real.exp (-expo β ρ * x ^ 2) *
          Real.exp (-(β / (2 * ρ)) * (y - ρ * x) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      have := exponent_identity β κ ρ hβ hρ hrel x y
      linarith only [this]
    calc _ = y * (Real.exp (-(β * κ / 4) * x ^ 2 - (β * κ / 4) * y ^ 2 - β / 2 * (x - y) ^ 2) *
          Real.exp (-expo β ρ * y ^ 2)) := by ring
      _ = _ := by rw [h2]; ring
  simp only [he]
  rw [integral_const_mul, gaussian_moment _ _ hA]
  unfold lam
  ring

omit hβ hρ hrel

/-- **Lattice dispersion.** With `ρ = e^{-ω}`, the relation `ρ + 1/ρ = κ + 2` says `4 sinh²(ω/2) = κ`. -/
theorem dispersion (ω κ : ℝ) (h : Real.exp (-ω) + 1 / Real.exp (-ω) = κ + 2) :
    4 * Real.sinh (ω / 2) ^ 2 = κ := by
  have h1 : 1 / Real.exp (-ω) = Real.exp ω := by
    rw [Real.exp_neg]
    simp
  rw [h1] at h
  have hs := Real.cosh_two_mul (ω / 2)
  rw [show 2 * (ω / 2) = ω by ring, Real.cosh_eq ω] at hs
  have hc := Real.cosh_sq (ω / 2)
  linarith only [h, hs, hc]

/-- **The window.** If `sinh(ω/2) = sin(π/2N)` then `√2/N ≤ ω ≤ π/N`. -/
theorem window (N : ℝ) (hN : 1 ≤ N) (ω : ℝ) (hω : 0 ≤ ω)
    (h : Real.sinh (ω / 2) = Real.sin (Real.pi / (2 * N))) :
    Real.sqrt 2 / N ≤ ω ∧ ω ≤ Real.pi / N := by
  have hNpos : 0 < N := by linarith only [hN]
  set x := ω / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  set θ := Real.pi / (2 * N) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ Real.pi / 2 := by
    rw [hθ]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith only [hN]
  have hsinθ : Real.sin θ ≤ θ := Real.sin_le hθ0
  have hsinlow := Real.mul_le_sin hθ0 hθ1
  have e1 : 2 / Real.pi * θ = 1 / N := by
    rw [hθ]
    have := Real.pi_pos.ne'
    field_simp
  rw [e1] at hsinlow
  have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0
  have hupper : ω ≤ Real.pi / N := by
    have : x ≤ θ := by
      rw [h] at hxs
      linarith only [hxs, hsinθ]
    have e : ω = 2 * x := by rw [hx]; ring
    have e2 : Real.pi / N = 2 * θ := by
      rw [hθ]
      field_simp
    rw [e, e2]
    linarith only [this]
  refine ⟨?_, hupper⟩
  -- `sinh x ≤ x cosh x` and `cosh² x = 1 + sinh² x ≤ 2`
  have hs1 : Real.sinh x ≤ 1 := by
    rw [h]
    exact Real.sin_le_one _
  have hs0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  have hcsq : Real.cosh x ^ 2 ≤ 2 := by
    rw [Real.cosh_sq]
    nlinarith only [hs0, hs1]
  have hcle : Real.cosh x ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le hcsq
  have hsx : Real.sinh x ≤ x * Real.cosh x := by
    -- the mean value bound for `sinh` on `[0, x]`
    have hmv : ∀ y ∈ Set.Icc 0 x, Real.cosh y ≤ Real.cosh x := fun y hy => by
      rw [Real.cosh_le_cosh, abs_of_nonneg hy.1, abs_of_nonneg hx0]
      exact hy.2
    have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.sinh) (f' := Real.cosh)
      (s := Set.Icc 0 x) (C := Real.cosh x) (x := 0) (y := x)
      (fun y _ => (Real.hasDerivAt_sinh y).hasDerivWithinAt)
      (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos y)]
        exact hmv y hy)
      (convex_Icc 0 x) (Set.left_mem_Icc.mpr hx0) (Set.right_mem_Icc.mpr hx0)
    simp only [Real.sinh_zero, sub_zero, Real.norm_eq_abs] at hd
    rw [abs_of_nonneg hs0, abs_of_nonneg hx0] at hd
    linarith only [hd]
  have hs2 : 1 / N ≤ x * Real.sqrt 2 := by
    have h3 : Real.sinh x ≤ x * Real.sqrt 2 := hsx.trans (mul_le_mul_of_nonneg_left hcle hx0)
    rw [h] at h3
    linarith only [h3, hsinlow]
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hω2 : ω = 2 * x := by rw [hx]; ring
  rw [hω2, div_le_iff₀ hNpos]
  have h4 := mul_le_mul_of_nonneg_left hs2 hsq0.le
  have e4 : Real.sqrt 2 * (1 / N) * N = Real.sqrt 2 := by field_simp
  have h5 := mul_le_mul_of_nonneg_right h4 hNpos.le
  rw [e4] at h5
  have e5 : Real.sqrt 2 * (x * Real.sqrt 2) * N = 2 * x * N := by
    calc _ = (Real.sqrt 2 * Real.sqrt 2) * x * N := by ring
      _ = _ := by rw [hsq2]
  rw [e5] at h5
  exact h5

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler
