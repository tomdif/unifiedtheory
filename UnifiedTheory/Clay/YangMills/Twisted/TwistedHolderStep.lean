/- The upper half of the convex RG step. `TwistedPrekopaMulti.prekopa_rg_step_multi` shows that integrating out
fine variables preserves a lower bound on the coarse Hessian: if `V(x, y) − c‖y‖²` is jointly convex, then
`U(y) = −log ∫ e^{−V(x,y)} dμ(x)` has `U − c‖y‖²` convex. To iterate an RG step the effective action must keep
its form, which needs an upper bound too. That half follows from Hölder's inequality, not Prékopa: integrals
of log-convex functions are log-convex. So if `y ↦ V(x, y) − C‖y‖²` is concave for every fine field `x` (a bound
`∂²_y V ≤ 2C`, uniform in `x`, with no joint condition), then `U − C‖y‖²` is concave. Together the two halves show
that one convex step preserves both Hessian bounds `2c ≤ ∂²U ≤ 2C` exactly. In particular the condition number
does not grow. This is still the small-field (convex) step only. The large-field region and the SU(2) chart are
not covered. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedHolderStep

open MeasureTheory Set
open UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

/-- Log-convexity of an `ℝ≥0∞`-valued function on a real vector space. -/
def LogConvex {X : Type*} [AddCommGroup X] [Module ℝ X] (F : X → ENNReal) : Prop :=
  ∀ (x x' : X) (lam : ℝ), 0 < lam → lam < 1 →
    F (lam • x + (1 - lam) • x') ≤ F x ^ lam * F x' ^ (1 - lam)

/-- **Integrals of log-convex functions are log-convex** (Hölder with exponents `1/λ` and
`1/(1−λ)`). -/
theorem logConvex_lintegral {X E : Type*} [MeasurableSpace X] [AddCommGroup E] [Module ℝ E]
    (μ : Measure X) (F : X → E → ENNReal) (hF : ∀ x, LogConvex (F x))
    (hm : ∀ y, AEMeasurable (fun x => F x y) μ) : LogConvex (fun y => ∫⁻ x, F x y ∂μ) := by
  intro a b lam h0 h1
  have hpq := Real.HolderConjugate.inv_one_sub_inv h0 h1
  have h1' : 0 < 1 - lam := sub_pos.mpr h1
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x => F x a ^ lam) (g := fun x => F x b ^ (1 - lam))
    ((hm a).pow_const _) ((hm b).pow_const _)
  have ea : ∀ x, (F x a ^ lam) ^ lam⁻¹ = F x a := fun x => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ h0.ne', ENNReal.rpow_one]
  have eb : ∀ x, (F x b ^ (1 - lam)) ^ (1 - lam)⁻¹ = F x b := fun x => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ h1'.ne', ENNReal.rpow_one]
  simp only [ea, eb, one_div, inv_inv] at hH
  exact (lintegral_mono fun x => hF x a b lam h0 h1).trans hH

/-- The Boltzmann weight of a concave action is log-convex. -/
theorem logConvex_exp_neg {X : Type*} [AddCommGroup X] [Module ℝ X] (W : X → ℝ)
    (hW : ConcaveOn ℝ univ W) : LogConvex (fun x => ENNReal.ofReal (Real.exp (-W x))) := by
  intro x x' lam hl0 hl1
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl0.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl1'.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  have := hW.2 (mem_univ x) (mem_univ x') hl0.le hl1'.le (by ring)
  simp only [smul_eq_mul] at this
  linarith

/-- A finite, nonzero log-convex weight has concave `−log`. -/
theorem concave_neg_log {E : Type*} [AddCommGroup E] [Module ℝ E] (Z : E → ENNReal)
    (hZ : LogConvex Z) (hfin : ∀ y, Z y ≠ ⊤) (hpos : ∀ y, Z y ≠ 0) :
    ConcaveOn ℝ univ (fun y => -Real.log (Z y).toReal) := by
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : b = 1 - a := by linarith
  have key := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ha (hfin _))
    (ENNReal.rpow_ne_top_of_nonneg hb (hfin _))) (hZ y1 y2 a ha' (by linarith))
  have p1 : 0 < (Z y1).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  have p2 : 0 < (Z y2).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  have p3 : 0 < (Z (a • y1 + (1 - a) • y2)).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at key
  have hl := Real.log_le_log p3 key
  rw [Real.log_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
    Real.log_rpow p1, Real.log_rpow p2] at hl
  simp only [smul_eq_mul]
  linarith

/-- **One RG step preserves the upper Hessian bound.** If `y ↦ V(x, y) − C‖y‖²` is concave for
every fine field `x`, the coarse action `U(y) = −log ∫ e^{−V(x,y)} dμ(x)` has `U − C‖y‖²` concave.
No convexity in `x` and no Prékopa property of `μ` is needed. -/
theorem holder_rg_step_upper {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : X → E → ℝ) (C : ℝ)
    (hV : ∀ x, ConcaveOn ℝ univ (fun y => V x y - C * ‖y‖ ^ 2))
    (hVm : ∀ y, Measurable fun x => V x y)
    (hfin : ∀ y, ZM μ V y ≠ ⊤) (hpos : ∀ y, ZM μ V y ≠ 0) :
    ConcaveOn ℝ univ (fun y => -Real.log (ZM μ V y).toReal - C * ‖y‖ ^ 2) := by
  set W : X → E → ℝ := fun x y => V x y - C * ‖y‖ ^ 2
  have hZ : ∀ y, ZM μ W y = ENNReal.ofReal (Real.exp (C * ‖y‖ ^ 2)) * ZM μ V y := by
    intro y
    simp only [ZM, W]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hlc : LogConvex (ZM μ W) :=
    logConvex_lintegral μ (fun x y => ENNReal.ofReal (Real.exp (-W x y)))
      (fun x => logConvex_exp_neg _ (hV x))
      fun y => (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((hVm y).sub_const (C * ‖y‖ ^ 2)).neg)).aemeasurable
  have hWfin : ∀ y, ZM μ W y ≠ ⊤ := fun y => by
    rw [hZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin y)
  have hWpos : ∀ y, ZM μ W y ≠ 0 := fun y => by
    rw [hZ]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hpos y)
  have key := concave_neg_log _ hlc hWfin hWpos
  convert key using 2 with y
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos (hpos y) (hfin y)).ne', Real.log_exp]
  ring

/-- **The convex RG step preserves both Hessian bounds.** On a Prékopa space of fine variables,
if `V − c‖y‖²` is jointly convex and `y ↦ V(x, y) − C‖y‖²` is concave for every `x`, then the
coarse action satisfies `U − c‖y‖²` convex and `U − C‖y‖²` concave: `2c ≤ ∂²U ≤ 2C` in the sense
of convexity, with the same constants. -/
theorem rg_step_two_sided {X : Type} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PrekopaSpace X μ) {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : X → E → ℝ) (c C : ℝ)
    (hlow : ConvexOn ℝ univ (fun p : X × E => V p.1 p.2 - c * ‖p.2‖ ^ 2))
    (hup : ∀ x, ConcaveOn ℝ univ (fun y => V x y - C * ‖y‖ ^ 2))
    (hVm : ∀ y, Measurable fun x => V x y)
    (hfin : ∀ y, ZM μ V y ≠ ⊤) (hpos : ∀ y, ZM μ V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (ZM μ V y).toReal - c * ‖y‖ ^ 2) ∧
      ConcaveOn ℝ univ (fun y => -Real.log (ZM μ V y).toReal - C * ‖y‖ ^ 2) :=
  ⟨prekopa_rg_step_multi hX V c hlow hVm hfin hpos, holder_rg_step_upper V C hup hVm hfin hpos⟩

end UnifiedTheory.Clay.YangMills.Twisted.TwistedHolderStep
