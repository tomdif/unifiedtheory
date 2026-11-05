/- **The convex RG step restricted to a convex small-field domain.** In a multiscale argument
the fine integral runs over a small-field region `D` rather than the whole space, and the action
is only known to be convex there. If `D ⊆ X × E` is convex and `V − c‖y‖²` is convex on `D`, then
`1_D · e^{−V}` is still log-concave (`logConcave_indicator`). So by Prékopa (`PrekopaSpace`) the
coarse action `U(y) = −log ∫_{D_y} e^{−V(x,y)} dμ(x)` has `U − c‖y‖²` convex on any convex set `S`
of coarse fields where the restricted marginal is finite and nonzero (`prekopa_rg_step_domain`).
This lets the convexity results apply to a region like `{‖dA‖_∞ ≤ ε}` in linear coordinates, which
is convex. It does not say how the complement (the large fields) is handled. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain

open MeasureTheory Set
open UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

/-- The restricted Boltzmann weight `1_D e^{−W}` is log-concave when `D` is convex and `W` is
convex on `D`. -/
theorem logConcave_indicator {X : Type*} [AddCommGroup X] [Module ℝ X] (D : Set X)
    (hD : Convex ℝ D) (W : X → ℝ) (hW : ConvexOn ℝ D W) :
    LogConcave (D.indicator fun x => ENNReal.ofReal (Real.exp (-W x))) := by
  intro x x' lam hl0 hl1
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  by_cases hx : x ∈ D
  · by_cases hx' : x' ∈ D
    · have hm : lam • x + (1 - lam) • x' ∈ D := hD hx hx' hl0.le hl1'.le (by ring)
      rw [indicator_of_mem hx, indicator_of_mem hx', indicator_of_mem hm,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl0.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl1'.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
      have := hW.2 hx hx' hl0.le hl1'.le (by ring)
      simp only [smul_eq_mul] at this
      linarith
    · rw [indicator_of_notMem hx', ENNReal.zero_rpow_of_pos hl1', mul_zero]
      exact zero_le _
  · rw [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hl0, zero_mul]
    exact zero_le _

/-- A log-concave function that is finite and nonzero on a convex set `S` has a convex negative
logarithm on `S`. -/
theorem convex_neg_log_on {E : Type*} [AddCommGroup E] [Module ℝ E] (Z : E → ENNReal)
    (hZ : LogConcave Z) (S : Set E) (hS : Convex ℝ S) (hfin : ∀ y ∈ S, Z y ≠ ⊤)
    (hpos : ∀ y ∈ S, Z y ≠ 0) :
    ConvexOn ℝ S (fun y => -Real.log (Z y).toReal) := by
  refine ⟨hS, fun y1 h1 y2 h2 a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : b = 1 - a := by linarith
  have hm : a • y1 + (1 - a) • y2 ∈ S := hS h1 h2 ha hb (by ring)
  have key := ENNReal.toReal_mono (hfin _ hm) (hZ y1 y2 a ha' (by linarith))
  have p1 : 0 < (Z y1).toReal := ENNReal.toReal_pos (hpos _ h1) (hfin _ h1)
  have p2 : 0 < (Z y2).toReal := ENNReal.toReal_pos (hpos _ h2) (hfin _ h2)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at key
  have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos p1 _) (Real.rpow_pos_of_pos p2 _)) key
  rw [Real.log_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
    Real.log_rpow p1, Real.log_rpow p2] at hl
  simp only [smul_eq_mul]
  linarith

/-- The restricted marginal `∫_{D_y} e^{−V(x,y)} dμ(x)`. -/
noncomputable def ZD {X E : Type*} [MeasurableSpace X] (μ : Measure X) (D : Set (X × E))
    (V : X → E → ℝ) (y : E) : ENNReal :=
  ∫⁻ x, D.indicator (fun p => ENNReal.ofReal (Real.exp (-V p.1 p.2))) (x, y) ∂μ

/-- **The convex RG step on a convex small-field domain.** -/
theorem prekopa_rg_step_domain {X : Type} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PrekopaSpace X μ) {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (D : Set (X × E)) (hD : Convex ℝ D)
    (hDm : ∀ y, MeasurableSet {x | (x, y) ∈ D}) (V : X → E → ℝ) (c : ℝ)
    (hV : ConvexOn ℝ D (fun p : X × E => V p.1 p.2 - c * ‖p.2‖ ^ 2))
    (hVm : ∀ y, Measurable fun x => V x y) (S : Set E) (hS : Convex ℝ S)
    (hfin : ∀ y ∈ S, ZD μ D V y ≠ ⊤) (hpos : ∀ y ∈ S, ZD μ D V y ≠ 0) :
    ConvexOn ℝ S (fun y => -Real.log (ZD μ D V y).toReal - c * ‖y‖ ^ 2) := by
  set W : X → E → ℝ := fun x y => V x y - c * ‖y‖ ^ 2
  have hZ : ∀ y, ZD μ D W y = ENNReal.ofReal (Real.exp (c * ‖y‖ ^ 2)) * ZD μ D V y := by
    intro y
    simp only [ZD]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x
    by_cases hxy : (x, y) ∈ D
    · simp only [indicator_of_mem hxy, W]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    · simp [indicator_of_notMem hxy]
  have hlc : LogConcave (ZD μ D W) := by
    refine hX E (D.indicator fun p => ENNReal.ofReal (Real.exp (-W p.1 p.2)))
      (logConcave_indicator D hD (fun p => W p.1 p.2) hV) fun y => ?_
    have hm : Measurable fun x => ENNReal.ofReal (Real.exp (-W x y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((hVm y).sub_const (c * ‖y‖ ^ 2)).neg :)
    exact (hm.indicator (hDm y) : Measurable ({x | (x, y) ∈ D}.indicator _))
  have hWfin : ∀ y ∈ S, ZD μ D W y ≠ ⊤ := fun y hy => by
    rw [hZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin y hy)
  have hWpos : ∀ y ∈ S, ZD μ D W y ≠ 0 := fun y hy => by
    rw [hZ]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hpos y hy)
  have key := convex_neg_log_on _ hlc S hS hWfin hWpos
  refine ⟨hS, fun y1 h1 y2 h2 a b ha hb hab => ?_⟩
  have k := key.2 h1 h2 ha hb hab
  have e : ∀ y ∈ S, -Real.log (ZD μ D W y).toReal
      = -Real.log (ZD μ D V y).toReal - c * ‖y‖ ^ 2 := by
    intro y hy
    rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos (hpos y hy) (hfin y hy)).ne',
      Real.log_exp]
    ring
  simp only at k ⊢
  rwa [e _ (hS h1 h2 ha hb hab), e _ h1, e _ h2] at k

end UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaDomain
