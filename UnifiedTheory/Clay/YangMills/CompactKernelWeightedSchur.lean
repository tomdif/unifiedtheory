/- A positive eigenfunction gives the sharp L2 Schur bound for a symmetric
nonnegative kernel. No ratio bound on that eigenfunction is used. -/
import UnifiedTheory.Clay.YangMills.CompactKernelDomination
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactKernelWeightedSchur
noncomputable section
open MeasureTheory CompactKernelOperator WilsonPositiveGroundState CompactDensityEntropy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem weighted_row (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (g f : C(X, ℝ)) (hg : ∀ x, 0 < g x) (x : X) :
    (realSmoothing μ K f x)^2 ≤
      (∫ y, K (x, y) * g y ∂μ)*(∫ y, K (x, y)*(f y)^2/g y ∂μ) := by
  let a := fun y => Real.sqrt (K (x, y))*Real.sqrt (g y)
  let b := fun y => Real.sqrt (K (x, y))*f y/Real.sqrt (g y)
  have hk : Continuous (fun y => K (x, y)) :=
    K.continuous.comp (continuous_const.prodMk continuous_id)
  have ha : Continuous a := hk.sqrt.mul g.continuous.sqrt
  have hb : Continuous b := (hk.sqrt.mul f.continuous).div g.continuous.sqrt
    (fun y => (Real.sqrt_pos.mpr (hg y)).ne')
  have hab (y : X) : a y*b y = K (x, y)*f y := by
    dsimp [a, b]
    field_simp [(Real.sqrt_pos.mpr (hg y)).ne']
    rw [Real.sq_sqrt (hK x y)]
    ring
  have ha2 (y : X) : (a y)^2 = K (x, y) * g y := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hK x y), Real.sq_sqrt (hg y).le]
  have hb2 (y : X) : (b y)^2 = K (x, y)*(f y)^2/g y := by
    dsimp [b]
    rw [div_pow, mul_pow, Real.sq_sqrt (hK x y), Real.sq_sqrt (hg y).le]
  have h := integral_product_sq μ a b ha hb
  simp_rw [hab, ha2, hb2] at h
  rwa [realSmoothing_integral]

variable [SecondCountableTopology X]

theorem weighted_square_bound (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (hs : ∀ x y, K (x, y) = K (y, x)) (g : C(X, ℝ)) (hg : ∀ x, 0 < g x)
    (c : ℝ) (he : ∀ x, (∫ y, K (x, y) * g y ∂μ) = c * g x) (f : C(X, ℝ)) :
    (∫ x, (realSmoothing μ K f x)^2 ∂μ) ≤ c^2*(∫ x, (f x)^2 ∂μ) := by
  let H := fun z : X × X => c * g z.1*K z*(f z.2)^2/g z.2
  have hH : Continuous H := by
    exact ((((continuous_const.mul (g.continuous.comp continuous_fst)).mul K.continuous).mul
      ((f.continuous.comp continuous_snd).pow 2)).div
      (g.continuous.comp continuous_snd) (fun z => (hg z.2).ne'))
  have hi : Integrable H (μ.prod μ) := continuous_integrable (μ.prod μ) _ hH
  have hr : Continuous (fun x => ∫ y, H (x, y) ∂μ) :=
    GibbsMarginalTower.fiber_integral_continuous μ H hH
  have hrow (x : X) : (realSmoothing μ K f x)^2 ≤ ∫ y, H (x, y) ∂μ := by
    have h := weighted_row μ K hK g f hg x
    rw [he x] at h
    apply h.trans_eq
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [H]
    ring
  have h := integral_mono (continuous_integrable μ _ ((realSmoothing μ K f).continuous.pow 2))
    (continuous_integrable μ _ hr) hrow
  have hmass : (∫ x, ∫ y, H (x, y) ∂μ ∂μ) = c^2*(∫ x, (f x)^2 ∂μ) := by
    rw [integral_integral_swap (f := fun x y => H (x, y)) hi]
    have hy (y : X) : (∫ x, H (x, y) ∂μ) = c^2*(f y)^2 := by
      have heq (x : X) : H (x, y) = (c*(f y)^2/g y)*(K (y, x)*g x) := by
        dsimp [H]
        rw [hs x y]
        ring
      simp_rw [heq]
      rw [integral_const_mul, he y]
      field_simp [(hg y).ne']
    simp_rw [hy]
    exact integral_const_mul _ _
  exact h.trans_eq hmass

variable [NormalSpace X] [μ.WeaklyRegular]

theorem norm_le (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (hs : ∀ x y, K (x, y) = K (y, x)) (g : C(X, ℝ)) (hg : ∀ x, 0 < g x)
    (c : ℝ) (hc : 0 ≤ c) (he : ∀ x, (∫ y, K (x, y) * g y ∂μ) = c * g x) :
    ‖operator μ K‖ ≤ c :=
  CompactKernelDomination.norm_le_of_real_sq μ K hK c hc
    (weighted_square_bound μ K hK hs g hg c he)

end
end UnifiedTheory.Clay.YangMills.CompactKernelWeightedSchur
