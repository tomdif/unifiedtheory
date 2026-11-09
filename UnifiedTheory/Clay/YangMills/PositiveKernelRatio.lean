/- A quantitative finite-volume eigenvalue-ratio estimate from actual kernel
bounds. The common Doob minorant is constructed from the positive ground
profile; no contraction estimate is assumed. -/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveKernelRatio
noncomputable section
open MeasureTheory Set

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The actual normalized ground-profile transition density. -/
def doob (K : C(X × X, ℝ)) (ψ : C(X, ℝ)) (lam : ℝ) (x y : X) : ℝ :=
  K (x, y) * ψ y / (lam * ψ x)

theorem profile_integral_pos (ψ : C(X, ℝ)) (hψ : ∀ x, 0 < ψ x) :
    0 < ∫ x, ψ x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hψ x).le)
    (ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support ψ = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (hψ x)
  simp [hs]

/-- The ground equation bounds its profile without a normalization assumption. -/
theorem profile_upper (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam M : ℝ)
    (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x) (x : X) :
    lam * ψ x ≤ M * ∫ y, ψ y ∂μ := by
  rw [← heig x, ← integral_const_mul]
  apply integral_mono
  · have hc : Continuous (fun y => K (x, y) * ψ y) :=
      (K.continuous.comp (continuous_const.prodMk continuous_id)).mul ψ.continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul ψ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  intro y
  exact mul_le_mul_of_nonneg_right (hupper x y) (hψ y).le

/-- A common reference law gives the sharper minorization m/M, not (m/M)². -/
theorem doob_minorant (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x) (x y : X) :
    (m / M) * (ψ y / (∫ z, ψ z ∂μ)) ≤ doob K ψ lam x y := by
  have hS := profile_integral_pos μ ψ hψ
  have hx : 0 < lam * ψ x := mul_pos hlam (hψ x)
  calc
    _ = m * ψ y / (M * ∫ z, ψ z ∂μ) := by ring
    _ ≤ K (x, y) * ψ y / (M * ∫ z, ψ z ∂μ) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hlower x y) (hψ y).le) (mul_pos hM hS).le
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (hm.le.trans (hlower x y)) (hψ y).le) hx
      (profile_upper μ K ψ hψ lam M hupper heig x)

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem doob_mass (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam : ℝ) (hlam : 0 < lam)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x) (x : X) :
    (∫ y, doob K ψ lam x y ∂μ) = 1 := by
  simp only [doob]
  rw [integral_div, heig]
  exact div_self (mul_ne_zero hlam.ne' (hψ x).ne')

/-- The remainder after removing the common minorant. -/
def residual (K : C(X × X, ℝ)) (ψ : C(X, ℝ)) (lam m M : ℝ) (x y : X) : ℝ :=
  doob K ψ lam x y - (m / M) * (ψ y / (∫ z, ψ z ∂μ))

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem residual_continuous (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (lam m M : ℝ) (x : X) : Continuous (residual μ K ψ lam m M x) := by
  unfold residual doob
  have hc : Continuous (fun y => K (x, y) * ψ y) :=
      (K.continuous.comp (continuous_const.prodMk continuous_id)).mul ψ.continuous
  exact (hc.div_const _).sub (continuous_const.mul (ψ.continuous.div_const _))

theorem residual_mass (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x) (x : X) :
    (∫ y, residual μ K ψ lam m M x y ∂μ) = 1 - m / M := by
  have hc : Continuous (fun y => K (x, y) * ψ y) :=
      (K.continuous.comp (continuous_const.prodMk continuous_id)).mul ψ.continuous
  have hi : Integrable (doob K ψ lam x) μ :=
    (hc.div_const _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun y => (m / M) * (ψ y / (∫ z, ψ z ∂μ))) μ :=
    (continuous_const.mul (ψ.continuous.div_const _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold residual
  rw [integral_sub hi hj, doob_mass μ K ψ hψ lam hlam heig x,
    integral_const_mul, integral_div, div_self (profile_integral_pos μ ψ hψ).ne', mul_one]

variable [Nonempty X]

/-- A nonconstant continuous eigenfunction of a minorized transition has a strict ratio bound. -/
theorem doob_eigen_ratio (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (F : C(X, ℝ)) (r : ℝ) (hF : ∃ x y, F x ≠ F y)
    (hFeig : ∀ x, (∫ y, doob K ψ lam x y * F y ∂μ) = r * F x) :
    |r| ≤ 1 - m / M := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) F.continuous.continuousOn
  obtain ⟨b, _, hb⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) F.continuous.continuousOn
  have hmax (y : X) : F y ≤ F a := ha (mem_univ y)
  have hmin (y : X) : F b ≤ F y := hb (mem_univ y)
  have hdiff : 0 < F a - F b := by
    have hab : F b ≤ F a := hmax b
    by_contra! hn
    have hab' : F a = F b := by linarith
    obtain ⟨x, y, hxy⟩ := hF
    apply hxy
    have hx := hmin x
    have hx' := hmax x
    have hy := hmin y
    have hy' := hmax y
    linarith
  let c := ∫ y, (m / M) * (ψ y / (∫ z, ψ z ∂μ)) * F y ∂μ
  have split (x : X) : (∫ y, residual μ K ψ lam m M x y * F y ∂μ) = r * F x - c := by
    have hi : Integrable (fun y => doob K ψ lam x y * F y) μ := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      unfold doob
      fun_prop
    have hj : Integrable (fun y => (m / M) * (ψ y / (∫ z, ψ z ∂μ)) * F y) μ := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
    simp_rw [residual, sub_mul]
    rw [integral_sub hi hj, hFeig x]
  have bounds (x : X) :
      (1 - m / M) * F b ≤ r * F x - c ∧ r * F x - c ≤ (1 - m / M) * F a := by
    have hi := (residual_continuous μ K ψ lam m M x).integrable_of_hasCompactSupport
      (μ := μ) (HasCompactSupport.of_compactSpace _)
    have hcf := (residual_continuous μ K ψ lam m M x).mul F.continuous
    have hif := hcf.integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace _)
    have hq (y : X) : 0 ≤ residual μ K ψ lam m M x y :=
      sub_nonneg.mpr (doob_minorant μ K ψ hψ lam m M hlam hm hM hlower hupper heig x y)
    constructor
    · have h := integral_mono (hi.mul_const (F b)) hif
        (fun y => mul_le_mul_of_nonneg_left (hmin y) (hq y))
      simp only [Pi.mul_apply] at h
      rw [integral_mul_const, residual_mass μ K ψ hψ lam m M hlam heig x, split x] at h
      exact h
    · have h := integral_mono hif (hi.mul_const (F a))
        (fun y => mul_le_mul_of_nonneg_left (hmax y) (hq y))
      simp only [Pi.mul_apply] at h
      rw [integral_mul_const, residual_mass μ K ψ hψ lam m M hlam heig x, split x] at h
      exact h
  have ha' := bounds a
  have hb' := bounds b
  apply abs_le.mpr
  constructor <;> nlinarith


/-- Dividing an actual kernel eigenfunction by the positive ground profile. -/
def quotient (ψ f : C(X, ℝ)) (hψ : ∀ x, 0 < ψ x) : C(X, ℝ) :=
  ⟨fun x => f x / ψ x, f.continuous.div ψ.continuous (fun x => (hψ x).ne')⟩

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [Nonempty X] in
/-- The actual integral eigen-equation becomes the Doob eigen-equation. -/
theorem quotient_eigen (K : C(X × X, ℝ)) (ψ f : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam rho : ℝ) (hlam : 0 < lam)
    (hf : ∀ x, (∫ y, K (x, y) * f y ∂μ) = rho * f x) (x : X) :
    (∫ y, doob K ψ lam x y * quotient ψ f hψ y ∂μ) =
      (rho / lam) * quotient ψ f hψ x := by
  have he : (fun y => doob K ψ lam x y * quotient ψ f hψ y) =
      (fun y => (K (x, y) * f y) / (lam * ψ x)) := by
    funext y
    simp only [doob, quotient, ContinuousMap.coe_mk]
    field_simp [(hψ y).ne', (hψ x).ne', hlam.ne']
  rw [he, integral_div, hf]
  simp only [quotient, ContinuousMap.coe_mk]
  ring

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [Nonempty X] in
/-- A different eigenvalue cannot have a constant quotient unless its eigenfunction vanishes. -/
theorem quotient_nonconstant (K : C(X × X, ℝ)) (ψ f : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam rho : ℝ)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (hf : f ≠ 0) (hrho : rho ≠ lam)
    (hfeig : ∀ x, (∫ y, K (x, y) * f y ∂μ) = rho * f x) :
    ∃ x y, quotient ψ f hψ x ≠ quotient ψ f hψ y := by
  have hxexists : ∃ x, f x ≠ 0 := by
    by_contra! hh
    apply hf
    ext x
    exact hh x
  obtain ⟨x, hx⟩ := hxexists
  by_contra! hn
  let c := f x / ψ x
  have hc (y : X) : f y = c * ψ y := by
    have hy := hn y x
    change f y / ψ y = c at hy
    exact (div_eq_iff (hψ y).ne').mp hy
  have he : rho * f x = lam * f x := by
    rw [← hfeig x]
    calc
      _ = ∫ y, c * (K (x, y) * ψ y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [hc y]
        ring
      _ = c * (lam * ψ x) := by rw [integral_const_mul, heig]
      _ = _ := by rw [hc x]; ring
  exact hrho (mul_right_cancel₀ hx he)

/-- Every different nonzero real continuous eigenfunction obeys an explicit ratio bound. -/
theorem real_eigenvalue_ratio (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (f : C(X, ℝ)) (rho : ℝ) (hf : f ≠ 0) (hrho : rho ≠ lam)
    (hfeig : ∀ x, (∫ y, K (x, y) * f y ∂μ) = rho * f x) :
    |rho / lam| ≤ 1 - m / M :=
  doob_eigen_ratio μ K ψ hψ lam m M hlam hm hM hlower hupper heig
    (quotient ψ f hψ) (rho / lam)
    (quotient_nonconstant μ K ψ f hψ lam rho heig hf hrho hfeig)
    (quotient_eigen μ K ψ f hψ lam rho hlam hfeig)

/-- Complex eigenfunctions have real or imaginary components with the same real eigenvalue. -/
theorem complex_eigenvalue_ratio (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (f : C(X, ℂ)) (rho : ℝ) (hf : f ≠ 0) (hrho : rho ≠ lam)
    (hfeig : ∀ x, (∫ y, (K (x, y) : ℂ) * f y ∂μ) = (rho : ℂ) * f x) :
    |rho / lam| ≤ 1 - m / M := by
  let fre : C(X, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fim : C(X, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hi (x : X) : Integrable (fun y => (K (x, y) : ℂ) * f y) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  by_cases hre : fre = 0
  · have him : fim ≠ 0 := by
      intro hz
      apply hf
      ext x
      apply Complex.ext
      · have hx := congrArg (fun g : C(X, ℝ) => g x) hre
        exact hx
      · have hx := congrArg (fun g : C(X, ℝ) => g x) hz
        exact hx
    apply real_eigenvalue_ratio μ K ψ hψ lam m M hlam hm hM hlower hupper heig
      fim rho him hrho
    intro x
    have h := congrArg Complex.im (hfeig x)
    change RCLike.im (∫ y, (K (x, y) : ℂ) * f y ∂μ) =
      RCLike.im ((rho : ℂ) * f x) at h
    rw [← integral_im (hi x)] at h
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, fim, ContinuousMap.coe_mk] using h
  · apply real_eigenvalue_ratio μ K ψ hψ lam m M hlam hm hM hlower hupper heig
      fre rho hre hrho
    intro x
    have h := congrArg Complex.re (hfeig x)
    change RCLike.re (∫ y, (K (x, y) : ℂ) * f y ∂μ) =
      RCLike.re ((rho : ℂ) * f x) at h
    rw [← integral_re (hi x)] at h
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, fre, ContinuousMap.coe_mk] using h


/-- The same minorization forces every real top eigenfunction to be proportional to the ground. -/
theorem real_top_proportional (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (f : C(X, ℝ)) (hfeig : ∀ x, (∫ y, K (x, y) * f y ∂μ) = lam * f x) :
    ∃ c : ℝ, ∀ x, f x = c * ψ x := by
  have hc : ∀ x y, quotient ψ f hψ x = quotient ψ f hψ y := by
    by_contra! hn
    have h := doob_eigen_ratio μ K ψ hψ lam m M hlam hm hM hlower hupper heig
      (quotient ψ f hψ) (lam / lam) hn (quotient_eigen μ K ψ f hψ lam lam hlam hfeig)
    rw [div_self hlam.ne', abs_one] at h
    have hp : 0 < m / M := div_pos hm hM
    linarith
  let x₀ := Classical.arbitrary X
  refine ⟨quotient ψ f hψ x₀, ?_⟩
  intro x
  have hx := hc x x₀
  change f x / ψ x = _ at hx
  exact (div_eq_iff (hψ x).ne').mp hx

/-- Simplicity on all continuous complex eigenfunctions, derived rather than assumed. -/
theorem complex_top_proportional (K : C(X × X, ℝ)) (ψ : C(X, ℝ))
    (hψ : ∀ x, 0 < ψ x) (lam m M : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ K (x, y)) (hupper : ∀ x y, K (x, y) ≤ M)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (f : C(X, ℂ))
    (hfeig : ∀ x, (∫ y, (K (x, y) : ℂ) * f y ∂μ) = (lam : ℂ) * f x) :
    ∃ c : ℂ, ∀ x, f x = c * (ψ x : ℂ) := by
  let fre : C(X, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fim : C(X, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hi (x : X) : Integrable (fun y => (K (x, y) : ℂ) * f y) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hre (x : X) : (∫ y, K (x, y) * fre y ∂μ) = lam * fre x := by
    have h := congrArg Complex.re (hfeig x)
    change RCLike.re (∫ y, (K (x, y) : ℂ) * f y ∂μ) =
      RCLike.re ((lam : ℂ) * f x) at h
    rw [← integral_re (hi x)] at h
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, fre, ContinuousMap.coe_mk] using h
  have him (x : X) : (∫ y, K (x, y) * fim y ∂μ) = lam * fim x := by
    have h := congrArg Complex.im (hfeig x)
    change RCLike.im (∫ y, (K (x, y) : ℂ) * f y ∂μ) =
      RCLike.im ((lam : ℂ) * f x) at h
    rw [← integral_im (hi x)] at h
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, fim, ContinuousMap.coe_mk] using h
  obtain ⟨a, ha⟩ := real_top_proportional μ K ψ hψ lam m M hlam hm hM hlower hupper heig fre hre
  obtain ⟨b, hb⟩ := real_top_proportional μ K ψ hψ lam m M hlam hm hM hlower hupper heig fim him
  refine ⟨⟨a, b⟩, ?_⟩
  intro x
  apply Complex.ext
  · simpa only [fre, ContinuousMap.coe_mk, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using ha x
  · simpa only [fim, ContinuousMap.coe_mk, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] using hb x

end
end UnifiedTheory.Clay.YangMills.PositiveKernelRatio
