/- Bounded Yosida operators and strong resolvent approximation.
The estimates apply to a positive self-adjoint operator only after the
resolvent equations are supplied; the concrete application proves them. -/
import UnifiedTheory.Audit.KFCausalPositiveResolventBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalYosidaApproximation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def yosida (R : H →L[ℂ] H) (a : ℝ) : H →L[ℂ] H :=
  a • ContinuousLinearMap.id ℂ H - a • (a • R)

theorem yosida_apply (R : H →L[ℂ] H) (a : ℝ) (x : H) :
    yosida R a x = a • x - a • (a • R x) := rfl

theorem scaled_resolvent_contraction (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (x : H) :
    ‖a • R x‖ ≤ ‖x‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hb := resolvent_apply_norm_bound T R a ha hr hp x
  calc
    a*‖R x‖ ≤ a*(a⁻¹*‖x‖) := mul_le_mul_of_nonneg_left hb ha.le
    _ = ‖x‖ := by rw [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]

theorem yosida_selfAdjoint [CompleteSpace H] (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (ht : IsSelfAdjoint T) : IsSelfAdjoint (yosida R a) := by
  exact ((IsSelfAdjoint.all a).smul (IsSelfAdjoint.one (H →L[ℂ] H))).sub
    ((IsSelfAdjoint.all a).smul ((IsSelfAdjoint.all a).smul (resolvent_selfAdjoint T R a hr ht)))

theorem yosida_positive (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (x : H) :
    0 ≤ (inner ℂ (yosida R a x) x).re := by
  have hb : (inner ℂ (a • R x) x).re ≤ ‖x‖^2 := by
    calc
      _ ≤ ‖a • R x‖*‖x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖x‖*‖x‖ := mul_le_mul_of_nonneg_right
        (scaled_resolvent_contraction T R a ha hr hp x) (norm_nonneg _)
      _ = _ := (pow_two _).symm
  have he : (inner ℂ (yosida R a x) x).re = a*(‖x‖^2-(inner ℂ (a • R x) x).re) := by
    rw [yosida_apply,inner_sub_left,inner_smul_left_eq_smul,inner_smul_left_eq_smul,
      UnifiedTheory.Audit.KFCausalShiftedForm.complex_inner_square x]
    simp only [Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    ring
  rw [he]
  exact mul_nonneg ha.le (sub_nonneg.mpr hb)

theorem yosida_norm_bound (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) :
    ‖yosida R a‖ ≤ 2*a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [yosida_apply]
  calc
    ‖a • x - a • (a • R x)‖ ≤ ‖a • x‖ + ‖a • (a • R x)‖ := norm_sub_le _ _
    _ = a*‖x‖+a*‖a • R x‖ := by simp only [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    _ ≤ a*‖x‖+a*‖x‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (scaled_resolvent_contraction T R a ha hr hp x) ha.le)
    _ = (2*a)*‖x‖ := by ring

theorem yosida_on_domain (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (x : T.domain) :
    yosida R a (x:H) = a • R (T x) := by
  have hh : R (T x)+a • R (x:H) = (x:H) := by
    simpa only [map_add,ContinuousLinearMap.map_smul_of_tower] using hl x
  rw [yosida_apply,← smul_sub]
  congr 1
  exact sub_eq_iff_eq_add.mpr hh.symm

theorem dense_approximation_error (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re)
    (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (f : H) (x : T.domain) :
    ‖a • R f-f‖ ≤ 2*‖f-(x:H)‖+a⁻¹*‖T x‖ := by
  have he : a • R f-f = a • R (f-(x:H))+(a • R (x:H)-(x:H))+((x:H)-f) := by
    rw [map_sub,smul_sub]
    abel
  rw [he]
  calc
    _ ≤ (‖a • R (f-(x:H))‖+‖a • R (x:H)-(x:H)‖)+‖(x:H)-f‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖f-(x:H)‖+a⁻¹*‖T x‖)+‖(x:H)-f‖ := add_le_add
      (add_le_add (scaled_resolvent_contraction T R a ha hr hp _)
        (approximation_error T R a ha hr hp hl x)) le_rfl
    _ = _ := by rw [norm_sub_rev (x:H) f]; ring

theorem scaled_resolvent_strong_limit (T : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (T.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves T (R a) a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re)
    (hl : ∀ a, 0 < a → ∀ x : T.domain, R a (T x+a • (x:H)) = x) (f : H) :
    Tendsto (fun a : ℝ => a • R a f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨x,hx,hfx⟩ := hd.exists_dist_lt f (show 0 < δ/4 by positivity)
  let y : T.domain := ⟨x,hx⟩
  refine ⟨max 1 (4*‖T y‖/δ),?_⟩
  intro a ha
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ham : 4*‖T y‖/δ ≤ a := (le_max_right _ _).trans ha
  have hb : a⁻¹*‖T y‖ ≤ δ/4 := by
    apply (inv_mul_le_iff₀ hap).mpr
    have hm := (div_le_iff₀ hδ).mp ham
    nlinarith
  have he := dense_approximation_error T (R a) a hap (hr a hap) hp (hl a hap) f y
  rw [dist_eq_norm] at hfx ⊢
  change ‖f-(y:H)‖ < δ/4 at hfx
  linarith

theorem yosida_strong_limit_on_domain (T : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (T.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves T (R a) a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re)
    (hl : ∀ a, 0 < a → ∀ x : T.domain, R a (T x+a • (x:H)) = x) (x : T.domain) :
    Tendsto (fun a : ℝ => yosida (R a) a (x:H)) atTop (𝓝 (T x)) := by
  apply (scaled_resolvent_strong_limit T R hd hr hp hl (T x)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  exact (yosida_on_domain T (R a) a (hl a ha) x).symm

#print axioms scaled_resolvent_contraction
#print axioms yosida_selfAdjoint
#print axioms yosida_positive
#print axioms yosida_norm_bound
#print axioms yosida_on_domain
#print axioms dense_approximation_error
#print axioms scaled_resolvent_strong_limit
#print axioms yosida_strong_limit_on_domain

end
end UnifiedTheory.Audit.KFCausalYosidaApproximation
