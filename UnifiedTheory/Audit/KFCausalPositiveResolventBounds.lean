/- Estimates for a bounded resolvent satisfying the actual equation for
a positive self-adjoint partial operator. The application constructs that
resolvent and discharges every equation hypothesis. -/
import UnifiedTheory.Audit.KFCausalShiftedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveResolventBounds
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Resolves (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) : Prop :=
  ∀ f, ∃ hx : R f ∈ T.domain, T ⟨R f,hx⟩ = f-a • R f

def point (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (hr : Resolves T R a) (f : H) : T.domain :=
  ⟨R f,(hr f).choose⟩

theorem point_value (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (hr : Resolves T R a) (f : H) :
    T (point T R a hr f) = f-a • R f := (hr f).choose_spec

theorem resolvent_inner_symm [CompleteSpace H] (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (ht : IsSelfAdjoint T) (f g : H) :
    inner ℂ (R f) g = inner ℂ f (R g) := by
  have hs := LinearPMap.adjoint_isFormalAdjoint ht.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp ht] at hs
  have hp := hs (point T R a hr f) (point T R a hr g)
  change inner ℂ (T (point T R a hr f)) (R g) = inner ℂ (R f) (T (point T R a hr g)) at hp
  rw [point_value,point_value,inner_sub_left,inner_sub_right,
    inner_smul_left_eq_smul,inner_smul_right_eq_smul] at hp
  exact (sub_left_inj.mp hp).symm

theorem resolvent_selfAdjoint [CompleteSpace H] (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (ht : IsSelfAdjoint T) : IsSelfAdjoint R :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (resolvent_inner_symm T R a hr ht)

theorem resolvent_inner_lower (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    a*‖R f‖^2 ≤ (inner ℂ f (R f)).re := by
  have hh := hp (point T R a hr f)
  change 0 ≤ (inner ℂ (T (point T R a hr f)) (R f)).re at hh
  rw [point_value,inner_sub_left,inner_smul_left_eq_smul,
    UnifiedTheory.Audit.KFCausalShiftedForm.complex_inner_square (R f)] at hh
  simp only [Complex.sub_re, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re] at hh
  linarith

theorem resolvent_positive [CompleteSpace H] (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (ht : IsSelfAdjoint T)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    0 ≤ (inner ℂ (R f) f).re := by
  rw [resolvent_inner_symm T R a hr ht f f]
  exact (mul_nonneg ha.le (sq_nonneg _)).trans (resolvent_inner_lower T R a hr hp f)

theorem resolvent_apply_norm_bound (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    ‖R f‖ ≤ a⁻¹*‖f‖ := by
  by_cases hz : R f = 0
  · rw [hz,norm_zero]
    positivity
  have hn : 0 < ‖R f‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hb := resolvent_inner_lower T R a hr hp f
  have hi : (inner ℂ f (R f)).re ≤ ‖f‖*‖R f‖ := re_inner_le_norm (𝕜 := ℂ) f (R f)
  nlinarith

theorem resolvent_norm_bound (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) :
    ‖R‖ ≤ a⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr ha).le
    (resolvent_apply_norm_bound T R a ha hr hp)

theorem resolvent_injective (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) : Function.Injective R := by
  intro f g hfg
  have he : point T R a hr f = point T R a hr g := Subtype.ext hfg
  have hv := congrArg T he
  rw [point_value,point_value,hfg] at hv
  exact sub_left_inj.mp hv

theorem resolvent_dense [CompleteSpace H] (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves T R a) (ht : IsSelfAdjoint T) : DenseRange R := by
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [(resolvent_selfAdjoint T R a hr ht).isSymmetric.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr (resolvent_injective T R a hr)

theorem approximation_error (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves T R a) (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re)
    (hl : ∀ x : T.domain, R (T x+a • (x:H)) = x) (x : T.domain) :
    ‖a • R (x:H) - (x:H)‖ ≤ a⁻¹*‖T x‖ := by
  have hh : R (T x)+a • R (x:H) = (x:H) := by simpa only [map_add,ContinuousLinearMap.map_smul_of_tower] using hl x
  have hq : a • R (x:H) = (x:H)-R (T x) :=
    eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)
  rw [hq]
  have he : (x:H)-R (T x)-(x:H) = -R (T x) := by abel
  rw [he,norm_neg]
  exact resolvent_apply_norm_bound T R a ha hr hp (T x)

#print axioms resolvent_selfAdjoint
#print axioms resolvent_inner_lower
#print axioms resolvent_positive
#print axioms resolvent_norm_bound
#print axioms resolvent_injective
#print axioms resolvent_dense
#print axioms approximation_error

end
end UnifiedTheory.Audit.KFCausalPositiveResolventBounds
