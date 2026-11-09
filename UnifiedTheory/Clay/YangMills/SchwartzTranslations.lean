/- Strong continuity of translations in every Schwartz derivative seminorm,
for an arbitrary real normed domain. This is used at every correlation order. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzTranslations
noncomputable section
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def translationCLM (a : E) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (Function.HasTemperateGrowth.id.sub (Function.HasTemperateGrowth.const a))
    (IsometryEquiv.subRight a).isometry.antilipschitz

@[simp] theorem translationCLM_apply (a : E) (f : SchwartzMap E ℂ) (x : E) :
    translationCLM a f x = f (x - a) := rfl

/-- A finite higher-derivative seminorm controlling small translations. -/
def derivativeBound (f : SchwartzMap E ℂ) (k n : ℕ) : ℝ :=
  2 ^ k * (Finset.Iic (k, n + 1)).sup (fun i => SchwartzMap.seminorm ℂ i.1 i.2) f

theorem derivativeBound_nonneg (f : SchwartzMap E ℂ) (k n : ℕ) : 0 ≤ derivativeBound f k n := by
  unfold derivativeBound
  positivity

theorem weighted_fderiv_bound (f : SchwartzMap E ℂ) (k n : ℕ) (x y : E)
    (hy : y ∈ Metric.closedBall x 1) :
    ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y‖ ≤ derivativeBound f k n := by
  have hxy : ‖x‖ ≤ 1 + ‖y‖ := by
    have hd : ‖x - y‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy
    calc
      ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
      _ ≤ 1 + ‖y‖ := by gcongr
  rw [norm_fderiv_iteratedFDeriv]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖ ≤
        (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖ := by gcongr
    _ ≤ derivativeBound f k n :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, n + 1)) le_rfl le_rfl f y

/-- Uniform, weighted mean-value estimate for each derivative order. -/
theorem weighted_derivative_translation_difference (f : SchwartzMap E ℂ) (k n : ℕ)
    (a x : E) (ha : ‖a‖ ≤ 1) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - a) - iteratedFDeriv ℝ n f x‖ ≤
      derivativeBound f k n * ‖a‖ := by
  let F := fun y : E => ‖x‖ ^ k • iteratedFDeriv ℝ n f y
  have hf : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    (f.smooth (n + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have hF : Differentiable ℝ F := hf.const_smul (‖x‖ ^ k)
  have hbound : ∀ y ∈ Metric.closedBall x 1, ‖fderiv ℝ F y‖ ≤ derivativeBound f k n := by
    intro y hy
    change ‖fderiv ℝ ((‖x‖ ^ k) • iteratedFDeriv ℝ n f) y‖ ≤ derivativeBound f k n
    rw [fderiv_const_smul (hf y) (‖x‖ ^ k), norm_smul,
      Real.norm_of_nonneg (by positivity)]
    exact weighted_fderiv_bound f k n x y hy
  have hx : x ∈ Metric.closedBall x 1 := Metric.mem_closedBall_self (by norm_num)
  have hxa : x - a ∈ Metric.closedBall x 1 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using ha
  have hm := (convex_closedBall x (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hF y) hbound hx hxa
  simpa only [F, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ k),
    sub_sub_cancel_left, norm_neg] using hm

theorem iteratedFDeriv_translation (f : SchwartzMap E ℂ) (a x : E) (n : ℕ) :
    iteratedFDeriv ℝ n (translationCLM a f) x = iteratedFDeriv ℝ n f (x - a) := by
  have hcoe : (translationCLM a f : E → ℂ) = fun z => f (z - a) := by
    funext z
    rfl
  rw [hcoe, iteratedFDeriv_comp_sub]

theorem iteratedFDeriv_schwartz_sub (f h : SchwartzMap E ℂ) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (f - h) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n h x := by
  rw [sub_eq_add_neg]
  change iteratedFDeriv ℝ n ((f : E → ℂ) + -(h : E → ℂ)) x = _
  have hh : ContDiffAt ℝ n (-(h : E → ℂ)) x := (h.smooth n).contDiffAt.neg
  rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt hh,
    iteratedFDeriv_neg_apply]
  rfl

/-- Every Schwartz seminorm of the translation difference is O(norm(a)). -/
theorem seminorm_translation_difference (f : SchwartzMap E ℂ) (k n : ℕ)
    (a : E) (ha : ‖a‖ ≤ 1) :
    SchwartzMap.seminorm ℂ k n (translationCLM a f - f) ≤
      derivativeBound f k n * ‖a‖ := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _
    (mul_nonneg (derivativeBound_nonneg f k n) (norm_nonneg a))
  intro x
  rw [iteratedFDeriv_schwartz_sub, iteratedFDeriv_translation]
  exact weighted_derivative_translation_difference f k n a x ha

theorem tendsto_translation_zero (f : SchwartzMap E ℂ) :
    Filter.Tendsto (fun a : E => translationCLM a f) (𝓝 0) (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ f).mpr
  rintro ⟨k, n⟩ ε hε
  have hsmall : ∀ᶠ a : E in 𝓝 0, ‖a‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : E)
      (by norm_num : (0 : ℝ) < 1)] with a ha
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  have hlimit : Filter.Tendsto (fun a : E => derivativeBound f k n * ‖a‖)
      (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const.mul continuous_norm).tendsto (0 : E)
  have hεsmall : ∀ᶠ a : E in 𝓝 0, derivativeBound f k n * ‖a‖ < ε :=
    hlimit.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, hεsmall] with a ha hεa
  exact (seminorm_translation_difference f k n a ha).trans_lt hεa

/-- Genuine strong continuity in the full Schwartz topology of spacetime
translations. This theorem has no continuity or physical-representation premise. -/
theorem continuous_translation_tests (f : SchwartzMap E ℂ) :
    Continuous (fun a : E => translationCLM a f) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hab : Filter.Tendsto (fun a : E => a - b) (𝓝 b) (𝓝 0) := by
    have hc : Continuous (fun a : E => a - b) := continuous_id.sub continuous_const
    simpa using hc.tendsto b
  have ht := (tendsto_translation_zero (translationCLM b f)).comp hab
  have he : ∀ a : E, translationCLM (a - b) (translationCLM b f) = translationCLM a f := by
    intro a
    ext x
    simp only [translationCLM_apply]
    congr 1
    abel
  simpa only [Function.comp_def, he] using ht

end
end UnifiedTheory.Clay.YangMills.SchwartzTranslations
