/- Polynomial growth and exponential damping of actual Schwartz translations.
These estimates use the Schwartz topology itself, with no uniform bare-field
bound and no hypothesis on a translated orbit. -/
import UnifiedTheory.Clay.YangMills.SchwartzTranslations
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzTranslationGrowth
noncomputable section
open Filter SchwartzTranslations
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def growthConstant (f : SchwartzMap E ℂ) (k n : ℕ) : ℝ :=
  2 ^ k * (Finset.Iic (k, n)).sup (fun i => SchwartzMap.seminorm ℂ i.1 i.2) f

theorem growthConstant_nonneg (f : SchwartzMap E ℂ) (k n : ℕ) :
    0 ≤ growthConstant f k n := by
  unfold growthConstant
  positivity

/-- A global estimate, without the small-displacement restriction. -/
theorem seminorm_translation_bound (f : SchwartzMap E ℂ) (k n : ℕ) (a : E) :
    SchwartzMap.seminorm ℂ k n (translationCLM a f) ≤
      (1 + ‖a‖)^k * growthConstant f k n := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _
    (mul_nonneg (by positivity) (growthConstant_nonneg f k n))
  intro x
  rw [iteratedFDeriv_translation]
  have hx : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x-a‖) := by
    have hh := norm_le_norm_sub_add x a
    nlinarith [norm_nonneg a, norm_nonneg (x-a), mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  calc
    ‖x‖^k * ‖iteratedFDeriv ℝ n f (x-a)‖ ≤
        ((1+‖a‖)*(1+‖x-a‖))^k * ‖iteratedFDeriv ℝ n f (x-a)‖ := by gcongr
    _ = (1+‖a‖)^k * ((1+‖x-a‖)^k * ‖iteratedFDeriv ℝ n f (x-a)‖) := by
      rw [mul_pow, mul_assoc]
    _ ≤ (1+‖a‖)^k * growthConstant f k n := by
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.one_add_le_sup_seminorm_apply (m := (k,n)) le_rfl le_rfl f (x-a))
        (by positivity)

theorem seminorm_ray_bound (f : SchwartzMap E ℂ) (k n : ℕ) (v : E)
    (t : ℝ) (ht : 1 ≤ t) :
    SchwartzMap.seminorm ℂ k n (translationCLM (t • v) f) ≤
      ((1+‖v‖)^k * growthConstant f k n) * t^k := by
  have ht0 : 0 ≤ t := by linarith
  have hn : ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht0]
  calc
    _ ≤ (1+‖t • v‖)^k * growthConstant f k n := seminorm_translation_bound f k n _
    _ ≤ ((1+‖v‖)*t)^k * growthConstant f k n := by
      rw [hn]
      apply mul_le_mul_of_nonneg_right _ (growthConstant_nonneg f k n)
      gcongr
      nlinarith
    _ = _ := by rw [mul_pow]; ring

/-- Every exponentially damped translation ray converges to zero in all
Schwartz derivative seminorms, including arbitrarily high weights. -/
theorem damped_translation_tendsto_zero (f : SchwartzMap E ℂ) (v : E)
    (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun t : ℝ => (Real.exp (-eps*t) : ℂ) • translationCLM (t • v) f)
      atTop (𝓝 0) := by
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ 0).mpr
  rintro ⟨k,n⟩ δ hδ
  let C : ℝ := (1+‖v‖)^k * growthConstant f k n
  have hlim : Tendsto (fun t : ℝ => C * (t^k * Real.exp (-eps*t))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) eps heps).const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually (gt_mem_nhds hδ)] with t ht hδt
  simp only [sub_zero, map_smul_eq_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply lt_of_le_of_lt _ hδt
  calc
    Real.exp (-eps*t) * SchwartzMap.seminorm ℂ k n (translationCLM (t • v) f) ≤
        Real.exp (-eps*t) * (C * t^k) :=
      mul_le_mul_of_nonneg_left (seminorm_ray_bound f k n v t ht) (Real.exp_pos _).le
    _ = C * (t^k * Real.exp (-eps*t)) := by ring

theorem damped_nnreal_translation_tendsto_zero (f : SchwartzMap E ℂ) (v : E)
    (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun t : ℝ≥0 => (Real.exp (-eps*(t:ℝ)) : ℂ) •
      translationCLM ((t:ℝ) • v) f) atTop (𝓝 0) :=
  (damped_translation_tendsto_zero f v eps heps).comp
    (NNReal.tendsto_coe_atTop.mpr tendsto_id)

/-- A tempered distribution cannot grow exponentially on a translation ray. -/
theorem damped_distribution_tendsto_zero (F : SchwartzMap E ℂ →L[ℂ] ℂ)
    (f : SchwartzMap E ℂ) (v : E) (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun t : ℝ≥0 => (Real.exp (-eps*(t:ℝ)) : ℂ) *
      F (translationCLM ((t:ℝ) • v) f)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, map_smul, smul_eq_mul, map_zero] using
    F.continuous.continuousAt.tendsto.comp
      (damped_nnreal_translation_tendsto_zero f v eps heps)

end
end UnifiedTheory.Clay.YangMills.SchwartzTranslationGrowth
