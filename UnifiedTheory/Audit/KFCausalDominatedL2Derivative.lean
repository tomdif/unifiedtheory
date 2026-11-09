/- Pointwise derivatives with a proved local L2 majorant for the slopes
give actual strong L2 derivatives. This supplies domain membership, rather
than assuming a strong derivative and identifying its representative. -/
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalDominatedL2Derivative
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem hasDerivAt_toLp (F : ℝ → X → ℂ) (hF : ∀ t, MemLp (F t) 2 μ)
    (g : X → ℂ) (hg : MemLp g 2 μ) (b : X → ℝ)
    (hb2 : Integrable (fun x => b x^2) μ)
    (hb : ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ᵐ x ∂μ, ‖t⁻¹ • (F t x-F 0 x)‖ ≤ b x)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (g x) 0) :
    HasDerivAt (fun t => (hF t).toLp (F t)) (hg.toLp g) 0 := by
  let q : ℝ → X → ℂ := fun t => t⁻¹ • (F t-F 0)
  have hq (t : ℝ) : MemLp (q t) 2 μ := ((hF t).sub (hF 0)).const_smul t⁻¹
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Tendsto (fun t => ∫ x, ‖q t x-g x‖^2 ∂μ) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := 𝓝[≠] (0:ℝ)) (F := fun t x => ‖q t x-g x‖^2)
      (f := fun _ => (0:ℝ)) (bound := fun x => 2*b x^2+2*‖g x‖^2)
      (Eventually.of_forall (fun t => ((hq t).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2))
      (hb.mono (fun t ht => ht.mono (fun x hx => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have h0 : 0 ≤ b x := (norm_nonneg _).trans hx
        have h1 : ‖q t x-g x‖ ≤ b x+‖g x‖ := (norm_sub_le _ _).trans (add_le_add hx le_rfl)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg (b x-‖g x‖)])))
      ((hb2.const_mul 2).add (hg2.const_mul 2))
      (hd.mono (fun x hx => by
        have hs : Tendsto (fun t => q t x) (𝓝[≠] (0:ℝ)) (𝓝 (g x)) := by
          simpa only [q,Pi.smul_apply,Pi.sub_apply,zero_add] using hx.tendsto_slope_zero
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
          (hs.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => g x) (𝓝[≠] (0:ℝ)) (𝓝 (g x)))).norm.pow 2))
    simpa only [integral_zero] using hh
  have he (t : ℝ) : ‖(hq t).toLp (q t)-hg.toLp g‖^2 = ∫ x, ‖q t x-g x‖^2 ∂μ := by
    rw [← MemLp.toLp_sub,toLp_square_integral]
    rfl
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  have hn : Tendsto (fun t => ‖(hq t).toLp (q t)-hg.toLp g‖) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,← he,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs
  have hl := tendsto_iff_norm_sub_tendsto_zero.mpr hn
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [q,MemLp.toLp_const_smul,MemLp.toLp_sub,zero_add] using hl

theorem hasDerivAt_represented (u : ℝ → Lp ℂ 2 μ) (F : ℝ → X → ℂ)
    (hr : ∀ t, u t =ᵐ[μ] F t) (g : X → ℂ) (hg : MemLp g 2 μ)
    (b : X → ℝ) (hb2 : Integrable (fun x => b x^2) μ)
    (hb : ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ᵐ x ∂μ, ‖t⁻¹ • (F t x-F 0 x)‖ ≤ b x)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (g x) 0) :
    HasDerivAt u (hg.toLp g) 0 := by
  have hF (t : ℝ) : MemLp (F t) 2 μ := (memLp_congr_ae (hr t)).mp (Lp.memLp (u t))
  have he : u = fun t => (hF t).toLp (F t) := by
    funext t
    exact Lp.ext ((hr t).trans (hF t).coeFn_toLp.symm)
  rw [he]
  exact hasDerivAt_toLp F hF g hg b hb2 hb hd

#print axioms hasDerivAt_toLp
#print axioms hasDerivAt_represented
end
end UnifiedTheory.Audit.KFCausalDominatedL2Derivative
