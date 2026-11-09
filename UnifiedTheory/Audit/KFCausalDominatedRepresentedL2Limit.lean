/- Dominated pointwise convergence of proved representatives gives an
actual L2 vector limit along any countably generated filter. -/
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
  {l : Filter ι} [l.IsCountablyGenerated]

theorem represented_tendsto (u : ι → Lp ℂ 2 μ) (F : ι → X → ℂ)
    (g : X → ℂ) (hg : MemLp g 2 μ) (D : X → ℝ) (hD : MemLp D 2 μ)
    (hu : ∀ᶠ i in l, u i =ᵐ[μ] F i)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ ‖D x‖)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (g x))) :
    Tendsto u l (𝓝 (hg.toLp g)) := by
  have hD2 := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Tendsto (fun i => ∫ x, ‖F i x-g x‖^2 ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (F := fun i x => ‖F i x-g x‖^2) (f := fun _ => (0:ℝ))
      (bound := fun x => 2*‖D x‖^2+2*‖g x‖^2)
      (hu.mono (fun i hi => (((Lp.memLp (u i)).ae_eq hi).aestronglyMeasurable.sub
        hg.aestronglyMeasurable).norm.pow 2))
      (hb.mono (fun i hi => hi.mono (fun x hx => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hd : ‖F i x-g x‖ ≤ ‖D x‖+‖g x‖ := (norm_sub_le _ _).trans (add_le_add hx le_rfl)
        have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
        nlinarith [sq_nonneg (‖D x‖-‖g x‖)])))
      ((hD2.const_mul 2).add (hg2.const_mul 2))
      (hl.mono (fun x hx => by
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using (hx.sub_const (g x)).norm.pow 2))
    simpa only [integral_zero] using hh
  have he : ∀ᶠ i in l, ‖u i-hg.toLp g‖^2 = ∫ x, ‖F i x-g x‖^2 ∂μ := by
    filter_upwards [hu] with i hi
    rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u i) (hg.toLp g),hi,hg.coeFn_toLp] with x hx hF hgx
    simp only [hx,Pi.sub_apply,hF,hgx]
  have hs : Tendsto (fun i => ‖u i-hg.toLp g‖^2) l (𝓝 0) := Tendsto.congr' (he.mono (fun i hi => hi.symm)) hi
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hn

#print axioms represented_tendsto
end
end UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit
