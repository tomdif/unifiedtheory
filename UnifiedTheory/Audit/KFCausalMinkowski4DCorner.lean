/-
  Audit/KFCausalMinkowski4DCorner.lean   (Volume sector → K4-corner, stage A)

  Rung 4d of the 4D ladder: the analytic heart of the K4-corner — Frullani for all
  scales and the FRULLANI CONCENTRATION LIMIT.

  In boost coordinates the K4-corner mass sits log-uniformly on the hyperbola
  `uv ~ 1/√a`; the per-`w` content of its limit is the statement proved here
  (`frullani_concentration`): for jointly continuous `g` with bounded `∂_u g` and
  `u`-support in `[0,A]`, and any `w > 0`,

      ∫₀^∞ (g(w·s, (√a·s)⁻¹) − g(s, (√a·s)⁻¹)) / s ds
          ⟶  −g(0,0)·ln w        (a → ∞),

  by dominated convergence (dominator `M_u·|w−1|·1_{(0,max(A,A/w)]}`, mean value in
  the FIRST argument — fixed, no moving support) down to the exact Frullani value.

  Supporting, both of independent use:
   • `haar_scale` — the multiplicative Haar invariance `∫₀^∞ h(w·s)/s ds = ∫₀^∞ h(u)/u du`
     (exact, unconditional — `du/u` is scale invariant).
   • `frullani_pos` — Frullani for ALL `b > 0` (the `b < 1` case by Haar reflection
     from the proven `b ≥ 1` case; `ln` antisymmetry).

  REMAINING for the full K4-corner after this stage: the inner `w = √a·u·v`
  substitution identity (mechanical, the `J4_slice_identity` pattern), the product
  Fubini, the outer DCT with the `|K4(w²)|(C + |ln w|)` dominator, and the constant
  evaluation `C_K = −∫K4(s²)ln s ds = √π/3` (a `Γ'(½)`-chain, numerically locked).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowskiFrullani

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowskiFrullani

namespace UnifiedTheory.Audit.KFCausalMinkowski4DCorner

/-! ## Multiplicative Haar invariance -/

/-- **Scale invariance of `du/u`**: `∫₀^∞ h(w·s)/s ds = ∫₀^∞ h(u)/u du` for `w > 0`.
Exact and unconditional (`integral_comp_mul_left_Ioi`). -/
theorem haar_scale (h : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    ∫ s in Ioi (0:ℝ), h (w*s) / s = ∫ u in Ioi (0:ℝ), h u / u := by
  have hcomp := integral_comp_mul_left_Ioi (fun u => h u / u) 0 hw
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcancel : (∫ s in Ioi (0:ℝ), (fun u => h u / u) (w*s))
      = ∫ s in Ioi (0:ℝ), w⁻¹ * (h (w*s) / s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    rw [mem_Ioi] at hs
    show h (w*s) / (w*s) = w⁻¹ * (h (w*s)/s)
    field_simp
    try ring
  rw [hcancel, integral_const_mul] at hcomp
  exact mul_left_cancel₀ (inv_ne_zero hw.ne') hcomp

/-! ## Frullani for all scales -/

/-- **Frullani's integral for every `b > 0`**: with `f ∈ C¹`, `|f'| ≤ M`, vanishing
past `R`,  `∫₀^∞ (f(bu) − f(u))/u du = −f(0)·ln b`.  The `b < 1` case follows from
the `b ≥ 1` case (`frullani`) by Haar reflection. -/
theorem frullani_pos (f f' : ℝ → ℝ) (M R : ℝ) (hR : 0 < R)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hM : ∀ x, |f' x| ≤ M)
    (hsupp : ∀ x, R ≤ x → f x = 0)
    (b : ℝ) (hb : 0 < b) :
    ∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u = -(f 0) * Real.log b := by
  rcases le_total 1 b with hb1 | hb1
  · exact frullani f f' M R hR hd hM hsupp b hb1
  · have hbinv : 1 ≤ b⁻¹ := by
      nlinarith [mul_inv_cancel₀ hb.ne', inv_pos.mpr hb]
    have hfr := frullani f f' M R hR hd hM hsupp b⁻¹ hbinv
    have hneg : (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)
        = -∫ u in Ioi (0:ℝ), (f u - f (b*u)) / u := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      ring
    have hhaar := haar_scale (fun u => f u - f (b*u)) b⁻¹ (inv_pos.mpr hb)
    have hpt : (∫ s in Ioi (0:ℝ), (fun u => f u - f (b*u)) (b⁻¹*s) / s)
        = ∫ s in Ioi (0:ℝ), (f (b⁻¹*s) - f s) / s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      show (f (b⁻¹*s) - f (b*(b⁻¹*s))) / s = (f (b⁻¹*s) - f s) / s
      rw [mul_inv_cancel_left₀ hb.ne']
    rw [hneg, ← hhaar, hpt, hfr, Real.log_inv]
    ring

/-! ## The Frullani concentration limit (the K4-corner's per-`w` heart) -/

/-- **The Frullani concentration limit.**  For jointly continuous `g` with bounded
`∂_u g` and `u`-support in `[0,A]`, and every `w > 0`,

    ∫₀^∞ (g(ws, (√a·s)⁻¹) − g(s, (√a·s)⁻¹))/s ds  →  −g(0,0)·ln w    (a → ∞):

the boost-hyperbola difference concentrates to the Frullani value.  Dominated
convergence with the FIXED dominator `M_u|w−1|·1_{(0,max(A,A/w)]}` (mean value in the
first argument), pointwise continuity in the second argument, and `frullani_pos` for
the limiting integral. -/
theorem frullani_concentration (g pdug : ℝ → ℝ → ℝ) (Mu A : ℝ) (hA : 0 < A)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hMu : ∀ u v, |pdug u v| ≤ Mu)
    (hsupp : ∀ u v, A ≤ u → g u v = 0)
    (w : ℝ) (hw : 0 < w) :
    Tendsto (fun a : ℝ => ∫ s in Ioi (0:ℝ),
        (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s)
      atTop (𝓝 (-(g 0 0) * Real.log w)) := by
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0 0)
  set A' := max A (A/w) with hA'def
  have hA' : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  -- mean-value bound in the first argument (uniform in the second)
  have hlipu : ∀ v x y : ℝ, |g x v - g y v| ≤ Mu * |x - y| := by
    intro v x y
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => g u v) (f' := fun u => pdug u v)
      (fun z _ => (hdu v z).hasDerivWithinAt)
      (fun z _ => by simpa [Real.norm_eq_abs] using hMu z v) (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs] using h
  -- DCT
  have hdct : Tendsto (fun a : ℝ => ∫ s in Ioi (0:ℝ),
      (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s)
      atTop (𝓝 (∫ s in Ioi (0:ℝ), (g (w*s) 0 - g s 0) / s)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun s => (Ioc (0:ℝ) A').indicator (fun _ => Mu * |w - 1|) s)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      have hy : Measurable (fun s : ℝ => (Real.sqrt a * s)⁻¹) :=
        (measurable_id.const_mul (Real.sqrt a)).inv
      have h1 : Measurable (fun s : ℝ => g (w*s) ((Real.sqrt a * s)⁻¹)) :=
        hgc.measurable.comp ((measurable_id.const_mul w).prodMk hy)
      have h2 : Measurable (fun s : ℝ => g s ((Real.sqrt a * s)⁻¹)) :=
        hgc.measurable.comp (measurable_id.prodMk hy)
      exact ((h1.sub h2).div measurable_id).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro s hs
      rw [mem_Ioi] at hs
      by_cases hsA : s ≤ A'
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs, hsA⟩), Real.norm_eq_abs, abs_div,
          div_le_iff₀ (abs_pos.mpr hs.ne')]
        calc |g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)|
            ≤ Mu * |w*s - s| := hlipu _ _ _
          _ = Mu * |w - 1| * |s| := by
              rw [show w*s - s = (w-1)*s from by ring, abs_mul]
              ring
      · push_neg at hsA
        have hz1 : g (w*s) ((Real.sqrt a * s)⁻¹) = 0 := by
          apply hsupp
          rw [hA'def] at hsA
          have := lt_of_le_of_lt (le_max_right A (A/w)) hsA
          rw [div_lt_iff₀ hw] at this
          nlinarith
        have hz2 : g s ((Real.sqrt a * s)⁻¹) = 0 := by
          apply hsupp
          rw [hA'def] at hsA
          exact (lt_of_le_of_lt (le_max_left A (A/w)) hsA).le
        rw [hz1, hz2, sub_zero, zero_div, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg hMu0 (abs_nonneg _)) s
    · rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (hs := ne_top_of_le_ne_top
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (Measure.restrict_apply_le _ _))
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro s hs
      rw [mem_Ioi] at hs
      have hyto : Tendsto (fun a : ℝ => (Real.sqrt a * s)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.atTop_mul_const hs)
      have hg1 : Continuous (fun v => g (w*s) v) :=
        hgc.comp (continuous_const.prodMk continuous_id)
      have hg2 : Continuous (fun v => g s v) :=
        hgc.comp (continuous_const.prodMk continuous_id)
      have h1 := (hg1.tendsto 0).comp hyto
      have h2 := (hg2.tendsto 0).comp hyto
      exact ((h1.sub h2).div_const s)
  -- the limiting integral is Frullani
  have hval : (∫ s in Ioi (0:ℝ), (g (w*s) 0 - g s 0) / s) = -(g 0 0) * Real.log w :=
    frullani_pos (fun u => g u 0) (fun u => pdug u 0) Mu A hA
      (fun x => hdu 0 x) (fun x => hMu x 0) (fun x hx => hsupp x 0 hx) w hw
  rwa [hval] at hdct

#print axioms haar_scale
#print axioms frullani_pos
#print axioms frullani_concentration

end UnifiedTheory.Audit.KFCausalMinkowski4DCorner
