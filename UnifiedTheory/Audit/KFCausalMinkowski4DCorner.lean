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

/-! ## The inner substitution (K4-corner step 1) -/

/-- **The inner `w = √a·u·v` substitution** (exact, per `a, u > 0`):

    √a · ∫₀^∞ K4(a u²v²) g(u,v) dv  =  u⁻¹ · ∫₀^∞ K4(w²) g(u, w/(√a·u)) dw.

The starting move of the K4-corner assembly: after it, the outer `u`-integral
against `u⁻¹` is the multiplicative-Haar structure that `frullani_concentration`
consumes. -/
theorem K4_corner_inner_sub (g : ℝ → ℝ → ℝ) (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    Real.sqrt a * ∫ v in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*v^2) * g u v
      = u⁻¹ * ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/(Real.sqrt a * u)) := by
  set c := Real.sqrt a * u with hcdef
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr ha) hu
  have hc2 : c^2 = a * u^2 := by rw [hcdef, mul_pow, Real.sq_sqrt ha.le]
  have hcomp := integral_comp_mul_left_Ioi
    (fun w => UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/c)) 0 hc
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcancel : (∫ x in Ioi (0:ℝ),
      (fun w => UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/c)) (c * x))
      = ∫ x in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*x^2) * g u x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    show UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 ((c*x)^2) * g u ((c*x)/c)
      = UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*x^2) * g u x
    rw [mul_div_cancel_left₀ x hc.ne', mul_pow, hc2]
    try ring_nf
  rw [hcancel] at hcomp
  dsimp only at hcomp
  rw [hcomp, hcdef]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  try ring

/-- **The Haar link (K4-corner step 2b).**  The inner profile of the K4-corner,
`G_a(w) = ∫₀^∞ u⁻¹ g(u, w/(√a·u)) du`, equals `∫₀^∞ s⁻¹ g(ws, (√a·s)⁻¹) ds` — the
`u = w·s` rescaling turns the second argument `w/(√a·u)` into `(√a·s)⁻¹`, so
`G_a(w) − G_a(1)` is EXACTLY the `frullani_concentration` integrand. -/
theorem K4_corner_haar_link (g : ℝ → ℝ → ℝ) (a w : ℝ) (hw : 0 < w) :
    ∫ u in Ioi (0:ℝ), g u (w/(Real.sqrt a * u)) / u
      = ∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s := by
  have h := haar_scale (fun u => g u (w/(Real.sqrt a * u))) w hw
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  rw [mem_Ioi] at hs
  show g (w*s) (w/(Real.sqrt a * (w*s))) / s = g (w*s) ((Real.sqrt a * s)⁻¹) / s
  congr 2
  field_simp
  try ring

/-! ## The Fubini swap (K4-corner step 2a) -/

/-- `t·e^{−t} ≤ 1` for `t ≥ 0`. -/
private lemma mul_exp_neg_le_one (t : ℝ) (ht : 0 ≤ t) : t * Real.exp (-t) ≤ 1 := by
  have h1 : t ≤ Real.exp t := (Real.add_one_le_exp t).trans' (by linarith)
  have h2 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-t), Real.exp_pos t]

/-- Global bound `|K4(z)| ≤ 7` for `z ≥ 0`. -/
theorem K4_abs_bound (z : ℝ) (hz : 0 ≤ z) :
    |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 z| ≤ 7 := by
  have h1 : z * Real.exp (-z) ≤ 1 := mul_exp_neg_le_one z hz
  have h2 : z^2 * Real.exp (-z) ≤ 4 := by
    have hh := mul_exp_neg_le_one (z/2) (by linarith)
    have hsq : (z/2 * Real.exp (-(z/2)))^2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ z/2) (Real.exp_pos (-(z/2))).le]
    have hexp : Real.exp (-(z/2)) * Real.exp (-(z/2)) = Real.exp (-z) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (-z)]
  have h3 : Real.exp (-z) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), abs_of_pos (Real.exp_pos _)]
  have habs : |1 + 4*z - 4*z^2| ≤ 1 + 4*z + 4*z^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  calc (1/3) * Real.exp (-z) * |1 + 4*z - 4*z^2|
      ≤ (1/3) * Real.exp (-z) * (1 + 4*z + 4*z^2) := by
        apply mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (1/3) * (Real.exp (-z) + 4*(z*Real.exp (-z)) + 4*(z^2*Real.exp (-z))) := by ring
    _ ≤ (1/3) * (1 + 4*1 + 4*4) := by
        apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
    _ = 7 := by norm_num

/-- `w ↦ K4(w²)` is integrable on `(0,∞)` (Gaussian moments `s = 0, 2, 4`). -/
theorem K4_sq_integrable :
    IntegrableOn (fun w => UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)) (Ioi (0:ℝ)) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (0:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (0:ℝ))).integrableOn
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (2:ℝ))).integrableOn
  have h4 : IntegrableOn (fun x : ℝ => x ^ (4:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (4:ℝ))).integrableOn
  refine IntegrableOn.congr_fun
    (((h0.const_mul (1/3)).add (h2.const_mul (4/3))).sub (h4.const_mul (4/3))) ?_
    measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [show w ^ (0:ℝ) = 1 from Real.rpow_zero w,
    show w ^ (2:ℝ) = w ^ (2:ℕ) from by rw [← Real.rpow_natCast w 2]; norm_num,
    show w ^ (4:ℝ) = w ^ (4:ℕ) from by rw [← Real.rpow_natCast w 4]; norm_num]
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
  simp only [neg_one_mul]
  ring

/-- **The Fubini swap (K4-corner step 2a).**  For bounded continuous `g` with
`u`-support `[0,A]` and `v`-support `[0,B]`, and `a > 0`:

    ∫₀^∞ u⁻¹ ∫₀^∞ K4(w²) g(u, w/(√a·u)) dw du
      = ∫₀^∞ K4(w²) · (∫₀^∞ g(u, w/(√a·u))/u du) dw.

Product integrability: per-`u` sections are bounded×integrable; the norm marginal is
bounded by the `√a`-uniform constant `7·Cg·B·√a` on the `u`-support box (the
`v`-support cuts the `w`-integral at `√a·u·B`, and the `u⁻¹` cancels). -/
theorem K4_corner_fubini (g : ℝ → ℝ → ℝ) (Cg A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0)
    (hsuppV : ∀ u v, B ≤ v → g u v = 0)
    (a : ℝ) (ha : 0 < a) :
    ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/(Real.sqrt a * u))
      = ∫ w in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          ∫ u in Ioi (0:ℝ), g u (w/(Real.sqrt a * u)) / u := by
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set F : ℝ → ℝ → ℝ := fun u w =>
    u⁻¹ * (UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/(Real.sqrt a * u)))
    with hFdef
  have hKc : Continuous (fun w : ℝ => UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    fun_prop
  have hFm : Measurable (Function.uncurry F) := by
    apply Measurable.mul
    · exact measurable_fst.inv
    · apply Measurable.mul
      · exact hKc.measurable.comp measurable_snd
      · exact hgc.measurable.comp (measurable_fst.prodMk
          (measurable_snd.div (measurable_fst.const_mul (Real.sqrt a))))
  -- per-u section integrability (u > 0)
  have hsec : ∀ u : ℝ, 0 < u → Integrable (fun w => F u w) (volume.restrict (Ioi (0:ℝ))) := by
    intro u hu
    have hsm : AEStronglyMeasurable (fun w => g u (w/(Real.sqrt a * u)))
        (volume.restrict (Ioi (0:ℝ))) :=
      (hgc.comp (continuous_const.prodMk
        ((continuous_id.div_const (Real.sqrt a * u))))).aestronglyMeasurable
    have hbd : ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))),
        ‖g u (w/(Real.sqrt a * u))‖ ≤ Cg :=
      ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hgb _ _
    have := (K4_sq_integrable.bdd_mul hsm hbd).const_mul (u⁻¹)
    apply this.congr (ae_of_all _ fun w => ?_)
    rw [hFdef]
    dsimp only
    ring
  -- the norm marginal is bounded by (7·Cg·B·√a)·1_(0,A]
  have hmarg : Integrable (fun u => ∫ w in Ioi (0:ℝ), ‖F u w‖) (volume.restrict (Ioi (0:ℝ))) := by
    have hsm : AEStronglyMeasurable (fun u => ∫ w in Ioi (0:ℝ), ‖F u w‖)
        (volume.restrict (Ioi (0:ℝ))) := by
      have : StronglyMeasurable (Function.uncurry (fun u w => ‖F u w‖)) :=
        (hFm.norm).stronglyMeasurable
      exact this.integral_prod_right'.aestronglyMeasurable
    have hDint : Integrable
        (fun u => (Ioc (0:ℝ) A).indicator (fun _ => 7*Cg*B*Real.sqrt a) u)
        (volume.restrict (Ioi (0:ℝ))) := by
      apply Integrable.integrableOn
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    apply Integrable.mono' hDint hsm
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    by_cases huA : u ≤ A
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, huA⟩), Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
      set c := Real.sqrt a * u * B with hcdef
      have hc : 0 < c := by positivity
      have hptbd : ∀ w ∈ Ioi (0:ℝ),
          ‖F u w‖ ≤ (Ioc (0:ℝ) c).indicator (fun _ => u⁻¹ * 7 * Cg) w := by
        intro w hw
        rw [mem_Ioi] at hw
        by_cases hwc : w ≤ c
        · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hw, hwc⟩), hFdef]
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_inv, abs_of_pos hu]
          calc u⁻¹ * (|UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |g u (w/(Real.sqrt a * u))|)
              ≤ u⁻¹ * (7 * Cg) := by
                apply mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul (K4_abs_bound _ (sq_nonneg w)) (hgb _ _) (abs_nonneg _)
                  (by norm_num)
            _ = u⁻¹ * 7 * Cg := by ring
        · push_neg at hwc
          have hzero : g u (w/(Real.sqrt a * u)) = 0 := by
            apply hsuppV
            rw [le_div_iff₀ (by positivity)]
            rw [hcdef] at hwc
            nlinarith
          rw [hFdef]
          dsimp only
          rw [hzero, mul_zero, mul_zero, norm_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) w
      calc (∫ w in Ioi (0:ℝ), ‖F u w‖)
          ≤ ∫ w in Ioi (0:ℝ), (Ioc (0:ℝ) c).indicator (fun _ => u⁻¹ * 7 * Cg) w := by
            apply setIntegral_mono_on ((hsec u hu).norm) ?_ measurableSet_Ioi hptbd
            apply Integrable.integrableOn
            rw [integrable_indicator_iff measurableSet_Ioc]
            exact integrableOn_const
              (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        _ ≤ 7*Cg*B*Real.sqrt a := by
            rw [integral_indicator measurableSet_Ioc, setIntegral_const]
            have hmeas : (volume.restrict (Ioi (0:ℝ))).real (Ioc (0:ℝ) c) = c := by
              show ((volume.restrict (Ioi (0:ℝ))) (Ioc (0:ℝ) c)).toReal = c
              rw [Measure.restrict_apply measurableSet_Ioc,
                show Ioc (0:ℝ) c ∩ Ioi 0 = Ioc 0 c from by
                  rw [Set.inter_eq_left]; exact Ioc_subset_Ioi_self,
                Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
              ring
            rw [hmeas, smul_eq_mul, hcdef]
            have huinv : u⁻¹ * u = 1 := inv_mul_cancel₀ hu.ne'
            apply le_of_eq
            calc (Real.sqrt a * u * B) * (u⁻¹ * 7 * Cg)
                = 7*Cg*B*Real.sqrt a * (u⁻¹ * u) := by ring
              _ = 7*Cg*B*Real.sqrt a := by rw [huinv, mul_one]
    · push_neg at huA
      have hzero : ∀ w, F u w = 0 := by
        intro w
        rw [hFdef]
        dsimp only
        rw [hsuppU u _ huA.le, mul_zero, mul_zero]
      simp only [hzero, norm_zero, integral_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) u
  -- product integrability and the swap
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff (hFm.aestronglyMeasurable)]
    constructor
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      rw [mem_Ioi] at hu
      exact hsec u hu
    · exact hmarg
  have hswap := integral_integral_swap hprod
  -- massage both sides
  have hL : (∫ u in Ioi (0:ℝ), ∫ w in Ioi (0:ℝ), F u w)
      = ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * g u (w/(Real.sqrt a * u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [← integral_const_mul]
  have hR : (∫ w in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), F u w)
      = ∫ w in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          ∫ u in Ioi (0:ℝ), g u (w/(Real.sqrt a * u)) / u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w _
    dsimp only
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    rw [hFdef]
    dsimp only
    ring
  rw [← hL, ← hR]
  exact hswap

/-! ## The outer log-dominator (K4-corner step 3a) -/

/-- `|ln w| ≤ w + 4·w^{−1/4}` for `w > 0`. -/
theorem abs_log_le (w : ℝ) (hw : 0 < w) :
    |Real.log w| ≤ w + 4 * w ^ (-(1:ℝ)/4) := by
  have hrp : (0:ℝ) < w ^ (-(1:ℝ)/4) := Real.rpow_pos_of_pos hw _
  rcases le_or_gt 1 w with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos hw
    linarith
  · have hlt : Real.log w < 0 := Real.log_neg hw h1
    rw [abs_of_neg hlt]
    have hinv : (0:ℝ) < w⁻¹ := inv_pos.mpr hw
    have hq : Real.log (w⁻¹ ^ ((1:ℝ)/4)) ≤ w⁻¹ ^ ((1:ℝ)/4) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hinv _)
    rw [Real.log_rpow hinv, Real.log_inv] at hq
    have hconv : w⁻¹ ^ ((1:ℝ)/4) = w ^ (-(1:ℝ)/4) := by
      rw [← Real.rpow_neg_one w, ← Real.rpow_mul hw.le]
      norm_num
    rw [hconv] at hq
    nlinarith

/-- Pointwise envelope `|K4(w²)| ≤ ⅓e^{−w²}(1 + 4w² + 4w⁴)`. -/
theorem K4_sq_abs_le (w : ℝ) :
    |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
      ≤ (1/3) * Real.exp (-w^2) * (1 + 4*w^2 + 4*w^4) := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3),
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg w, sq_nonneg (w^2)]

/-- **Integrability of the log dominator**: `∫₀^∞ |K4(w²)|·|ln w| dw < ∞`.
Split at `1`: on `(0,1]` the log is beaten by `35·w^{−1/4}` with `|K4| ≤ 7`; on
`(1,∞)` `ln w ≤ w` with the Gaussian envelope. -/
theorem K4_log_integrable :
    IntegrableOn (fun w => |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
      * |Real.log w|) (Ioi (0:ℝ)) := by
  have hKm : Measurable (fun w : ℝ =>
      |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |Real.log w|) := by
    have hKc : Continuous (fun w : ℝ =>
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)) := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
      fun_prop
    exact (hKc.abs.measurable).mul Real.measurable_log.abs
  rw [show Ioi (0:ℝ) = Ioc (0:ℝ) 1 ∪ Ioi 1 from
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)).symm]
  apply IntegrableOn.union
  · -- (0,1]: dominate by 35·w^{−1/4}
    have hDint : IntegrableOn (fun w : ℝ => 35 * w ^ (-(1:ℝ)/4)) (Ioc (0:ℝ) 1) := by
      have h := intervalIntegral.intervalIntegrable_rpow'
        (a := 0) (b := 1) (by norm_num : (-1:ℝ) < -(1:ℝ)/4)
      rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
      exact h.const_mul 35
    apply Integrable.mono' hDint (hKm.aestronglyMeasurable)
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hrp1 : (1:ℝ) ≤ w ^ (-(1:ℝ)/4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hw0 hw1 (by norm_num)
    have hlog : |Real.log w| ≤ 5 * w ^ (-(1:ℝ)/4) := by
      have := abs_log_le w hw0
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    calc |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |Real.log w|
        ≤ 7 * (5 * w ^ (-(1:ℝ)/4)) := by
          apply mul_le_mul (UnifiedTheory.Audit.KFCausalMinkowski4DCorner.K4_abs_bound _ (sq_nonneg w)) hlog
            (abs_nonneg _) (by norm_num)
      _ = 35 * w ^ (-(1:ℝ)/4) := by ring
  · -- (1,∞): dominate by the Gaussian envelope times w
    have h1i : IntegrableOn (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
      (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (1:ℝ))).integrableOn
    have h3i : IntegrableOn (fun x : ℝ => x ^ (3:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
      (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (3:ℝ))).integrableOn
    have h5i : IntegrableOn (fun x : ℝ => x ^ (5:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
      (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (5:ℝ))).integrableOn
    have hDint : IntegrableOn (fun w : ℝ =>
        (1/3) * (w ^ (1:ℝ) * Real.exp (-(1:ℝ) * w ^ 2))
          + (4/3) * (w ^ (3:ℝ) * Real.exp (-(1:ℝ) * w ^ 2))
          + (4/3) * (w ^ (5:ℝ) * Real.exp (-(1:ℝ) * w ^ 2))) (Ioi 1) := by
      apply IntegrableOn.mono_set ?_ (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
      exact ((h1i.const_mul (1/3)).add (h3i.const_mul (4/3))).add (h5i.const_mul (4/3))
    apply Integrable.mono' hDint (hKm.aestronglyMeasurable)
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro w hw
    rw [mem_Ioi] at hw
    have hw0 : (0:ℝ) < w := lt_trans one_pos hw
    have hlogw : |Real.log w| ≤ w := by
      rw [abs_of_nonneg (Real.log_nonneg hw.le)]
      have := Real.log_le_sub_one_of_pos hw0
      linarith
    have hK := K4_sq_abs_le w
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    have hrw : ∀ r : ℝ, w ^ r = w ^ r := fun _ => rfl
    calc |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |Real.log w|
        ≤ ((1/3) * Real.exp (-w^2) * (1 + 4*w^2 + 4*w^4)) * w := by
          apply mul_le_mul hK hlogw (abs_nonneg _) (by positivity)
      _ = (1/3) * (w ^ (1:ℝ) * Real.exp (-(1:ℝ) * w ^ 2))
          + (4/3) * (w ^ (3:ℝ) * Real.exp (-(1:ℝ) * w ^ 2))
          + (4/3) * (w ^ (5:ℝ) * Real.exp (-(1:ℝ) * w ^ 2)) := by
          rw [show w ^ (1:ℝ) = w from Real.rpow_one w,
            show w ^ (3:ℝ) = w ^ (3:ℕ) from by rw [← Real.rpow_natCast w 3]; norm_num,
            show w ^ (5:ℝ) = w ^ (5:ℕ) from by rw [← Real.rpow_natCast w 5]; norm_num,
            neg_one_mul]
          ring

/-- **The uniform hyperbola bound (K4-corner step 3b).**  For `g` with `|g| ≤ Cg`,
`|∂_u g| ≤ Mu`, `u`-support `[0,A]`, ANY second-argument family `y`, and `w > 0`:

    |∫₀^∞ (g(ws, y(s)) − g(s, y(s)))/s ds|  ≤  Mu·A + Cg·|ln w|.

MVT controls `s ≤ min(A, A/w)` (both terms alive); the support-mismatch region
`(min, max]` contributes `Cg·ln(max/min) = Cg·|ln w|`; beyond `max` both vanish.
Uniform in `y`, hence in the boost parameter — the outer-DCT dominator. -/
theorem D_bound (g pdug : ℝ → ℝ → ℝ) (Mu Cg A : ℝ) (hA : 0 < A)
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsupp : ∀ u v, A ≤ u → g u v = 0)
    (y : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    |∫ s in Ioi (0:ℝ), (g (w*s) (y s) - g s (y s)) / s|
      ≤ Mu * A + Cg * |Real.log w| := by
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0 0)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  set m := min A (A/w) with hmdef
  set M := max A (A/w) with hMdef
  have hm : 0 < m := lt_min hA (div_pos hA hw)
  have hmM : m ≤ M := min_le_max
  have hlipu : ∀ v x x' : ℝ, |g x v - g x' v| ≤ Mu * |x - x'| := by
    intro v x x'
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => g u v) (f' := fun u => pdug u v)
      (fun z _ => (hdu v z).hasDerivWithinAt)
      (fun z _ => by simpa [Real.norm_eq_abs] using hMu z v) (mem_univ x') (mem_univ x)
    simpa [Real.norm_eq_abs] using h
  set φ : ℝ → ℝ := fun s => (Ioc (0:ℝ) m).indicator (fun _ => Mu * |w - 1|) s
      + (Ioc m M).indicator (fun _ => Cg) s * s⁻¹ with hφdef
  have hφ1int : Integrable ((Ioc (0:ℝ) m).indicator (fun _ => Mu * |w - 1|))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hφ2int : Integrable (fun s => (Ioc m M).indicator (fun _ => Cg) s * s⁻¹)
      (volume.restrict (Ioi (0:ℝ))) := by
    have hmeas : AEStronglyMeasurable
        (fun s => (Ioc m M).indicator (fun _ => Cg) s * s⁻¹)
        (volume.restrict (Ioi (0:ℝ))) :=
      ((measurable_const.indicator measurableSet_Ioc).mul measurable_inv).aestronglyMeasurable
    have hDint : Integrable ((Ioc m M).indicator (fun _ => Cg * m⁻¹))
        (volume.restrict (Ioi (0:ℝ))) := by
      apply Integrable.integrableOn
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    apply Integrable.mono' hDint hmeas
    apply ae_of_all
    intro s
    by_cases hmem : s ∈ Ioc m M
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hCg0, abs_inv, abs_of_pos (lt_trans hm hmem.1)]
      apply mul_le_mul_of_nonneg_left ?_ hCg0
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hm hmem.1.le
    · rw [Set.indicator_of_notMem hmem, zero_mul, norm_zero]
      exact Set.indicator_apply_nonneg (fun _ => by positivity)
  have hφint : Integrable φ (volume.restrict (Ioi (0:ℝ))) := hφ1int.add hφ2int
  have hpt : ∀ s ∈ Ioi (0:ℝ), ‖(g (w*s) (y s) - g s (y s)) / s‖ ≤ φ s := by
    intro s hs
    rw [mem_Ioi] at hs
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs]
    simp only [hφdef]
    by_cases hsm : s ≤ m
    · have hnot2 : s ∉ Ioc m M := by
        intro hmem
        exact absurd (Set.mem_Ioc.mp hmem).1 (not_lt.mpr hsm)
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs, hsm⟩),
        Set.indicator_of_notMem hnot2, zero_mul, add_zero, div_le_iff₀ hs]
      calc |g (w*s) (y s) - g s (y s)| ≤ Mu * |w*s - s| := hlipu _ _ _
        _ = Mu * |w - 1| * s := by
            rw [show w*s - s = (w-1)*s from by ring, abs_mul, abs_of_pos hs]
            ring
    · push_neg at hsm
      have hnot1 : s ∉ Ioc (0:ℝ) m := by
        intro hmem
        exact absurd (Set.mem_Ioc.mp hmem).2 (not_le.mpr hsm)
      rw [Set.indicator_of_notMem hnot1, zero_add]
      by_cases hsM : s ≤ M
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hsm, hsM⟩)]
        have hone : g (w*s) (y s) = 0 ∨ g s (y s) = 0 := by
          rcases min_lt_iff.mp (hmdef ▸ hsm) with h | h
          · exact Or.inr (hsupp _ _ h.le)
          · refine Or.inl (hsupp _ _ ?_)
            rw [div_lt_iff₀ hw] at h
            nlinarith
        have habs : |g (w*s) (y s) - g s (y s)| ≤ Cg := by
          rcases hone with h | h
          · rw [h, zero_sub, abs_neg]; exact hgb _ _
          · rw [h, sub_zero]; exact hgb _ _
        rw [div_le_iff₀ hs]
        calc |g (w*s) (y s) - g s (y s)| ≤ Cg := habs
          _ = Cg * s⁻¹ * s := by field_simp
      · push_neg at hsM
        have hnot2 : s ∉ Ioc m M := by
          intro hmem
          exact absurd (Set.mem_Ioc.mp hmem).2 (not_le.mpr hsM)
        rw [Set.indicator_of_notMem hnot2, zero_mul]
        have h1 : g s (y s) = 0 :=
          hsupp _ _ (le_of_lt (lt_of_le_of_lt (le_max_left _ _) (hMdef ▸ hsM)))
        have h2 : g (w*s) (y s) = 0 := by
          apply hsupp
          have := lt_of_le_of_lt (le_max_right A (A/w)) (hMdef ▸ hsM)
          rw [div_lt_iff₀ hw] at this
          nlinarith
        rw [h1, h2]
        simp
  have hφval : (∫ s in Ioi (0:ℝ), φ s) = Mu * |w - 1| * m + Cg * Real.log (M/m) := by
    simp only [hφdef]
    rw [integral_add hφ1int hφ2int]
    congr 1
    · rw [integral_indicator measurableSet_Ioc, setIntegral_const]
      have hmeasval : (volume.restrict (Ioi (0:ℝ))).real (Ioc (0:ℝ) m) = m := by
        show ((volume.restrict (Ioi (0:ℝ))) (Ioc (0:ℝ) m)).toReal = m
        rw [Measure.restrict_apply measurableSet_Ioc,
          show Ioc (0:ℝ) m ∩ Ioi 0 = Ioc 0 m from by
            rw [Set.inter_eq_left]; exact Ioc_subset_Ioi_self,
          Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hm.le]
      rw [hmeasval, smul_eq_mul]
      ring
    · have hpt2 : ∀ s : ℝ, (Ioc m M).indicator (fun _ => Cg) s * s⁻¹
          = (Ioc m M).indicator (fun t => Cg * t⁻¹) s := by
        intro s
        by_cases hmem : s ∈ Ioc m M
        · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
      simp_rw [hpt2]
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        show Ioc m M ∩ Ioi 0 = Ioc m M from by
          rw [Set.inter_eq_left]; exact fun x hx => lt_trans hm hx.1,
        integral_const_mul]
      congr 1
      rw [← intervalIntegral.integral_of_le hmM, integral_inv (by
        rw [Set.uIcc_of_le hmM]
        intro hmem
        exact absurd hmem.1 (not_le.mpr hm))]
  calc |∫ s in Ioi (0:ℝ), (g (w*s) (y s) - g s (y s)) / s|
      ≤ ∫ s in Ioi (0:ℝ), φ s := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hφint
          (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    _ = Mu * |w - 1| * m + Cg * Real.log (M/m) := hφval
    _ ≤ Mu * A + Cg * |Real.log w| := by
        rcases le_total 1 w with h1 | h1
        · have hAw : A/w ≤ A := div_le_self hA.le h1
          have hmeq : m = A/w := by rw [hmdef]; exact min_eq_right hAw
          have hMeq : M = A := by rw [hMdef]; exact max_eq_left hAw
          have hMm : M/m = w := by
            rw [hmeq, hMeq]
            field_simp
          have hlogd : Real.log (M/m) = |Real.log w| := by
            rw [hMm, abs_of_nonneg (Real.log_nonneg h1)]
          have habs : |w - 1| = w - 1 := abs_of_nonneg (by linarith)
          have hprod : (w-1) * (A/w) = A - A/w := by
            field_simp
            try ring
          rw [hlogd, hmeq, habs]
          have hAw0 : (0:ℝ) ≤ A/w := by positivity
          nlinarith [mul_nonneg hMu0 hAw0]
        · have hAw : A ≤ A/w := by
            rw [le_div_iff₀ hw]
            nlinarith
          have hmeq : m = A := by rw [hmdef]; exact min_eq_left hAw
          have hMeq : M = A/w := by rw [hMdef]; exact max_eq_right hAw
          have hMm : M/m = 1/w := by
            rw [hmeq, hMeq]
            field_simp
          have hlogd : Real.log (M/m) = |Real.log w| := by
            rw [hMm, one_div, Real.log_inv,
              abs_of_nonpos (Real.log_nonpos hw.le h1)]
          have habs : |w - 1| = 1 - w := by
            rw [abs_of_nonpos (by linarith)]
            ring
          rw [hlogd, hmeq, habs]
          nlinarith [mul_nonneg (mul_nonneg hMu0 hw.le) hA.le]

/-- **The K4-corner outer DCT (step 4).**  Under the standing hypotheses,

    ∫₀^∞ K4(w²)·[∫₀^∞ (g(ws,(√a·s)⁻¹) − g(s,(√a·s)⁻¹))/s ds] dw
        ⟶  −g(0,0) · ∫₀^∞ K4(w²)·ln w dw       (a → ∞):

dominated convergence with the dominator `Mu·A·|K4(w²)| + Cg·|K4(w²)|·|ln w|`
(`D_bound` + `K4_log_integrable` — fixed, `a`-independent), pointwise limit
`frullani_concentration`. -/
theorem K4_corner_outer_dct (g pdug : ℝ → ℝ → ℝ) (Mu Cg A : ℝ) (hA : 0 < A)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsupp : ∀ u v, A ≤ u → g u v = 0) :
    Tendsto (fun a : ℝ => ∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
        (∫ s in Ioi (0:ℝ),
          (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s))
      atTop (𝓝 (-(g 0 0) * ∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * Real.log w)) := by
  have hKc : Continuous (fun w : ℝ =>
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    fun_prop
  have hdct : Tendsto (fun a : ℝ => ∫ w in Ioi (0:ℝ),
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
      (∫ s in Ioi (0:ℝ),
        (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s))
      atTop (𝓝 (∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
        (-(g 0 0) * Real.log w))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun w => Mu * A * |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
        + Cg * (|UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |Real.log w|))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      have hFm : Measurable (Function.uncurry (fun w s =>
          (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s)) := by
        have hy : Measurable (fun p : ℝ × ℝ => (Real.sqrt a * p.2)⁻¹) :=
          (measurable_snd.const_mul (Real.sqrt a)).inv
        have h1 : Measurable (fun p : ℝ × ℝ => g (p.1 * p.2) ((Real.sqrt a * p.2)⁻¹)) :=
          hgc.measurable.comp ((measurable_fst.mul measurable_snd).prodMk hy)
        have h2 : Measurable (fun p : ℝ × ℝ => g p.2 ((Real.sqrt a * p.2)⁻¹)) :=
          hgc.measurable.comp (measurable_snd.prodMk hy)
        exact (h1.sub h2).div measurable_snd
      have hmarg : StronglyMeasurable (fun w => ∫ s in Ioi (0:ℝ),
          (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s) :=
        hFm.stronglyMeasurable.integral_prod_right'
      exact (hKc.measurable.mul hmarg.measurable).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      rw [Real.norm_eq_abs, abs_mul]
      calc |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| *
          |∫ s in Ioi (0:ℝ),
            (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s|
          ≤ |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| *
            (Mu * A + Cg * |Real.log w|) := by
            apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact D_bound g pdug Mu Cg A hA hdu hMu hgb hsupp
              (fun s => (Real.sqrt a * s)⁻¹) w hw
        _ = Mu * A * |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
            + Cg * (|UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| * |Real.log w|) := by
            ring
    · exact ((K4_sq_integrable.abs.const_mul (Mu*A)).add
        (K4_log_integrable.const_mul Cg))
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      exact (frullani_concentration g pdug Mu A hA hgc hdu hMu hsupp w hw).const_mul
        (UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2))
  have hval : (∫ w in Ioi (0:ℝ),
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * (-(g 0 0) * Real.log w))
      = -(g 0 0) * ∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * Real.log w := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w _
    ring
  rwa [hval] at hdct

/-- Per-`(a,w)` integrability of the boost-profile integrand
`s ↦ g(ws, (√a·s)⁻¹)/s`: the `v`-support kills it below `(√a·B)⁻¹`
(where `(√a·s)⁻¹ ≥ B`), the `u`-support above `A/w`; in between `1/s` is
bounded by `√a·B`. -/
theorem G_integrable (g : ℝ → ℝ → ℝ) (Cg A B : ℝ)
    (hgc : Continuous (Function.uncurry g)) (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0)
    (hB : 0 < B) (a : ℝ) (ha : 0 < a) (w : ℝ) (hw : 0 < w) :
    IntegrableOn (fun s => g (w*s) ((Real.sqrt a * s)⁻¹) / s) (Ioi (0:ℝ)) := by
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set lo := (Real.sqrt a * B)⁻¹ with hlodef
  have hlo : 0 < lo := by positivity
  have hmeas : AEStronglyMeasurable (fun s => g (w*s) ((Real.sqrt a * s)⁻¹) / s)
      (volume.restrict (Ioi (0:ℝ))) := by
    have hy : Measurable (fun s : ℝ => (Real.sqrt a * s)⁻¹) :=
      (measurable_id.const_mul (Real.sqrt a)).inv
    exact ((hgc.measurable.comp ((measurable_id.const_mul w).prodMk hy)).div
      measurable_id).aestronglyMeasurable
  have hDint : Integrable ((Ioc lo (A/w)).indicator (fun _ => Cg * (Real.sqrt a * B)))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  apply Integrable.mono' hDint hmeas
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro s hs
  rw [mem_Ioi] at hs
  rcases lt_or_ge lo s with hlos | hslo
  swap
  · -- below the v-support cutoff: the integrand vanishes
    have hz : g (w*s) ((Real.sqrt a * s)⁻¹) = 0 := by
      apply hsuppV
      have h1 : Real.sqrt a * s ≤ 1 / B := by
        calc Real.sqrt a * s ≤ Real.sqrt a * lo :=
              mul_le_mul_of_nonneg_left hslo (le_of_lt hsa)
          _ = 1 / B := by rw [hlodef]; field_simp
      calc B = 1 / (1/B) := by field_simp
        _ ≤ 1 / (Real.sqrt a * s) := one_div_le_one_div_of_le (by positivity) h1
        _ = (Real.sqrt a * s)⁻¹ := one_div _
    rw [hz]
    simp only [zero_div, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg hCg (by positivity)) s
  · rcases lt_or_ge (A/w) s with hsAw | hsAw
    swap
    · -- the live band: 1/s ≤ √a·B
      rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨hlos, hsAw⟩)]
      have hinv : s⁻¹ ≤ Real.sqrt a * B := by
        have h1 : 1/s ≤ 1/lo := one_div_le_one_div_of_le hlo (le_of_lt hlos)
        rw [one_div, one_div, hlodef, inv_inv] at h1
        exact h1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, div_eq_mul_inv]
      exact mul_le_mul (hgb _ _) hinv (inv_nonneg.mpr (le_of_lt hs)) hCg
    · -- beyond the u-support: the integrand vanishes
      have hz : g (w*s) ((Real.sqrt a * s)⁻¹) = 0 := by
        apply hsuppU
        rw [div_lt_iff₀ hw] at hsAw
        nlinarith
      have hnot : s ∉ Ioc lo (A/w) := by
        intro hmem
        exact absurd (mem_Ioc.mp hmem).2 (not_le.mpr hsAw)
      rw [hz, Set.indicator_of_notMem hnot]
      simp

/-- **The complete K4-corner theorem.**  For `g` continuously differentiable in `u`
with uniform bounds and compact support in both arguments,

    √a · ∫₀^∞∫₀^∞ K4(a·u²v²)·g(u,v) dv du
        ⟶  −g(0,0) · ∫₀^∞ K4(w²)·ln w dw       (a → ∞).

The chain: pull `√a` inside (`inner_sub`), swap the order (`fubini`), pass to the
multiplicative Haar profile (`haar_link`), subtract the `w = 1` profile at zero
cost (`K4_mass_zero`), and dominate (`outer_dct`). -/
theorem K4_corner_limit (g pdug : ℝ → ℝ → ℝ) (Mu Cg A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0) :
    Tendsto (fun a : ℝ => Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*v^2) * g u v)
      atTop (𝓝 (-(g 0 0) * ∫ w in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) * Real.log w)) := by
  apply Filter.Tendsto.congr'
    (f₁ := fun a : ℝ => ∫ w in Ioi (0:ℝ),
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
      (∫ s in Ioi (0:ℝ),
        (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s))
  swap
  · exact K4_corner_outer_dct g pdug Mu Cg A hA hgc hdu hMu hgb hsuppU
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  have hKc : Continuous (fun w : ℝ =>
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    fun_prop
  -- the fixed `w = 1` boost profile
  have hG1 : IntegrableOn (fun s => g s ((Real.sqrt a * s)⁻¹) / s) (Ioi (0:ℝ)) := by
    have h := G_integrable g Cg A B hgc hgb hsuppU hsuppV hB a ha 1 one_pos
    simpa using h
  -- the profile difference is the difference of profiles
  have hdiff : ∀ w : ℝ, 0 < w →
      (∫ s in Ioi (0:ℝ),
        (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s)
      = (∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
        - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s := by
    intro w hw
    rw [← integral_sub (G_integrable g Cg A B hgc hgb hsuppU hsuppV hB a ha w hw) hG1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only
    rw [sub_div]
  -- marginal measurability of the moving profile
  have hy : Measurable (fun s : ℝ => (Real.sqrt a * s)⁻¹) :=
    (measurable_id.const_mul (Real.sqrt a)).inv
  have hm1 : StronglyMeasurable (fun w => ∫ s in Ioi (0:ℝ),
      g (w*s) ((Real.sqrt a * s)⁻¹) / s) := by
    have hFm : Measurable (Function.uncurry (fun w s =>
        g (w*s) ((Real.sqrt a * s)⁻¹) / s)) := by
      have h1 : Measurable (fun p : ℝ × ℝ => g (p.1 * p.2) ((Real.sqrt a * p.2)⁻¹)) :=
        hgc.measurable.comp ((measurable_fst.mul measurable_snd).prodMk
          (hy.comp measurable_snd))
      exact h1.div measurable_snd
    exact hFm.stronglyMeasurable.integral_prod_right'
  -- integrability of the two pieces of the subtraction
  have ip1 : Integrable (fun w =>
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
      ((∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
        - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s))
      (volume.restrict (Ioi (0:ℝ))) := by
    apply Integrable.mono' ((K4_sq_integrable.abs.const_mul (Mu*A)).add
      (K4_log_integrable.const_mul Cg))
    · exact (hKc.measurable.mul
        (hm1.measurable.sub measurable_const)).aestronglyMeasurable
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      rw [Real.norm_eq_abs, abs_mul]
      calc |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| *
          |(∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
            - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s|
          ≤ |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)| *
            (Mu * A + Cg * |Real.log w|) := by
            apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [← hdiff w hw]
            exact D_bound g pdug Mu Cg A hA hdu hMu hgb hsuppU
              (fun s => (Real.sqrt a * s)⁻¹) w hw
        _ = Mu * A * |UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
            + Cg * (|UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2)|
              * |Real.log w|) := by ring
  have ip2 : Integrable (fun w =>
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
      ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
      (volume.restrict (Ioi (0:ℝ))) :=
    K4_sq_integrable.mul_const _
  -- the subtracted piece integrates to zero against the massless kernel
  have hzero : (∫ w in Ioi (0:ℝ),
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
      ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s) = 0 := by
    have h := integral_smul_const (μ := volume.restrict (Ioi (0:ℝ)))
      (f := fun w => UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2))
      (c := ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
    simp only [smul_eq_mul] at h
    rw [h, K4_mass_zero, zero_mul]
  -- the chain
  symm
  calc Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*v^2) * g u v
      = ∫ u in Ioi (0:ℝ), Real.sqrt a * ∫ v in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (a*u^2*v^2) * g u v :=
        (integral_const_mul _ _).symm
    _ = ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          g u (w/(Real.sqrt a * u)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        rw [mem_Ioi] at hu
        exact K4_corner_inner_sub g a u ha hu
    _ = ∫ w in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          ∫ u in Ioi (0:ℝ), g u (w/(Real.sqrt a * u)) / u :=
        K4_corner_fubini g Cg A B hA hB hgc hgb hsuppU hsuppV a ha
    _ = ∫ w in Ioi (0:ℝ), UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          ∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro w hw
        rw [mem_Ioi] at hw
        dsimp only
        rw [K4_corner_haar_link g a w hw]
    _ = ∫ w in Ioi (0:ℝ),
          (UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
            ((∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
              - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
          + UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
            ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro w _
        ring
    _ = (∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
            ((∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
              - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s))
        + ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
            ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s :=
        integral_add ip1 ip2
    _ = ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
            ((∫ s in Ioi (0:ℝ), g (w*s) ((Real.sqrt a * s)⁻¹) / s)
              - ∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s) := by
        rw [hzero, add_zero]
    _ = ∫ w in Ioi (0:ℝ),
          UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4 (w^2) *
          (∫ s in Ioi (0:ℝ),
            (g (w*s) ((Real.sqrt a * s)⁻¹) - g s ((Real.sqrt a * s)⁻¹)) / s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro w hw
        rw [mem_Ioi] at hw
        dsimp only
        rw [hdiff w hw]

#print axioms haar_scale

#print axioms frullani_pos
#print axioms frullani_concentration
#print axioms K4_corner_inner_sub
#print axioms K4_corner_haar_link

end UnifiedTheory.Audit.KFCausalMinkowski4DCorner
