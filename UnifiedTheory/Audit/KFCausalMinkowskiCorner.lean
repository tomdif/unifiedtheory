/-
  Audit/KFCausalMinkowskiCorner.lean   (Volume sector → the corner-kernel gate, cores)

  The full 2D causal-set continuum theorem reduces (per review) to ONE corner-kernel limit,
  avoiding rapidity coordinates and doing the cancellation before domination:

      a ∫_0^∞ ∫_0^∞ H(aUW) g(U,W) dU dW  →  -½ g(0,0)      (a = ρc₀ → ∞,  g = ∂_U∂_W φ).

  The route (do NOT apply DCT to `a H(aUW)` directly -- its mass is not uniformly bounded
  in the boost direction) uses the kernel identity `H(aUW) = -½ ∂_W(W e^{-aUW})`, IBP in
  `W` first, and then the INNER concentration limit with a FIXED, mass-one kernel:

      aw ∫_0^∞ e^{-aUw} h(U) dU  →  h(0)      (w > 0 fixed),     since  aw ∫_0^∞ e^{-aUw} dU = 1.

  This file CLOSES that gate: `corner_kernel_limit` proves, axiom-clean and sorry-free,

      a ∫_{(0,∞)} ∫_{(0,∞)} H(aUW) g(U,W) dW dU  →  -½ g(0,0)      (a → ∞),

  for `g` with continuous compactly-supported `∂_W g` and `W`-support box `B`.  The route,
  entirely on the finite rectangle before any domination:

    * `corner_kernel_deriv` / `corner_kernel_identity` :  `H(aUW) = -½ ∂_W(W e^{-aUW})`.
    * `concentration_limit` / `scaling_change_of_var` / `inner_limit` :  the inner limit
      `aw ∫_0^∞ e^{-aUw} ∂_W g(U,w) dU → ∂_W g(0,w)` with the FIXED mass-one kernel.
    * `inner_bound` + `outer_dct` :  the outer dominated convergence over the finite
      `w`-support, dominator `M · 1_(0,B]`.
    * `boundary_ftc` :  `½ ∫_0^∞ ∂_W g(0,w) dw = -½ g(0,0)` (the sign).
    * `corner_rectangle_ibp` → `corner_Ioi_identity` :  the rectangle IBP (`W` first),
      lifted to `Ioi` via the support and Fubini (`integral_integral_swap_of_hasCompactSupport`).
    * `corner_integrand_aestronglyMeasurable` :  the parameter-integral measurability,
      derived from continuity, not assumed.
    * `corner_kernel_limit` :  the assembled gate.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowskiRadial

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowskiRadial

namespace UnifiedTheory.Audit.KFCausalMinkowskiCorner

/-- **Corner kernel derivative.**  `∂_W (W e^{-aUW}) = e^{-aUW}(1 - aUW)`. -/
theorem corner_kernel_deriv (a U W : ℝ) :
    HasDerivAt (fun w => w * Real.exp (-(a * U * w)))
      (Real.exp (-(a * U * W)) * (1 - a * U * W)) W := by
  have h1 : HasDerivAt (fun w : ℝ => w) 1 W := hasDerivAt_id W
  have h2 : HasDerivAt (fun w : ℝ => Real.exp (-(a * U * w))) (-(a * U) * Real.exp (-(a * U * W))) W := by
    have := (Real.hasDerivAt_exp (-(a * U * W))).comp W (((hasDerivAt_id W).const_mul (a * U)).neg)
    convert this using 1
    ring
  convert h1.mul h2 using 1
  ring

/-- **Corner kernel identity.**  `H(aUW) = -½ ∂_W(W e^{-aUW}) = -½ e^{-aUW}(1 - aUW)`.
Combined with `corner_kernel_deriv` this is the exact-derivative form used to integrate by
parts in `W` first (before any domination), the step that avoids the boost direction. -/
theorem corner_kernel_identity (a U W : ℝ) :
    Hkern (a * U * W) = -(1 / 2) * (Real.exp (-(a * U * W)) * (1 - a * U * W)) := by
  unfold Hkern; ring

/-- **Concentration limit (inner limit of the corner-kernel gate).**  For continuous
bounded `h`, `∫_0^∞ e^{-t} h(t/λ) dt → h(0)` as `λ → ∞`.  This is the substituted form of
`aw ∫_0^∞ e^{-aUw} h(U) dU → h(0)` (via `U = t/(aw)`); the FIXED dominator `M e^{-t}`
(integrable) and `∫_0^∞ e^{-t} = 1` are what make it work without a moving-support trap. -/
theorem concentration_limit (h : ℝ → ℝ) (M : ℝ) (hcont : Continuous h) (hM : ∀ x, |h x| ≤ M) :
    Tendsto (fun l : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-t) * h (t / l)) atTop (𝓝 (h 0)) := by
  have hexpint : IntegrableOn (fun t => Real.exp (-t)) (Ioi (0:ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1)
  have hexp1 : ∫ t in Ioi (0:ℝ), Real.exp (-t) = 1 := by rw [integral_exp_neg_Ioi]; simp
  have hdct : Tendsto (fun l : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-t) * h (t / l)) atTop
      (𝓝 (∫ t in Ioi (0:ℝ), Real.exp (-t) * h 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => M * Real.exp (-t))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with l _
      exact ((Real.continuous_exp.comp continuous_neg).mul
        (hcont.comp (continuous_id.div_const l))).aestronglyMeasurable
    · filter_upwards with l
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-t) * |h (t / l)|
          ≤ Real.exp (-t) * M := mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
        _ = M * Real.exp (-t) := by ring
    · exact hexpint.const_mul M
    · filter_upwards with t
      have htends : Tendsto (fun l : ℝ => t / l) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul t
      simpa using ((hcont.tendsto 0).comp htends).const_mul (Real.exp (-t))
  have hval : ∫ t in Ioi (0:ℝ), Real.exp (-t) * h 0 = h 0 := by
    rw [show (fun t => Real.exp (-t) * h 0) = fun t => h 0 * Real.exp (-t) from by funext t; ring,
      integral_const_mul, hexp1, mul_one]
  rwa [hval] at hdct

/-- **Scaling change of variables** (the substitution linking the two inner forms).
For `a, w > 0`,

    aw ∫_0^∞ e^{-aUw} h(U) dU  =  ∫_0^∞ e^{-t} h(t/(aw)) dt,

via `t = aUw` (`integral_comp_mul_left_Ioi`).  This turns the original-variable inner
expression into the `concentration_limit` form. -/
theorem scaling_change_of_var (h : ℝ → ℝ) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    a * w * ∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * h U
      = ∫ t in Ioi (0:ℝ), Real.exp (-t) * h (t / (a * w)) := by
  have hc0 : 0 < a * w := mul_pos ha hw
  have key := integral_comp_mul_left_Ioi (fun t => Real.exp (-t) * h (t / (a * w))) 0 hc0
  rw [mul_zero, smul_eq_mul] at key
  have hcancel : (∫ x in Ioi (0:ℝ), (fun t => Real.exp (-t) * h (t / (a * w))) (a * w * x))
      = ∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * h U := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    have hxeq : a * w * x / (a * w) = x := by
      rw [mul_comm (a * w) x, mul_div_assoc, div_self hc0.ne', mul_one]
    show Real.exp (-(a * w * x)) * h (a * w * x / (a * w)) = Real.exp (-(a * w * x)) * h x
    rw [hxeq]
  rw [hcancel] at key
  rw [key, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]

/-- **Inner limit for every fixed `w > 0`** (the corner-kernel gate's inner step, original
variable).  For continuous bounded `G` (playing the role of `∂_W g(·,w)`),

    aw ∫_0^∞ e^{-aUw} G(U) dU  →  G(0)      (a → ∞),

by the scaling substitution followed by `concentration_limit` (with `λ = aw → ∞`). -/
theorem inner_limit (G : ℝ → ℝ) (M : ℝ) (hcont : Continuous G) (hM : ∀ x, |G x| ≤ M)
    (w : ℝ) (hw : 0 < w) :
    Tendsto (fun a : ℝ => a * w * ∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U) atTop (𝓝 (G 0)) := by
  have hcomp : Tendsto (fun a : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-t) * G (t / (a * w)))
      atTop (𝓝 (G 0)) :=
    (concentration_limit G M hcont hM).comp (tendsto_id.atTop_mul_const hw)
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  exact (scaling_change_of_var G a w ha hw).symm

/-- **Boundary evaluation (the FTC step of the corner gate).**  If `G` is everywhere
differentiable with integrable derivative `G'` and vanishes past `B` (the `w`-support box),
then `∫_0^∞ G'(w) dw = -G(0)`.  Applied to `G = g(0,·)`, `G' = ∂_W g(0,·)` this gives
`½ ∫_0^∞ ∂_W g(0,w) dw = -½ g(0,0)` -- the sign of the corner limit, from compact support
at infinity via the fundamental theorem of calculus. -/
theorem boundary_ftc (G G' : ℝ → ℝ) (B : ℝ)
    (hderiv : ∀ x, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Ioi (0:ℝ)))
    (hsupp : ∀ w, B ≤ w → G w = 0) :
    ∫ w in Ioi (0:ℝ), G' w = - G 0 := by
  have htend : Tendsto G atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop B] with w hw
    exact (hsupp w hw).symm
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0:ℝ)) (fun x _ => hderiv x) hint htend
  rw [h, zero_sub]

/-- The corner gate's boundary value in the exact `-½ g(0,0)` form. -/
theorem boundary_ftc_half (G G' : ℝ → ℝ) (B : ℝ)
    (hderiv : ∀ x, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Ioi (0:ℝ)))
    (hsupp : ∀ w, B ≤ w → G w = 0) :
    (1 / 2) * ∫ w in Ioi (0:ℝ), G' w = -(1 / 2) * G 0 := by
  rw [boundary_ftc G G' B hderiv hint hsupp]; ring

/-- **Inner uniform bound (the outer DCT's dominator ingredient).**  For continuous bounded
`G` (`|G| ≤ M`) and `a, w > 0`, `|aw ∫_0^∞ e^{-aUw} G(U) dU| ≤ M`, because the kernel has
unit mass `aw ∫_0^∞ e^{-aUw} dU = 1`.  This is the `a`-independent dominator on the
`w`-support box that makes the outer dominated convergence legitimate. -/
theorem inner_bound (G : ℝ → ℝ) (M : ℝ) (hM : ∀ x, |G x| ≤ M)
    (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    |a * w * ∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U| ≤ M := by
  have hc0 : 0 < a * w := mul_pos ha hw
  have hexpint : IntegrableOn (fun U => Real.exp (-(a * w * U))) (Ioi (0:ℝ)) := by
    simpa only [neg_mul] using exp_neg_integrableOn_Ioi 0 hc0
  have hexpval : ∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) = (a * w)⁻¹ := by
    have hcov := integral_comp_mul_left_Ioi (fun u => Real.exp (-u)) 0 hc0
    simpa only [mul_zero, smul_eq_mul, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one] using hcov
  rw [abs_mul, abs_of_pos hc0]
  have hfg : |∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U| ≤ M * (a * w)⁻¹ := by
    calc |∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U|
        = ‖∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ U in Ioi (0:ℝ), M * Real.exp (-(a * w * U)) := by
          apply norm_integral_le_of_norm_le (hexpint.const_mul M)
          apply ae_restrict_of_forall_mem measurableSet_Ioi
          intro U _
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc Real.exp (-(a * w * U)) * |G U|
              ≤ Real.exp (-(a * w * U)) * M := mul_le_mul_of_nonneg_left (hM U) (Real.exp_pos _).le
            _ = M * Real.exp (-(a * w * U)) := by ring
      _ = M * (a * w)⁻¹ := by rw [integral_const_mul, hexpval]
  calc a * w * |∫ U in Ioi (0:ℝ), Real.exp (-(a * w * U)) * G U|
      ≤ a * w * (M * (a * w)⁻¹) := mul_le_mul_of_nonneg_left hfg hc0.le
    _ = M := by field_simp

/-- **Outer dominated convergence (the outer half of the corner gate).**  If the outer
integrand family `Φ a` is measurable, dominated by a fixed integrable `D` on `(0,∞)`, and
converges pointwise a.e. to `P` as `a → ∞`, then the outer integrals converge:
`∫_0^∞ Φ a w dw → ∫_0^∞ P w dw`.  In the corner gate `Φ a w = aw ∫_U e^{-aUw} ∂_W g(U,w) dU`,
`P w = ∂_W g(0,w)` (from `inner_limit`, a.e.), and `D = M · 1_(0,B]` (from `inner_bound` on
the `w`-support box).  The filter is `atTop` on `ℝ`, which is countably generated. -/
theorem outer_dct (Φ : ℝ → ℝ → ℝ) (P D : ℝ → ℝ)
    (hmeas : ∀ a, AEStronglyMeasurable (Φ a) (volume.restrict (Ioi (0:ℝ))))
    (hD : IntegrableOn D (Ioi (0:ℝ)))
    (hbound : ∀ᶠ a in atTop, ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))), ‖Φ a w‖ ≤ D w)
    (hlim : ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))), Tendsto (fun a => Φ a w) atTop (𝓝 (P w))) :
    Tendsto (fun a => ∫ w in Ioi (0:ℝ), Φ a w) atTop (𝓝 (∫ w in Ioi (0:ℝ), P w)) :=
  tendsto_integral_filter_of_dominated_convergence D
    (Eventually.of_forall hmeas) hbound hD hlim

/-! ## The finite-rectangle bridge (avoiding IBP under an improper integral) -/

/-- **Step 1 — rectangle IBP (pointwise in `U`).**  On the finite `W`-interval `[0,B]`, with
`g(U,B) = 0` (upper support) and `W=0` killing the lower term,

    a ∫_0^B H(aUW) g(U,W) dW  =  (a/2) ∫_0^B W e^{-aUW} ∂_W g(U,W) dW.

This is ordinary integration by parts on a compact interval (`integral_deriv_mul_eq_sub`),
using `corner_kernel_identity`/`corner_kernel_deriv`; no differentiation under an integral. -/
theorem corner_rectangle_ibp (g pdg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g)) (hpdgc : Continuous (Function.uncurry pdg))
    (hg : ∀ U W, HasDerivAt (fun W' => g U W') (pdg U W) W)
    (a U B : ℝ) (hgB : g U B = 0) :
    a * ∫ W in (0:ℝ)..B, Hkern (a * U * W) * g U W
      = (a / 2) * ∫ W in (0:ℝ)..B, W * Real.exp (-(a * U * W)) * pdg U W := by
  have hgU : Continuous (fun W => g U W) := hgc.comp (continuous_const.prodMk continuous_id)
  have hpdgU : Continuous (fun W => pdg U W) := hpdgc.comp (continuous_const.prodMk continuous_id)
  have hcu' : Continuous (fun W => Real.exp (-(a * U * W)) * (1 - a * U * W)) := by fun_prop
  have hcu : Continuous (fun W => W * Real.exp (-(a * U * W))) := by fun_prop
  have hu'int : IntervalIntegrable (fun W => Real.exp (-(a * U * W)) * (1 - a * U * W)) volume 0 B :=
    hcu'.intervalIntegrable 0 B
  have hv'int : IntervalIntegrable (fun W => pdg U W) volume 0 B := hpdgU.intervalIntegrable 0 B
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun W _ => corner_kernel_deriv a U W) (fun W _ => hg U W) hu'int hv'int
  rw [hgB] at hibp
  simp only [mul_zero, zero_mul, sub_zero] at hibp
  have hi1 : IntervalIntegrable
      (fun W => Real.exp (-(a * U * W)) * (1 - a * U * W) * g U W) volume 0 B :=
    (hcu'.mul hgU).intervalIntegrable 0 B
  have hi2 : IntervalIntegrable
      (fun W => W * Real.exp (-(a * U * W)) * pdg U W) volume 0 B :=
    (hcu.mul hpdgU).intervalIntegrable 0 B
  rw [intervalIntegral.integral_add hi1 hi2] at hibp
  have hHeq : ∫ W in (0:ℝ)..B, Hkern (a * U * W) * g U W
      = -(1 / 2) * ∫ W in (0:ℝ)..B, Real.exp (-(a * U * W)) * (1 - a * U * W) * g U W := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro W _
    dsimp only
    rw [corner_kernel_identity]; ring
  rw [hHeq]
  have hsplit : (∫ W in (0:ℝ)..B, Real.exp (-(a * U * W)) * (1 - a * U * W) * g U W)
      = - ∫ W in (0:ℝ)..B, W * Real.exp (-(a * U * W)) * pdg U W := by linarith [hibp]
  rw [hsplit]; ring

/-- A continuous function vanishing past `B > 0` is integrable on `(0,∞)`. -/
theorem corner_slice_integrable (f : ℝ → ℝ) (B : ℝ) (hB : 0 < B) (hfc : Continuous f)
    (hsupp : ∀ x, B ≤ x → f x = 0) : IntegrableOn f (Ioi (0:ℝ)) := by
  have h1 : IntegrableOn f (Ioc 0 B) :=
    (Continuous.integrableOn_Icc hfc : IntegrableOn f (Icc 0 B)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn f (Ioi B) :=
    integrableOn_zero.congr_fun (fun x hx => (hsupp x (le_of_lt hx)).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hB.le]
  exact h1.union h2

/-- **Interval → `Ioi` (support conversion).**  For continuous `f` vanishing past `B > 0`,
`∫_0^B f = ∫_{(0,∞)} f`.  Used to lift the finite-rectangle identity to `Ioi` integrals only
after the compact-interval work is done. -/
theorem corner_interval_to_Ioi (f : ℝ → ℝ) (B : ℝ) (hB : 0 < B) (hfc : Continuous f)
    (hsupp : ∀ x, B ≤ x → f x = 0) :
    ∫ x in (0:ℝ)..B, f x = ∫ x in Ioi (0:ℝ), f x := by
  have h1 : IntegrableOn f (Ioc 0 B) :=
    (Continuous.integrableOn_Icc hfc : IntegrableOn f (Icc 0 B)).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn f (Ioi B) :=
    integrableOn_zero.congr_fun (fun x hx => (hsupp x (le_of_lt hx)).symm) measurableSet_Ioi
  have h2z : ∫ x in Ioi B, f x = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ))
      (fun x hx => hsupp x (le_of_lt hx))]
    simp
  rw [intervalIntegral.integral_of_le hB.le, ← Ioc_union_Ioi_eq_Ioi hB.le,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2, h2z, add_zero]

/-- **Step 2+3 — the reduction identity on `Ioi × Ioi`.**  Integrating the rectangle IBP
over `U`, lifting to `Ioi` via the `W`-support, then Fubini (compact support) and pulling
`W` out of the `U`-integral gives

    a ∫_{(0,∞)} ∫_{(0,∞)} H(aUW) g(U,W) dW dU
      = ½ ∫_{(0,∞)} [ aW ∫_{(0,∞)} e^{-aUW} ∂_W g(U,W) dU ] dW.

The RHS inner bracket is exactly the `inner_limit`/`inner_bound` object `Φ_a(W)`. -/
theorem corner_Ioi_identity (g pdg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g)) (hpdgc : Continuous (Function.uncurry pdg))
    (hg : ∀ U W, HasDerivAt (fun W' => g U W') (pdg U W) W)
    (hpdgcs : HasCompactSupport (Function.uncurry pdg))
    (a B : ℝ) (hB : 0 < B)
    (hgsuppW : ∀ U W, B ≤ W → g U W = 0) (hpdgsuppW : ∀ U W, B ≤ W → pdg U W = 0) :
    a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W
      = (1 / 2) * ∫ W in Ioi (0:ℝ), a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W := by
  have hgU : ∀ U, Continuous (fun W => g U W) :=
    fun U => hgc.comp (continuous_const.prodMk continuous_id)
  have hpdgU : ∀ U, Continuous (fun W => pdg U W) :=
    fun U => hpdgc.comp (continuous_const.prodMk continuous_id)
  have hHU : ∀ U, Continuous (fun W => Hkern (a * U * W)) := fun U => by unfold Hkern; fun_prop
  -- per-U identity in Ioi form
  have perU : ∀ U, a * ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W
      = (a / 2) * ∫ W in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W := by
    intro U
    rw [← corner_interval_to_Ioi (fun W => Hkern (a * U * W) * g U W) B hB
          ((hHU U).mul (hgU U)) (fun W hW => by simp [hgsuppW U W hW]),
        ← corner_interval_to_Ioi (fun W => W * Real.exp (-(a * U * W)) * pdg U W) B hB
          (((continuous_id.mul (by fun_prop : Continuous fun W => Real.exp (-(a * U * W)))).mul
            (hpdgU U))) (fun W hW => by simp [hpdgsuppW U W hW])]
    exact corner_rectangle_ibp g pdg hgc hpdgc hg a U B (hgsuppW U B le_rfl)
  -- integrate over U
  have hstep2 : a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W
      = (a / 2) * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W := by
    rw [show a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W
          = ∫ U in Ioi (0:ℝ), a * ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W from
        (integral_const_mul a _).symm,
      show (a / 2) * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W
          = ∫ U in Ioi (0:ℝ), (a / 2) * ∫ W in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W from
        (integral_const_mul (a / 2) _).symm]
    exact setIntegral_congr_fun measurableSet_Ioi (fun U _ => perU U)
  rw [hstep2]
  -- Fubini (compact support)
  have hcontf : Continuous (Function.uncurry (fun U W => W * Real.exp (-(a * U * W)) * pdg U W)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => p.2 * Real.exp (-(a * p.1 * p.2))) := by fun_prop
    exact h1.mul hpdgc
  have hcsf : HasCompactSupport (Function.uncurry (fun U W => W * Real.exp (-(a * U * W)) * pdg U W)) :=
    hpdgcs.mul_left (f := fun p : ℝ × ℝ => p.2 * Real.exp (-(a * p.1 * p.2)))
  have hfub : ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W
      = ∫ W in Ioi (0:ℝ), ∫ U in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W :=
    integral_integral_swap_of_hasCompactSupport hcontf hcsf
  rw [hfub,
    show (a / 2) * ∫ W in Ioi (0:ℝ), ∫ U in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W
        = ∫ W in Ioi (0:ℝ), (a / 2) * ∫ U in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W from
      (integral_const_mul (a / 2) _).symm,
    show (1 / 2) * ∫ W in Ioi (0:ℝ), a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W
        = ∫ W in Ioi (0:ℝ), (1 / 2) * (a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W) from
      (integral_const_mul (1 / 2) _).symm]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro W _
  dsimp only
  have hpull : (∫ U in Ioi (0:ℝ), W * Real.exp (-(a * U * W)) * pdg U W)
      = W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro U _; ring
  rw [hpull]; ring

/-- **Step 4 — measurability of the outer integrand**, derived (not assumed): the joint
integrand is continuous, so `StronglyMeasurable.integral_prod_right'` gives measurability of
the parameter integral `W ↦ ∫_U e^{-aUW} ∂_W g(U,W) dU`, and multiplying by the continuous
`aW` keeps it (a.e.) strongly measurable. -/
theorem corner_integrand_aestronglyMeasurable (pdg : ℝ → ℝ → ℝ)
    (hpdgc : Continuous (Function.uncurry pdg)) (a : ℝ) :
    AEStronglyMeasurable
      (fun W => a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
      (volume.restrict (Ioi (0:ℝ))) := by
  have hf : Continuous (fun p : ℝ × ℝ => Real.exp (-(a * p.2 * p.1)) * pdg p.2 p.1) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.exp (-(a * p.2 * p.1)))).mul
      (hpdgc.comp continuous_swap)
  have hsm : StronglyMeasurable
      (fun W => ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W) :=
    hf.stronglyMeasurable.integral_prod_right'
  exact ((Continuous.stronglyMeasurable (by fun_prop : Continuous (fun W : ℝ => a * W))).mul
    hsm).aestronglyMeasurable

/-- **Step 5 — the corner-kernel gate (the full 2D analytic obstruction, closed).**

    a ∫_{(0,∞)} ∫_{(0,∞)} H(aUW) g(U,W) dW dU  →  -½ g(0,0)      (a → ∞),

for `g` with continuous `∂_W g = pdg`, compactly-supported `pdg`, `|pdg| ≤ M`, and the
`W`-support box `B`.  Assembled from `corner_Ioi_identity` (reduction), `inner_bound` +
`inner_limit` (the a.e. inner limit and its fixed dominator), `outer_dct` (outer dominated
convergence), and `boundary_ftc` (the FTC boundary evaluation giving the sign). -/
theorem corner_kernel_limit (g pdg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g)) (hpdgc : Continuous (Function.uncurry pdg))
    (hg : ∀ U W, HasDerivAt (fun W' => g U W') (pdg U W) W)
    (hpdgcs : HasCompactSupport (Function.uncurry pdg))
    (M B : ℝ) (hB : 0 < B) (hM : ∀ U W, |pdg U W| ≤ M)
    (hgsuppW : ∀ U W, B ≤ W → g U W = 0) (hpdgsuppW : ∀ U W, B ≤ W → pdg U W = 0) :
    Tendsto (fun a => a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * g U W)
      atTop (𝓝 (-(1 / 2) * g 0 0)) := by
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0 0)
  have hpdgUslice : ∀ W, Continuous (fun U => pdg U W) :=
    fun W => hpdgc.comp (continuous_id.prodMk continuous_const)
  have hpdg0slice : Continuous (fun W => pdg 0 W) :=
    hpdgc.comp (continuous_const.prodMk continuous_id)
  -- comm bridge  a*U*W = a*W*U  (to match inner_bound/inner_limit which use a*w*U)
  have hcomm : ∀ (a W : ℝ), (∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
      = ∫ U in Ioi (0:ℝ), Real.exp (-(a * W * U)) * pdg U W := by
    intro a W
    apply setIntegral_congr_fun measurableSet_Ioi
    intro U _; dsimp only; rw [mul_right_comm a U W]
  -- dominator
  have hD : IntegrableOn (fun W => (Ioc 0 B).indicator (fun _ => M) W) (Ioi (0:ℝ)) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hbound : ∀ᶠ a in atTop, ∀ᵐ W ∂(volume.restrict (Ioi (0:ℝ))),
      ‖a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W‖
        ≤ (Ioc 0 B).indicator (fun _ => M) W := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro W hW
    rw [mem_Ioi] at hW
    rw [Real.norm_eq_abs]
    by_cases hWB : W ≤ B
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hW, hWB⟩), hcomm a W]
      exact inner_bound (fun U => pdg U W) M (fun U => hM U W) a W ha hW
    · push_neg at hWB
      have hz : (∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W) = 0 := by
        have hzero : ∀ U ∈ Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W = 0 :=
          fun U _ => by rw [hpdgsuppW U W hWB.le, mul_zero]
        have heq : (∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
            = ∫ _U in Ioi (0:ℝ), (0:ℝ) := setIntegral_congr_fun measurableSet_Ioi hzero
        rw [heq, integral_zero]
      rw [hz, mul_zero, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => hM0) W
  have hlim : ∀ᵐ W ∂(volume.restrict (Ioi (0:ℝ))),
      Tendsto (fun a => a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
        atTop (𝓝 (pdg 0 W)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro W hW
    rw [mem_Ioi] at hW
    have he : (fun a => a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
        = fun a => a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * W * U)) * pdg U W := by
      funext a; rw [hcomm a W]
    rw [he]
    exact inner_limit (fun U => pdg U W) M (hpdgUslice W) (fun U => hM U W) W hW
  have hdct := outer_dct
    (fun a W => a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
    (fun W => pdg 0 W) (fun W => (Ioc 0 B).indicator (fun _ => M) W)
    (fun a => corner_integrand_aestronglyMeasurable pdg hpdgc a) hD hbound hlim
  -- boundary FTC
  have hbdry : ∫ W in Ioi (0:ℝ), pdg 0 W = - g 0 0 :=
    boundary_ftc (fun W => g 0 W) (fun W => pdg 0 W) B (fun W => hg 0 W)
      (corner_slice_integrable (fun W => pdg 0 W) B hB hpdg0slice
        (fun W hW => hpdgsuppW 0 W hW)) (fun W hW => hgsuppW 0 W hW)
  -- assemble
  have hfinal : Tendsto
      (fun a => (1 / 2) * ∫ W in Ioi (0:ℝ),
        a * W * ∫ U in Ioi (0:ℝ), Real.exp (-(a * U * W)) * pdg U W)
      atTop (𝓝 (-(1 / 2) * g 0 0)) := by
    have h2 := hdct.const_mul (1 / 2)
    rw [hbdry] at h2
    convert h2 using 2
    ring
  refine hfinal.congr' ?_
  filter_upwards with a
  exact (corner_Ioi_identity g pdg hgc hpdgc hg hpdgcs a B hB hgsuppW hpdgsuppW).symm

#print axioms corner_integrand_aestronglyMeasurable
#print axioms corner_kernel_limit

#print axioms corner_Ioi_identity

#print axioms corner_slice_integrable
#print axioms corner_interval_to_Ioi

#print axioms corner_kernel_deriv
#print axioms corner_kernel_identity
#print axioms concentration_limit
#print axioms scaling_change_of_var
#print axioms inner_limit
#print axioms boundary_ftc
#print axioms boundary_ftc_half
#print axioms inner_bound
#print axioms outer_dct
#print axioms corner_rectangle_ibp

end UnifiedTheory.Audit.KFCausalMinkowskiCorner
