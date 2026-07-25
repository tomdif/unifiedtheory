/-
  Audit/KFCausalMinkowskiCorner.lean   (Volume sector → the corner-kernel gate, cores)

  The full 2D causal-set continuum theorem reduces (per review) to ONE corner-kernel limit,
  avoiding rapidity coordinates and doing the cancellation before domination:

      a ∫_0^∞ ∫_0^∞ H(aUW) g(U,W) dU dW  →  -½ g(0,0)      (a = ρc₀ → ∞,  g = ∂_U∂_W φ).

  The route (do NOT apply DCT to `a H(aUW)` directly -- its mass is not uniformly bounded
  in the boost direction) uses the kernel identity `H(aUW) = -½ ∂_W(W e^{-aUW})`, IBP in
  `W` first, and then the INNER concentration limit with a FIXED, mass-one kernel:

      aw ∫_0^∞ e^{-aUw} h(U) dU  →  h(0)      (w > 0 fixed),     since  aw ∫_0^∞ e^{-aUw} dU = 1.

  This file closes the two analytic CORES of that gate, both axiom-clean:

    * `corner_kernel_deriv` / `corner_kernel_identity` :  `H(aUW) = -½ ∂_W(W e^{-aUW})`.
    * `concentration_limit` :  `∫_0^∞ e^{-t} h(t/λ) dt → h(0)` as `λ → ∞`, for continuous
      bounded `h` -- the substituted form of the inner limit, with the fixed dominator
      `M e^{-t}` (integrable) and `∫_0^∞ e^{-t} = 1`.

  The full corner-kernel lemma additionally needs the change of variables `U = t/(aw)`
  linking the two forms, Fubini, the `W`-IBP under the `U`-integral, the outer DCT over the
  finite `w`-support, and the boundary/counterterm assembly.  Those are the remaining gate;
  the analytic hearts are closed here.

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
    (hbound : ∀ a, ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))), ‖Φ a w‖ ≤ D w)
    (hlim : ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))), Tendsto (fun a => Φ a w) atTop (𝓝 (P w))) :
    Tendsto (fun a => ∫ w in Ioi (0:ℝ), Φ a w) atTop (𝓝 (∫ w in Ioi (0:ℝ), P w)) :=
  tendsto_integral_filter_of_dominated_convergence D
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hD hlim

#print axioms corner_kernel_deriv
#print axioms corner_kernel_identity
#print axioms concentration_limit
#print axioms scaling_change_of_var
#print axioms inner_limit
#print axioms boundary_ftc
#print axioms boundary_ftc_half
#print axioms inner_bound
#print axioms outer_dct

end UnifiedTheory.Audit.KFCausalMinkowskiCorner
