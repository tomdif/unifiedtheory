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

#print axioms corner_kernel_deriv
#print axioms corner_kernel_identity
#print axioms concentration_limit

end UnifiedTheory.Audit.KFCausalMinkowskiCorner
