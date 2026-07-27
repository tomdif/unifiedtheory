/-
  Audit/KFCausalMinkowski4DEdgeAssembly.lean   (Volume sector → the J4-edge theorem)

  Rung 4b of the 4D ladder: THE J4-EDGE SLICE THEOREM — the analytic content of the
  first of the three bounded lemmas, closed per slice:

      √a ∫₀^∞ (u/v)·J4(a u²v²)·g(u,v) dv  ⟶  (−√π/24)·∂_vg(u,0)     (a → ∞, u > 0),

  for `C¹`-in-`v` fields `g` with `|∂_v g| ≤ M`.  (The `(v/u)`-edge is the mirror
  statement under `u ↔ v`.)

  WHAT IS PROVED (all machine-checked):
   • `J4_over_w_integrable`, `J4_edge_mass_zero` — `∫₀^∞ w⁻¹J4(w²)dw = 0`
     (`M[J4](0) = 0` in the substituted variable).
   • `J4_slice_identity` — the exact per-`u` substitution `w = √a·u·v` PLUS the
     zero-mass subtraction: the slice equals the SUBTRACTED slope form exactly,
     for every `a, u > 0`.
   • `J4_slice_limit` — the slice tends to `(−√π/24)·∂_vg(u,0)` per `u > 0`
     (`J4_edge_concentration` composed with `l = √a·u → ∞`).

  REMAINING for the full edge limit: the outer `u`-DCT over the support box (the
  `outer_dct` pattern of the closed 2D corner gate, with the `a`-independent slice
  dominator `M·∫|J4(w²)|`); then the K4-corner (boost coordinates + Frullani) and
  the spherical-mean `r²`-expansion complete the three bounded lemmas.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DConcentration

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DEdge
open UnifiedTheory.Audit.KFCausalMinkowski4DGate
open UnifiedTheory.Audit.KFCausalMinkowski4DConcentration
open UnifiedTheory.Audit.KFCausalMinkowskiCorner

namespace UnifiedTheory.Audit.KFCausalMinkowski4DEdgeAssembly

/-- `w ↦ w⁻¹·J4(w²)` is integrable on `(0,∞)` (Gaussian moments `w e^{−w²}`, `w³e^{−w²}`). -/
theorem J4_over_w_integrable : IntegrableOn (fun w => w⁻¹ * J4 (w^2)) (Ioi (0:ℝ)) := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (1:ℝ))).integrableOn
  have h3 : IntegrableOn (fun x : ℝ => x ^ (3:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (3:ℝ))).integrableOn
  refine IntegrableOn.congr_fun
    ((h1.const_mul (1/3)).sub (h3.const_mul (1/3))) ?_ measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  simp only [Pi.sub_apply]
  rw [show w ^ (1:ℝ) = w from Real.rpow_one w,
    show w ^ (3:ℝ) = w ^ (3:ℕ) from by rw [← Real.rpow_natCast w 3]; norm_num]
  unfold J4
  simp only [neg_one_mul]
  have hne : w ≠ 0 := hw.ne'
  field_simp
  try ring

/-- **The `J4` edge mass at order zero vanishes**: `∫₀^∞ w⁻¹ J4(w²) dw = 0`
(the `M[J4](0) = 0` zero, in the substituted variable). -/
theorem J4_edge_mass_zero : ∫ w in Ioi (0:ℝ), w⁻¹ * J4 (w^2) = 0 := by
  have hsub := integral_comp_rpow_Ioi (fun ξ => ξ⁻¹ * J4 ξ) (p := 2) (by norm_num)
  rw [J4_moment_neg_one] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => ξ⁻¹ * J4 ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * (x⁻¹ * J4 (x^2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    rw [show x ^ ((2:ℝ) - 1) = x from by
        rw [show (2:ℝ) - 1 = 1 from by norm_num, Real.rpow_one],
      show x ^ (2:ℝ) = x ^ (2:ℕ) from by rw [← Real.rpow_natCast x 2]; norm_num,
      show |(2:ℝ)| = 2 from abs_of_pos (by norm_num)]
    have hne : x ≠ 0 := hx.ne'
    field_simp
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

/-- **The slice identity**: for `a, u > 0`, the `u`-slice of the J4-edge integral
equals the subtracted slope form EXACTLY (substitution `w = √a·u·v` + the zero mass):

    √a ∫₀^∞ (u/v)·J4(au²v²)·g(u,v) dv
      = ∫₀^∞ J4(w²)·(g(u, w/(√a·u)) − g(u,0))/(w/(√a·u)) dw. -/
theorem J4_slice_identity (g pdvg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g))
    (hd : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (M : ℝ) (hM : ∀ u v, |pdvg u v| ≤ M)
    (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    Real.sqrt a * ∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v
      = ∫ w in Ioi (0:ℝ),
          J4 (w^2) * ((g u (w/(Real.sqrt a * u)) - g u 0) / (w/(Real.sqrt a * u))) := by
  set c := Real.sqrt a * u with hcdef
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr ha) hu
  have hc2 : c^2 = a * u^2 := by
    rw [hcdef, mul_pow, Real.sq_sqrt ha.le]
  have hgu : Continuous (fun v => g u v) :=
    hgc.comp (continuous_const.prodMk continuous_id)
  -- substitution w = c·v
  have hcomp := integral_comp_mul_left_Ioi
    (fun w => w⁻¹ * J4 (w^2) * g u (w/c)) 0 hc
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcancel : (∫ x in Ioi (0:ℝ), (fun w => w⁻¹ * J4 (w^2) * g u (w/c)) (c * x))
      = ∫ x in Ioi (0:ℝ), (c*x)⁻¹ * J4 (a*u^2*x^2) * g u x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    show (c*x)⁻¹ * J4 ((c*x)^2) * g u ((c*x)/c) = (c*x)⁻¹ * J4 (a*u^2*x^2) * g u x
    rw [mul_div_cancel_left₀ x hc.ne', mul_pow, hc2]
    try ring_nf
  rw [hcancel] at hcomp
  -- relate the (u/v) form to the (c·v)⁻¹ form
  have hrel : (∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v)
      = (u*c) * ∫ v in Ioi (0:ℝ), (c*v)⁻¹ * J4 (a*u^2*v^2) * g u v := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    rw [mem_Ioi] at hv
    dsimp only
    rw [mul_inv]
    field_simp
    try ring
  -- combine: √a · LHS = c · ∫ w⁻¹ J4(w²) g(u, w/c)
  have hmain : Real.sqrt a * ∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v
      = c * ∫ w in Ioi (0:ℝ), w⁻¹ * J4 (w^2) * g u (w/c) := by
    rw [hrel, hcomp]
    rw [hcdef]
    field_simp
    try ring
  rw [hmain]
  -- subtraction: c ∫ w⁻¹J4 g = ∫ J4·slope + (c·g(u,0))·∫w⁻¹J4 = ∫ J4·slope + 0
  have hslope_bound : ∀ y : ℝ, |g u y - g u 0| ≤ M * |y| := by
    intro y
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v' => g u v') (f' := fun v' => pdvg u v')
      (fun x _ => (hd u x).hasDerivWithinAt)
      (fun x _ => by simpa [Real.norm_eq_abs] using hM u x) (mem_univ 0) (mem_univ y)
    simpa [Real.norm_eq_abs] using h
  have iA : IntegrableOn
      (fun w => J4 (w^2) * ((g u (w/c) - g u 0) / (w/c))) (Ioi (0:ℝ)) := by
    have hsm : AEStronglyMeasurable (fun w => (g u (w/c) - g u 0) / (w/c))
        (volume.restrict (Ioi (0:ℝ))) := by
      have hnum : Measurable (fun w : ℝ => g u (w/c) - g u 0) :=
        ((hgu.comp (continuous_id.div_const c)).sub continuous_const).measurable
      exact (hnum.div (continuous_id.div_const c).measurable).aestronglyMeasurable
    have hbd : ∀ᵐ w ∂(volume.restrict (Ioi (0:ℝ))),
        ‖(g u (w/c) - g u 0) / (w/c)‖ ≤ M := by
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      have hwc : 0 < w / c := div_pos hw hc
      rw [Real.norm_eq_abs, abs_div, div_le_iff₀ (abs_pos.mpr hwc.ne')]
      exact hslope_bound (w/c)
    have := J4_sq_integrable.bdd_mul hsm hbd
    exact this.congr (ae_of_all _ fun w => mul_comm _ _)
  have iB : IntegrableOn (fun w => (c * g u 0) * (w⁻¹ * J4 (w^2))) (Ioi (0:ℝ)) :=
    J4_over_w_integrable.const_mul (c * g u 0)
  have hsplit : (∫ w in Ioi (0:ℝ), c * (w⁻¹ * J4 (w^2) * g u (w/c)))
      = (∫ w in Ioi (0:ℝ), J4 (w^2) * ((g u (w/c) - g u 0) / (w/c)))
        + ∫ w in Ioi (0:ℝ), (c * g u 0) * (w⁻¹ * J4 (w^2)) := by
    rw [← integral_add iA iB]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    rw [mem_Ioi] at hw
    dsimp only
    have hwne : w ≠ 0 := hw.ne'
    field_simp
    ring
  rw [← integral_const_mul] at hmain ⊢
  rw [show (∫ w in Ioi (0:ℝ), c * (w⁻¹ * J4 (w^2) * g u (w/c)))
      = (∫ w in Ioi (0:ℝ), J4 (w^2) * ((g u (w/c) - g u 0) / (w/c)))
        + ∫ w in Ioi (0:ℝ), (c * g u 0) * (w⁻¹ * J4 (w^2)) from hsplit,
    integral_const_mul, J4_edge_mass_zero, mul_zero, add_zero]

/-- **The slice limit**: for fixed `u > 0`,
`√a ∫₀^∞ (u/v)J4(au²v²)g(u,v)dv → (−√π/24)·∂_vg(u,0)` as `a → ∞`. -/
theorem J4_slice_limit (g pdvg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g))
    (hd : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (M : ℝ) (hM : ∀ u v, |pdvg u v| ≤ M)
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun a : ℝ => Real.sqrt a * ∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v)
      atTop (𝓝 (-(Real.sqrt π)/24 * pdvg u 0)) := by
  have hl : Tendsto (fun a : ℝ => Real.sqrt a * u) atTop atTop :=
    Real.tendsto_sqrt_atTop.atTop_mul_const hu
  have hconc := (J4_edge_concentration (fun v => g u v) (fun v => pdvg u v) M
    (hd u) (hM u)).comp hl
  apply hconc.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  exact (J4_slice_identity g pdvg hgc hd M hM a u ha hu).symm

#print axioms J4_over_w_integrable
/-- **The J4-edge outer theorem**: integrating the slice limit over `u`,

    ∫₀^∞ [√a ∫₀^∞ (u/v)·J4(au²v²)·g(u,v) dv] du
        ⟶  (−√π/24) · ∫₀^∞ ∂_v g(u,0) du       (a → ∞).

Dominated convergence over `u` (`outer_dct`): the slice identity plus the MVT
bound the slice uniformly in `a` by `M·∫|J4(w²)|dw` on the support `(0,A]`;
the pointwise limit is `J4_slice_limit`. -/
theorem J4_edge_outer (g pdvg : ℝ → ℝ → ℝ)
    (hgc : Continuous (Function.uncurry g))
    (hd : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (M : ℝ) (hM : ∀ u v, |pdvg u v| ≤ M)
    (A : ℝ) (hA : 0 < A) (hsuppU : ∀ u v, A ≤ u → g u v = 0) :
    Tendsto (fun a : ℝ => ∫ u in Ioi (0:ℝ),
        Real.sqrt a * ∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v)
      atTop (𝓝 (-(Real.sqrt π)/24 * ∫ u in Ioi (0:ℝ), pdvg u 0)) := by
  set CJ := ∫ w in Ioi (0:ℝ), |J4 (w^2)| with hCJdef
  have hCJ0 : 0 ≤ CJ :=
    setIntegral_nonneg measurableSet_Ioi (fun w _ => abs_nonneg _)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 0)
  have hJ4c : Continuous J4 := by
    unfold J4
    fun_prop
  have h := outer_dct
    (fun a u => Real.sqrt a * ∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v)
    (fun u => -(Real.sqrt π)/24 * pdvg u 0)
    ((Ioc (0:ℝ) A).indicator (fun _ => M * CJ))
    ?_ ?_ ?_ ?_
  · have hval : (∫ u in Ioi (0:ℝ), -(Real.sqrt π)/24 * pdvg u 0)
        = -(Real.sqrt π)/24 * ∫ u in Ioi (0:ℝ), pdvg u 0 := integral_const_mul _ _
    rwa [hval] at h
  · -- measurability of the outer family
    intro a
    have hFm : Measurable (Function.uncurry (fun u v =>
        (u/v) * J4 (a*u^2*v^2) * g u v)) := by
      have hquad : Measurable (fun p : ℝ × ℝ => a * p.1^2 * p.2^2) :=
        ((measurable_fst.pow_const 2).const_mul a).mul (measurable_snd.pow_const 2)
      exact ((measurable_fst.div measurable_snd).mul
        (hJ4c.measurable.comp hquad)).mul hgc.measurable
    have hmarg : StronglyMeasurable (fun u => ∫ v in Ioi (0:ℝ),
        (u/v) * J4 (a*u^2*v^2) * g u v) :=
      hFm.stronglyMeasurable.integral_prod_right'
    exact (measurable_const.mul hmarg.measurable).aestronglyMeasurable
  · -- the dominator is integrable
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  · -- the uniform bound
    filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    rcases lt_or_ge u A with huA | huA
    · rw [Set.indicator_of_mem (mem_Ioc.mpr ⟨hu, le_of_lt huA⟩)]
      rw [Real.norm_eq_abs, J4_slice_identity g pdvg hgc hd M hM a u ha hu]
      have hlip : ∀ y : ℝ, 0 ≤ y → |g u y - g u 0| ≤ M * y := by
        intro y hy
        have hmvt := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun z _ => (hd u z).hasDerivWithinAt)
          (fun z _ => by simpa [Real.norm_eq_abs] using hM u z)
          (mem_univ 0) (mem_univ y)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hy] at hmvt
        exact hmvt
      calc |∫ w in Ioi (0:ℝ),
            J4 (w^2) * ((g u (w/(Real.sqrt a * u)) - g u 0)/(w/(Real.sqrt a * u)))|
          ≤ ∫ w in Ioi (0:ℝ), |J4 (w^2)| * M := by
            rw [← Real.norm_eq_abs]
            apply norm_integral_le_of_norm_le (J4_sq_integrable.abs.mul_const M)
            apply ae_restrict_of_forall_mem measurableSet_Ioi
            intro w hw
            rw [mem_Ioi] at hw
            have hy : 0 < w/(Real.sqrt a * u) :=
              div_pos hw (mul_pos (Real.sqrt_pos.mpr ha) hu)
            rw [Real.norm_eq_abs, abs_mul]
            apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [abs_div, abs_of_pos hy, div_le_iff₀ hy]
            exact hlip _ (le_of_lt hy)
        _ = M * CJ := by
            rw [show (fun w => |J4 (w^2)| * M) = fun w => M * |J4 (w^2)| from by
              funext w; ring]
            rw [integral_const_mul, ← hCJdef]
    · have hz : (∫ v in Ioi (0:ℝ), (u/v) * J4 (a*u^2*v^2) * g u v) = 0 := by
        rw [setIntegral_congr_fun measurableSet_Ioi
          (fun v _ => by rw [hsuppU u v huA, mul_zero]), integral_zero]
      rw [hz, mul_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hM0 hCJ0) u
  · -- the pointwise limit
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    exact J4_slice_limit g pdvg hgc hd M hM u hu

#print axioms J4_edge_mass_zero
#print axioms J4_slice_identity
#print axioms J4_slice_limit

#print axioms J4_edge_outer

end UnifiedTheory.Audit.KFCausalMinkowski4DEdgeAssembly
