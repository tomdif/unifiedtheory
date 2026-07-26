/-
  Audit/KFCausalMinkowski4DConcentration.lean   (Volume sector → 4D edge concentration)

  Rung 4a of the 4D ladder: the J4-EDGE CONCENTRATION LIMIT — the analytic heart of
  the 4D gate's edge mechanism, machine-checked.

  After the scaling substitution `w = √a·u·v`, the J4-edge contribution of the 4D
  gate reduces (per axis, per `u`-slice) to the 1D limit proved here:

      ∫₀^∞ J4(w²) · (q(w/l) − q(0))/(w/l) dw  →  (−√π/24)·q'(0)      (l → ∞),

  the exact analogue of the 2D `concentration_limit`, with the just-proved edge mass
  `∫₀^∞ J4(w²)dw = −√π/24` (`J4_edge_mass`) as the limiting value and the FIXED
  dominator `|J4(w²)|·M` (Gaussian moments — no moving support).  The subtracted form
  is the honest one: the unsubtracted edge term equals it exactly because the leading
  mass vanishes (`J4_moment_neg_one`, `M[J4](0) = 0`).

  With this, the 4D gate's edge mechanism — (i) leading mass zero, (ii) slope
  concentration onto `∂g` at the axis with constant `−√π/24`, (iii) boundary-FTC to
  the corner — has all analytic ingredients Lean-closed; what remains of the full
  gate is the outer integration/DCT assembly of these slices and the K4-corner
  (boost coordinates + Frullani).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DGate

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DGate

namespace UnifiedTheory.Audit.KFCausalMinkowski4DConcentration

/-- `w ↦ J4(w²)` is integrable on `(0,∞)` (Gaussian moments `w²e^{−w²}`, `w⁴e^{−w²}`). -/
theorem J4_sq_integrable : IntegrableOn (fun w => J4 (w^2)) (Ioi (0:ℝ)) := by
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (2:ℝ))).integrableOn
  have h4 : IntegrableOn (fun x : ℝ => x ^ (4:ℝ) * Real.exp (-(1:ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1:ℝ) < (4:ℝ))).integrableOn
  refine IntegrableOn.congr_fun
    ((h2.const_mul (1/3)).sub (h4.const_mul (1/3))) ?_ measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  simp only [Pi.sub_apply]
  rw [show w ^ (2:ℝ) = w ^ (2:ℕ) from by rw [← Real.rpow_natCast w 2]; norm_num,
    show w ^ (4:ℝ) = w ^ (4:ℕ) from by rw [← Real.rpow_natCast w 4]; norm_num]
  unfold J4
  simp only [neg_one_mul]
  ring

/-- **The J4-edge concentration limit.**  For differentiable `q` with `|q'| ≤ M`,

    ∫₀^∞ J4(w²)·(q(w/l) − q(0))/(w/l) dw  →  (−√π/24)·q'(0)      (l → ∞).

The slope quotient concentrates onto `q'(0)` with the FIXED dominator `|J4(w²)|·M`
(mean-value bound — no moving support), and the limiting value is the proved edge
mass `∫J4(w²)dw = −√π/24`.  This is the per-slice mechanism of the 4D gate's
`−(√π/24)∫∂g`-edge terms. -/
theorem J4_edge_concentration (q q' : ℝ → ℝ) (M : ℝ)
    (hq : ∀ x, HasDerivAt q (q' x) x) (hM : ∀ x, |q' x| ≤ M) :
    Tendsto (fun l : ℝ => ∫ w in Ioi (0:ℝ), J4 (w^2) * ((q (w/l) - q 0) / (w/l)))
      atTop (𝓝 (-(Real.sqrt π)/24 * q' 0)) := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hq x).continuousAt
  have hslope_bound : ∀ y : ℝ, |q y - q 0| ≤ M * |y| := by
    intro y
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := q) (f' := q') (fun x _ => (hq x).hasDerivWithinAt)
      (fun x _ => by simpa [Real.norm_eq_abs] using hM x) (mem_univ 0) (mem_univ y)
    simpa [Real.norm_eq_abs] using h
  have hJc : Continuous (fun w : ℝ => J4 (w^2)) := by unfold J4; fun_prop
  have hdct : Tendsto (fun l : ℝ => ∫ w in Ioi (0:ℝ), J4 (w^2) * ((q (w/l) - q 0) / (w/l)))
      atTop (𝓝 (∫ w in Ioi (0:ℝ), J4 (w^2) * q' 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun w => |J4 (w^2)| * M)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
      have hnum : Measurable (fun w : ℝ => q (w/l) - q 0) :=
        ((hqc.comp (continuous_id.div_const l)).sub continuous_const).measurable
      have hden : Measurable (fun w : ℝ => w/l) := (continuous_id.div_const l).measurable
      exact (hJc.measurable.mul (hnum.div hden)).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      have hwl : 0 < w / l := div_pos hw hl
      rw [Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hwl.ne')]
      exact hslope_bound (w/l)
    · exact J4_sq_integrable.abs.mul_const M
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      have hslope := hasDerivAt_iff_tendsto_slope.mp (hq 0)
      have harg : Tendsto (fun l : ℝ => w / l) atTop (𝓝[≠] (0:ℝ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul w
        · filter_upwards [eventually_gt_atTop (0:ℝ)] with l hl
          exact (div_pos hw hl).ne'
      have hcomp := (hslope.comp harg).const_mul (J4 (w^2))
      apply hcomp.congr
      intro l
      rw [Function.comp_apply, slope_def_field]
      rw [sub_zero]
  have hval : ∫ w in Ioi (0:ℝ), J4 (w^2) * q' 0 = -(Real.sqrt π)/24 * q' 0 := by
    rw [show (fun w => J4 (w^2) * q' 0) = fun w => q' 0 * J4 (w^2) from by funext w; ring,
      integral_const_mul, J4_edge_mass]
    ring
  rwa [hval] at hdct

#print axioms J4_sq_integrable
#print axioms J4_edge_concentration

end UnifiedTheory.Audit.KFCausalMinkowski4DConcentration
