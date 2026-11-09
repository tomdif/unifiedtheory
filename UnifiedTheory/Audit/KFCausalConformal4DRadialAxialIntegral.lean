/- The axial disk-section formula equals the radial/angular formula by
one-dimensional substitution and integration by parts, including radius zero. -/
import UnifiedTheory.Audit.KFCausalConformal4DBallAxialIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialAxialIntegral
noncomputable section
open MeasureTheory Real Set
open KFCausalConformal4DBallAxialIntegral

theorem symmetric_interval (R : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in (-R)..R, f z) = ∫ z in (0:ℝ)..R, f z+f (-z) := by
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    ((show Continuous (fun z : ℝ => f (-z)) from hf.comp continuous_neg).intervalIntegrable _ _),
    intervalIntegral.integral_comp_neg]
  simpa only [neg_zero,add_comm] using
    (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-R) 0) (hf.intervalIntegrable 0 R)).symm

theorem axial_radial_identity (R : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in (-R)..R, (R^2-z^2)*f z) =
      2 * ∫ b in (0:ℝ)..R, b^2 * ∫ mu in (-1:ℝ)..1, f (b*mu) := by
  let F : ℝ → ℝ := fun x => ∫ z in (0:ℝ)..x, f z
  let H : ℝ → ℝ := fun x => F x-F (-x)
  have hF (x : ℝ) : HasDerivAt F (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hH (x : ℝ) : HasDerivAt H (f x+f (-x)) x := by
    simpa only [mul_neg_one,sub_neg_eq_add] using (hF x).sub ((hF (-x)).comp x (hasDerivAt_neg x))
  have hHc : Continuous H := continuous_iff_continuousAt.2 (fun x => (hH x).continuousAt)
  have he (x : ℝ) : H x=∫ z in (-x)..x, f z :=
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hscale (b : ℝ) : b*(∫ mu in (-1:ℝ)..1, f (b*mu))=H b := by
    rw [he]
    simpa only [smul_eq_mul,mul_neg_one,mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (-1:ℝ)) (b := 1) f b)
  have hp (x : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    norm_num
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x^2) (v := H) (u' := fun x => 2*x)
    (v' := fun x => f x+f (-x)) (a := 0) (b := R)
    (by fun_prop) hHc.continuousOn (fun x _ => hp x) (fun x _ => hH x)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hsecond : (∫ z in (-R)..R, z^2*f z) =
      ∫ b in (0:ℝ)..R, b^2*(f b+f (-b)) := by
    rw [symmetric_interval R _ (by fun_prop)]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  have hparts : (∫ z in (-R)..R, (R^2-z^2)*f z) =
      R^2*H R-(∫ b in (0:ℝ)..R, b^2*(f b+f (-b))) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      ((show Continuous (fun z : ℝ => R^2*f z) from continuous_const.mul hf).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun z : ℝ => z^2*f z)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,← he R,hsecond]
  rw [hparts]
  have hs : (∫ b in (0:ℝ)..R, 2*b*H b) =
      2*(∫ b in (0:ℝ)..R, b^2*(∫ mu in (-1:ℝ)..1, f (b*mu))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro b _
    dsimp only
    rw [← hscale b]
    ring
  simp only [zero_pow (by norm_num : 2≠0),zero_mul,sub_zero] at hibp
  linarith

theorem ball_radial_integral (R : ℝ) (hR : 0<R) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v in spatialBall R, f (v 0)) =
      2*π * ∫ b in (0:ℝ)..R, b^2 * ∫ mu in (-1:ℝ)..1, f (b*mu) := by
  rw [ball_axial_integral R hR f hf,axial_radial_identity R f hf]
  ring

#print axioms symmetric_interval
#print axioms axial_radial_identity
#print axioms ball_radial_integral
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialAxialIntegral
