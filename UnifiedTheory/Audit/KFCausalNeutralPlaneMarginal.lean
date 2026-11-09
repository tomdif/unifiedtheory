/- Exact integration of the three Gaussian spectator coordinates. This
identifies the two-dimensional density used by the degree-independent
pointwise estimate with the centered original transverse integral. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure
open UnifiedTheory.Audit.KFCausalQuarticPlaneDomination

def prefactor (α : ℝ) (r : ℂ) : ℝ :=
  (1/(4*|r.im|)) * (Real.sqrt (Real.pi/(2*α*(r.re^2-r.im^2))))^2 *
    Real.sqrt (Real.pi/(α*(r.re^2-r.im^2)))

theorem integral_head_product (n : ℕ) (f : ℝ → ℝ) (g : (Fin n → ℝ) → ℝ) :
    (∫ u : Fin (n+1) → ℝ, f (u 0)*g (fun i => u i.succ)) =
      (∫ x, f x)*(∫ v, g v) := by
  rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm).integral_comp']
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.cons_succ,Fin.zero_succAbove,
    cast_eq,Fin.cons_zero] using (integral_prod_mul f g)

theorem density_factorization (α β : ℝ) (r : ℂ) (P : Polynomial ℂ) (u : Transverse) :
    Real.exp (-quadratic α β r u)*potential (u 3+fieldSlope r*u 4)*
      ‖P.eval ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2 =
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
      (Real.exp (-(2*α*(r.re^2-r.im^2))*(u 1)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(u 2)^2) *
        density 1 β (planeWidth α β r) (fieldSlope r) P (u 3) (u 4))) := by
  unfold density
  simp only [one_mul,← mul_assoc,← Real.exp_add]
  congr 2
  unfold quadratic
  ring

theorem spectator_integral (α β : ℝ) (r : ℂ) (P : Polynomial ℂ) :
    (∫ u : Transverse, Real.exp (-quadratic α β r u)*
      potential (u 3+fieldSlope r*u 4)*‖P.eval ((u 3:ℂ)+(u 4:ℂ)*Complex.I)‖^2) =
    (Real.sqrt (Real.pi/(2*α*(r.re^2-r.im^2))))^2 *
      Real.sqrt (Real.pi/(α*(r.re^2-r.im^2))) *
      ∫ v : Fin 2 → ℝ, density 1 β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1) := by
  simp_rw [density_factorization]
  change (∫ u : Fin (4+1) → ℝ,
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 4 → ℝ =>
      Real.exp (-(2*α*(r.re^2-r.im^2))*(v 0)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(v 1)^2) *
        density 1 β (planeWidth α β r) (fieldSlope r) P (v 2) (v 3)))
      (fun i => u i.succ)) = _
  rw [integral_head_product 4 (fun x => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2))
    (fun v => Real.exp (-(2*α*(r.re^2-r.im^2))*(v 0)^2) *
      (Real.exp (-(α*(r.re^2-r.im^2))*(v 1)^2) *
        density 1 β (planeWidth α β r) (fieldSlope r) P (v 2) (v 3))),
    integral_gaussian]
  change _ * (∫ u : Fin (3+1) → ℝ,
    Real.exp (-(2*α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 3 → ℝ =>
      Real.exp (-(α*(r.re^2-r.im^2))*(v 0)^2) *
        density 1 β (planeWidth α β r) (fieldSlope r) P (v 1) (v 2))
      (fun i => u i.succ)) = _
  rw [integral_head_product 3 (fun x => Real.exp (-(2*α*(r.re^2-r.im^2))*x^2))
    (fun v => Real.exp (-(α*(r.re^2-r.im^2))*(v 0)^2) *
        density 1 β (planeWidth α β r) (fieldSlope r) P (v 1) (v 2)),
    integral_gaussian]
  change _ * (_ * (∫ u : Fin (2+1) → ℝ,
    Real.exp (-(α*(r.re^2-r.im^2))*(u 0)^2) *
    (fun v : Fin 2 → ℝ =>
        density 1 β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1))
      (fun i => u i.succ))) = _
  rw [integral_head_product 2 (fun x => Real.exp (-(α*(r.re^2-r.im^2))*x^2))
    (fun v => density 1 β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1)),
    integral_gaussian]
  ring

theorem centeredEnergy_plane_integral (α β : ℝ) (r : ℂ) (hr : r.im ≠ 0)
    (P : Polynomial ℂ) :
    (∫ q, centeredEnergyDensity α β r P q) =
      ∫ v : Fin 2 → ℝ,
        density (prefactor α r) β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1) := by
  rw [centeredEnergy_change_variables α β r hr,spectator_integral]
  have he : (fun v : Fin 2 → ℝ =>
      density (prefactor α r) β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1)) =
    fun v => prefactor α r * density 1 β (planeWidth α β r) (fieldSlope r) P (v 0) (v 1) := by
    funext v
    unfold density
    ring
  rw [he,integral_const_mul]
  unfold prefactor
  ring

theorem prefactor_positive (α : ℝ) (r : ℂ) (hα : 0 < α)
    (hA : 0 < r.re^2-r.im^2) (hr : r.im ≠ 0) : 0 < prefactor α r := by
  unfold prefactor
  positivity

#print axioms integral_head_product
#print axioms density_factorization
#print axioms spectator_integral
#print axioms centeredEnergy_plane_integral
#print axioms prefactor_positive
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
