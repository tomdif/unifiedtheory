/- Exact charged-coordinate changes of variables, retaining the positive
Y half-line. The Jacobian gives the derivative of the complete integral
without any assertion that a boundary flux vanishes. Identifying this with
the integral of a pointwise dilation jet requires a separate interchange. -/
import UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalJointFourierDilationMeasure
noncomputable section
open MeasureTheory Filter
open scoped Topology

def integral (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ x : ℝ, F Y u v x

def scaled (F : ℝ → ℝ → ℝ → ℝ → ℝ) (A B : ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun Y u v x => F (B*Y) (A*u) (A*v) x

theorem integral_scaled (F : ℝ → ℝ → ℝ → ℝ → ℝ) (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) :
    integral (scaled F A B) = A⁻¹^2*B⁻¹*integral F := by
  unfold integral scaled
  have hv (Y u : ℝ) : (∫ v : ℝ, ∫ x : ℝ, F (B*Y) (A*u) (A*v) x) =
      A⁻¹*(∫ v : ℝ, ∫ x : ℝ, F (B*Y) (A*u) v x) := by
    simpa only [smul_eq_mul,abs_of_pos (inv_pos.mpr hA)] using
      Measure.integral_comp_mul_left (fun v => ∫ x : ℝ, F (B*Y) (A*u) v x) A
  have hu (Y : ℝ) : (∫ u : ℝ, A⁻¹*(∫ v : ℝ, ∫ x : ℝ, F (B*Y) (A*u) v x)) =
      A⁻¹*(A⁻¹*(∫ u : ℝ, ∫ v : ℝ, ∫ x : ℝ, F (B*Y) u v x)) := by
    rw [integral_const_mul]
    congr 1
    simpa only [smul_eq_mul,abs_of_pos (inv_pos.mpr hA)] using
      Measure.integral_comp_mul_left (fun u => ∫ v : ℝ, ∫ x : ℝ, F (B*Y) u v x) A
  simp_rw [hv,hu]
  rw [integral_const_mul,integral_const_mul,
    integral_comp_mul_left_Ioi (fun Y => ∫ u : ℝ, ∫ v : ℝ, ∫ x : ℝ, F Y u v x) 0 hB]
  simp only [mul_zero,smul_eq_mul]
  ring

theorem exponential_scaling (F : ℝ → ℝ → ℝ → ℝ → ℝ) (ell t : ℝ) :
    integral (scaled F (Real.exp (ell*t)) (Real.exp (2*ell*t))) =
      Real.exp (-4*ell*t)*integral F := by
  rw [integral_scaled F _ _ (Real.exp_pos _) (Real.exp_pos _)]
  rw [← Real.exp_neg,← Real.exp_neg,← Real.exp_nat_mul,← Real.exp_add]
  congr 2
  ring

theorem exponential_derivative (F : ℝ → ℝ → ℝ → ℝ → ℝ) (ell : ℝ) :
    HasDerivAt (fun t => integral (scaled F (Real.exp (ell*t)) (Real.exp (2*ell*t))))
      (-4*ell*integral F) 0 := by
  simp_rw [exponential_scaling]
  convert ((((hasDerivAt_id (0:ℝ)).const_mul (-4*ell)).exp).mul_const (integral F)) using 1
  simp

theorem linear_derivative (F : ℝ → ℝ → ℝ → ℝ → ℝ) (ell : ℝ) :
    HasDerivAt (fun t => integral (scaled F (1+t*ell) (1+2*t*ell)))
      (-4*ell*integral F) 0 := by
  have hA : HasDerivAt (fun t : ℝ => 1+t*ell) ell 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const ell).const_add 1
  have hB : HasDerivAt (fun t : ℝ => 1+2*t*ell) (2*ell) 0 := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ell).const_add 1
  have hd := (((hA.inv (by simp)).pow 2).mul (hB.inv (by simp))).mul_const (integral F)
  have hs : HasDerivAt (fun t : ℝ => (1+t*ell)⁻¹^2*(1+2*t*ell)⁻¹*integral F)
      (-4*ell*integral F) 0 := by
    convert hd using 1
    simp
    ring
  apply hs.congr_of_eventuallyEq
  have hAp : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+t*ell :=
    hA.continuousAt.eventually (eventually_gt_nhds (by simp))
  have hBp : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+2*t*ell :=
    hB.continuousAt.eventually (eventually_gt_nhds (by simp))
  filter_upwards [hAp,hBp] with t htA htB
  exact integral_scaled F _ _ htA htB

#print axioms integral_scaled
#print axioms exponential_scaling
#print axioms exponential_derivative
#print axioms linear_derivative
end
end UnifiedTheory.Audit.KFCausalJointFourierDilationMeasure
