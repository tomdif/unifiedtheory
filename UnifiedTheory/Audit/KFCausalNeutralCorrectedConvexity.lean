/- Gaussian correction makes the actual neutral translation energy
convex. The proof retains the square-completion remainder and never
divides by the energy, so exact cancellation is included. -/
import UnifiedTheory.Audit.KFCausalNeutralIntegralDerivatives
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralCorrectedConvexity
noncomputable section
open Set
open KFCausalNeutralIntegralDerivatives
open KFCausalNeutralTransportDomination (curve_regular)
open KFCausalNeutralUniformDefect (curve)
open KFCausalNeutralLinePackets (step)
open KFCausalQuarticNeutralDefect (direction)
open KFCausalNeutralQuarticFormBound

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (z : ℂ) (η L a : ℝ)

def corrected (v : ℝ) : ℝ := Real.exp (a*v^2)*total n β b c P z η L v
def correctedSlope (v : ℝ) : ℝ := Real.exp (a*v^2)*
  (2*a*v*total n β b c P z η L v+totalSlope n β b c P z η L v)
def correctedCurvature (v : ℝ) : ℝ := Real.exp (a*v^2)*
  (totalCurvature n β b c P z η L v+4*a*v*totalSlope n β b c P z η L v+
    (2*a+4*a^2*v^2)*total n β b c P z η L v)
def symmetric (v : ℝ) : ℝ := corrected n β b c P z η L a v+corrected n β b c P z η L a (-v)

theorem corrected_derivative (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (corrected n β b c P z η L a) (correctedSlope n β b c P z η L a v) v := by
  have he := (((hasDerivAt_id v).pow 2).const_mul a).exp
  convert he.mul (first_derivative_data n β b c P z η L hβ v).2 using 1
  dsimp [corrected,correctedSlope]
  ring

theorem correctedSlope_derivative (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (correctedSlope n β b c P z η L a) (correctedCurvature n β b c P z η L a v) v := by
  have he := (((hasDerivAt_id v).pow 2).const_mul a).exp
  have hU := (first_derivative_data n β b c P z η L hβ v).2
  have hB := (second_derivative_data n β b c P z η L hβ v).2
  have hd := he.mul ((((hasDerivAt_id v).const_mul (2*a)).mul hU).add hB)
  convert hd using 1
  dsimp [correctedSlope,correctedCurvature]
  ring

theorem deriv_corrected (hβ : 0 < β) :
    deriv (corrected n β b c P z η L a) = correctedSlope n β b c P z η L a := by
  funext v
  exact (corrected_derivative n β b c P z η L a hβ v).deriv

theorem deriv_correctedSlope (hβ : 0 < β) :
    deriv (correctedSlope n β b c P z η L a) = correctedCurvature n β b c P z η L a := by
  funext v
  exact (correctedSlope_derivative n β b c P z η L a hβ v).deriv

theorem correctedCurvature_nonnegative (hβ : 0 < β) (ha : 2*(L^2+η^2) ≤ a) (v : ℝ) :
    0 ≤ correctedCurvature n β b c P z η L a v := by
  unfold correctedCurvature
  apply mul_nonneg (Real.exp_pos _).le
  rw [total_form,totalSlope_form n β b c P z η L hβ,totalCurvature_form n β b c P z η L hβ]
  let f := fun x => curve n β b c P z η L x v
  let g := fun x => curve n β b c (fun i => step β (b i) (P i)) z η L x v
  have hf := curve_regular n β b c P z η L hβ v
  have hg := curve_regular n β b c (fun i => step β (b i) (P i)) z η L hβ v
  have hq := second_lower η L f g hf hg (curve_x_derivative n β b c P z η L v)
  have hp := energy_nonnegative (fun x => direction η L x (f x) (g x)-((-a*v:ℝ):ℂ)*f x)
  rw [square_energy η L (-a*v) f g hf hg] at hp
  have hr := mul_nonneg (show 0 ≤ 2*a-4*(L^2+η^2) by linarith) (energy_nonnegative f)
  change 0 ≤ second η L f g+4*a*v*first η L f g+(2*a+4*a^2*v^2)*energy f
  nlinarith

theorem corrected_convex (hβ : 0 < β) (ha : 2*(L^2+η^2) ≤ a) :
    ConvexOn ℝ univ (corrected n β b c P z η L a) := by
  apply convexOn_univ_of_deriv2_nonneg
    (fun v => (corrected_derivative n β b c P z η L a hβ v).differentiableAt)
  · rw [deriv_corrected n β b c P z η L a hβ]
    exact fun v => (correctedSlope_derivative n β b c P z η L a hβ v).differentiableAt
  · intro v
    change 0 ≤ deriv (deriv (corrected n β b c P z η L a)) v
    rw [deriv_corrected n β b c P z η L a hβ,deriv_correctedSlope n β b c P z η L a hβ]
    exact correctedCurvature_nonnegative n β b c P z η L a hβ ha v

theorem symmetric_derivative (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (symmetric n β b c P z η L a)
      (correctedSlope n β b c P z η L a v-correctedSlope n β b c P z η L a (-v)) v := by
  have hd := (corrected_derivative n β b c P z η L a hβ v).add
    ((corrected_derivative n β b c P z η L a hβ (-v)).comp v (hasDerivAt_neg v))
  simpa only [symmetric,mul_neg_one,sub_eq_add_neg] using hd

theorem symmetric_monotone (hβ : 0 < β) (ha : 2*(L^2+η^2) ≤ a) :
    MonotoneOn (symmetric n β b c P z η L a) (Ici 0) := by
  have hc : Continuous (symmetric n β b c P z η L a) :=
    (show Differentiable ℝ _ from fun v => (symmetric_derivative n β b c P z η L a hβ v).differentiableAt).continuous
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc.continuousOn
    (fun v _ => (symmetric_derivative n β b c P z η L a hβ v).hasDerivWithinAt)
  intro v hv
  have hv' : 0 ≤ v := interior_subset hv
  have hm := (corrected_convex n β b c P z η L a hβ ha).monotoneOn_deriv
    (fun t _ => (corrected_derivative n β b c P z η L a hβ t).differentiableAt)
  have hh := hm (mem_univ (-v)) (mem_univ v) (by linarith : -v ≤ v)
  rw [deriv_corrected n β b c P z η L a hβ] at hh
  exact sub_nonneg.mpr hh

theorem symmetric_nonnegative (v : ℝ) : 0 ≤ symmetric n β b c P z η L a v := by
  unfold symmetric corrected
  rw [total_form,total_form]
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le (energy_nonnegative _))
    (mul_nonneg (Real.exp_pos _).le (energy_nonnegative _))

#print axioms corrected_derivative
#print axioms correctedSlope_derivative
#print axioms deriv_corrected
#print axioms deriv_correctedSlope
#print axioms correctedCurvature_nonnegative
#print axioms corrected_convex
#print axioms symmetric_derivative
#print axioms symmetric_monotone
#print axioms symmetric_nonnegative
end
end UnifiedTheory.Audit.KFCausalNeutralCorrectedConvexity
