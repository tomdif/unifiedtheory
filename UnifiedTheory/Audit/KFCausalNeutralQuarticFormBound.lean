/- A degree-independent lower bound for the quartic neutral second form.
The exact first-form square is retained through an integral Gram bound.
Every boundary integral is discharged by the weighted L2 domains. -/
import UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralQuarticFormBound
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain
open KFCausalNeutralQuarticBoundary
open KFCausalQuarticNeutralDefect
open KFCausalQuarticPlaneDomination (potential potential_positive)

def energy (f : ℝ → ℂ) : ℝ := ∫ x, potential x*‖f x‖^2
def first (η L : ℝ) (f g : ℝ → ℂ) : ℝ := ∫ x, firstDensity η L x (f x) (g x)
def second (η L : ℝ) (f g : ℝ → ℂ) : ℝ := ∫ x, secondDensity η L x (f x) (g x)

theorem energy_nonnegative (f : ℝ → ℂ) : 0 ≤ energy f :=
  integral_nonneg (fun x => mul_nonneg (potential_positive x).le (sq_nonneg _))

theorem square_energy (η L t : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    energy (fun x => direction η L x (f x) (g x)-(t:ℂ)*f x) =
      energy (fun x => direction η L x (f x) (g x))-t*first η L f g+t^2*energy f := by
  let d := fun x => direction η L x (f x) (g x)
  have hd := direction_regular η L f g hf hg
  have hi0 : Integrable (fun x => potential x*‖d x‖^2) := weight_norm_integrable d hd 0
  have hi1 := (first_integrable η L f g hf hg).const_mul t
  have hi2 : Integrable (fun x => t^2*(potential x*‖f x‖^2)) := (weight_norm_integrable f hf 0).const_mul _
  have he (x : ℝ) : potential x*‖d x-(t:ℂ)*f x‖^2 =
      potential x*‖d x‖^2-t*firstDensity η L x (f x) (g x)+t^2*(potential x*‖f x‖^2) := by
    rw [first_pairing]
    change potential x*‖d x-(t:ℂ)*f x‖^2 =
      potential x*‖d x‖^2-t*(2*potential x*(conj (f x)*d x).re)+t^2*(potential x*‖f x‖^2)
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
    ring
  change (∫ x, potential x*‖d x-(t:ℂ)*f x‖^2) = _
  simp_rw [he]
  have hi01 : Integrable (fun x => potential x*‖d x‖^2-t*firstDensity η L x (f x) (g x)) := hi0.sub hi1
  rw [integral_add hi01 hi2,integral_sub hi0 hi1,integral_const_mul,integral_const_mul]
  rfl

private theorem quadratic_bound (E B D : ℝ) (hE : 0 ≤ E)
    (hq : ∀ t : ℝ, 0 ≤ D-t*B+t^2*E) : B^2 ≤ 4*E*D := by
  by_cases he : E=0
  · by_cases hb : B=0
    · simp [he,hb]
    · have hh := hq ((D+1)/B)
      have ht : D-((D+1)/B)*B+((D+1)/B)^2*E = -1 := by rw [he]; field_simp; ring
      rw [ht] at hh
      norm_num at hh
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm he)
    have hh := mul_nonneg (show 0 ≤ 4*E by positivity) (hq (B/(2*E)))
    have ht : 4*E*(D-(B/(2*E))*B+(B/(2*E))^2*E) = 4*E*D-B^2 := by field_simp; ring
    rw [ht] at hh
    linarith

theorem first_square_bound (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    (first η L f g)^2 ≤ 4*energy f*energy (fun x => direction η L x (f x) (g x)) := by
  apply quadratic_bound _ _ _ (energy_nonnegative f)
  intro t
  rw [← square_energy η L t f g hf hg]
  exact energy_nonnegative _

theorem second_lower (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    4*energy (fun x => direction η L x (f x) (g x))-4*(L^2+η^2)*energy f ≤ second η L f g := by
  have hi0 : Integrable (fun x => potential x*‖direction η L x (f x) (g x)‖^2) :=
    weight_norm_integrable _ (direction_regular η L f g hf hg) 0
  have hi1 : Integrable (fun x => potential x*‖f x‖^2) := weight_norm_integrable f hf 0
  have hs := integral_mono ((hi0.const_mul 4).sub (hi1.const_mul (4*(L^2+η^2))))
    ((second_integrable η L f g hf hg).add ((boundary_integrable f g hf hg).const_mul (2*η^2)))
    (fun x => by simpa only [mul_assoc] using defect_lower η L x (f x) (g x))
  simp only [Pi.sub_apply,Pi.add_apply] at hs
  rw [integral_sub (hi0.const_mul 4) (hi1.const_mul (4*(L^2+η^2))),
    integral_add (second_integrable η L f g hf hg) ((boundary_integrable f g hf hg).const_mul (2*η^2))] at hs
  simp only [integral_const_mul,boundary_integral f g hf hg hd,mul_zero,add_zero] at hs
  exact hs

theorem curvature_form_bound (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    (first η L f g)^2-4*(L^2+η^2)*(energy f)^2 ≤ energy f*second η L f g := by
  have h0 := energy_nonnegative f
  have h1 := first_square_bound η L f g hf hg
  have h2 := mul_le_mul_of_nonneg_left (second_lower η L f g hf hg hd) h0
  nlinarith

#print axioms energy_nonnegative
#print axioms square_energy
#print axioms first_square_bound
#print axioms second_lower
#print axioms curvature_form_bound
end
end UnifiedTheory.Audit.KFCausalNeutralQuarticFormBound
