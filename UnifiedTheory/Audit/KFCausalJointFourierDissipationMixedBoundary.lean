/- The charged-neutral mixed second derivative has an exact neutral
integration-by-parts identity. Arbitrary correlated charged profiles
are retained. Polynomial L2 regularity proves all boundary hypotheses. -/
import UnifiedTheory.Audit.KFCausalJointFourierDissipationKernel
import UnifiedTheory.Audit.KFCausalNeutralQuarticTransportForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedBoundary
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain
open KFCausalQuarticPlaneDomination (potential potentialSlope potential_derivative)
open KFCausalQuarticNeutralDefect
open KFCausalNeutralQuarticBoundary
open KFCausalNeutralQuarticTransportForms (velocity acceleration)

def mixed (η L x : ℝ) (f g C Cg : ℂ) : ℝ :=
  2*potential x*((conj (velocity η L*g)*C).re+(conj f*(velocity η L*Cg)).re)

def completedMixed (η L x : ℝ) (f g C : ℂ) : ℝ :=
  4*potential x*(conj (direction η L x f g)*C).re

def crossBoundary (η L x : ℝ) (f g C Cg : ℂ) : ℝ :=
  potentialSlope x*(conj f*(velocity η L*C)).re+
    potential x*(conj g*(velocity η L*C)+conj f*(velocity η L*Cg)).re

theorem mixed_completion (η L x : ℝ) (f g C Cg : ℂ) :
    mixed η L x f g C Cg = completedMixed η L x f g C+2*crossBoundary η L x f g C Cg := by
  have hp := (KFCausalQuarticPlaneDomination.potential_positive x).ne'
  unfold mixed completedMixed crossBoundary direction connection velocity
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  field_simp
  ring

theorem crossBoundary_derivative (η L : ℝ) (f g C Cg : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (g x) x) (hC : HasDerivAt C (Cg x) x) :
    HasDerivAt (fun t => potential t*(conj (f t)*(velocity η L*C t)).re)
      (crossBoundary η L x (f x) (g x) (C x) (Cg x)) x := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hf.star.mul (hC.const_mul (velocity η L)))
  convert (potential_derivative x).mul hd using 1

theorem crossBoundary_integrable (η L : ℝ) (f g C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hC : Regular C) (hCg : Regular Cg) :
    Integrable (fun x => crossBoundary η L x (f x) (g x) (C x) (Cg x)) := by
  have hV := regular_const_mul C hC (velocity η L)
  have hVg := regular_const_mul Cg hCg (velocity η L)
  have h0 := weight_re_integrable f _ hf hV 1
  have h1 := weight_re_integrable g _ hg hV 0
  have h2 := weight_re_integrable f _ hf hVg 0
  simpa only [crossBoundary,Complex.add_re,mul_add] using h0.add (h1.add h2)

theorem crossBoundary_integral (η L : ℝ) (f g C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hC : Regular C) (hCg : Regular Cg)
    (hdf : ∀ x, HasDerivAt f (g x) x) (hdC : ∀ x, HasDerivAt C (Cg x) x) :
    (∫ x, crossBoundary η L x (f x) (g x) (C x) (Cg x)) = 0 := by
  have hV := regular_const_mul C hC (velocity η L)
  have hVg := regular_const_mul Cg hCg (velocity η L)
  have h0 : Integrable (fun x => potential x*(conj (f x)*(velocity η L*C x)).re) :=
    weight_re_integrable f _ hf hV 0
  have h1 : Integrable (fun x => potentialSlope x*(conj (f x)*(velocity η L*C x)).re) :=
    weight_re_integrable f _ hf hV 1
  have h2 : Integrable (fun x => potential x*(conj (g x)*(velocity η L*C x)+
      conj (f x)*(velocity η L*Cg x)).re) := by
    simpa only [Complex.add_re,mul_add] using
      (weight_re_integrable g _ hg hV 0).add (weight_re_integrable f _ hf hVg 0)
  have hd (x : ℝ) : HasDerivAt (fun t => (conj (f t)*(velocity η L*C t)).re)
      (conj (g x)*(velocity η L*C x)+conj (f x)*(velocity η L*Cg x)).re x := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((hdf x).star.mul ((hdC x).const_mul (velocity η L)))
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable potential_derivative hd h2 h1 h0
  unfold crossBoundary
  rw [integral_add h1 h2,hb]
  ring

theorem completedMixed_integrable (η L : ℝ) (f g C : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hC : Regular C) :
    Integrable (fun x => completedMixed η L x (f x) (g x) (C x)) := by
  have hi := (weight_re_integrable _ C (direction_regular η L f g hf hg) hC 0).const_mul 4
  simpa only [completedMixed,mul_assoc] using hi

theorem mixed_integrable (η L : ℝ) (f g C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hC : Regular C) (hCg : Regular Cg) :
    Integrable (fun x => mixed η L x (f x) (g x) (C x) (Cg x)) := by
  simp_rw [mixed_completion]
  exact (completedMixed_integrable η L f g C hf hg hC).add
    ((crossBoundary_integrable η L f g C Cg hf hg hC hCg).const_mul 2)

theorem mixed_integral (η L : ℝ) (f g C Cg : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hC : Regular C) (hCg : Regular Cg)
    (hdf : ∀ x, HasDerivAt f (g x) x) (hdC : ∀ x, HasDerivAt C (Cg x) x) :
    (∫ x, mixed η L x (f x) (g x) (C x) (Cg x)) =
      ∫ x, completedMixed η L x (f x) (g x) (C x) := by
  simp_rw [mixed_completion]
  rw [integral_add (completedMixed_integrable η L f g C hf hg hC)
    ((crossBoundary_integrable η L f g C Cg hf hg hC hCg).const_mul 2),
    integral_const_mul,crossBoundary_integral η L f g C Cg hf hg hC hCg hdf hdC,
    mul_zero,add_zero]

#print axioms mixed_completion
#print axioms crossBoundary_derivative
#print axioms crossBoundary_integrable
#print axioms crossBoundary_integral
#print axioms completedMixed_integrable
#print axioms mixed_integrable
#print axioms mixed_integral
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationMixedBoundary
