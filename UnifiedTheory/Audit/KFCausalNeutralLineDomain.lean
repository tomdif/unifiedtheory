/- Polynomially weighted L2 domains, including every finite translated
neutral family. These bounds justify the cross integrals and boundary
terms used in the quantitative quartic transport estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralLinePackets
import UnifiedTheory.Audit.KFCausalQuarticNeutralDefect
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralLineDomain
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLinePackets (packet entire step translatedPolynomial)
open KFCausalQuarticPlaneDomination (potential potentialSlope)
open KFCausalQuarticNeutralDefect (potentialSecond)

def Regular (f : ℝ → ℂ) : Prop :=
  ∀ P : Polynomial ℂ, MemLp (fun x : ℝ => P.eval (x:ℂ)*f x) 2 volume

theorem regular_memLp (f : ℝ → ℂ) (hf : Regular f) : MemLp f 2 volume := by
  simpa only [Polynomial.eval_one,one_mul] using hf 1

theorem regular_add (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Regular (fun x => f x+g x) := by
  intro P
  simpa only [mul_add] using (hf P).add (hg P)

theorem regular_const_mul (f : ℝ → ℂ) (hf : Regular f) (c : ℂ) :
    Regular (fun x => c*f x) := by
  intro P
  simpa only [mul_left_comm] using (hf P).const_mul c

theorem regular_sum (n : ℕ) (f : Fin n → ℝ → ℂ) (hf : ∀ i, Regular (f i)) :
    Regular (fun x => ∑ i, f i x) := by
  intro P
  simpa only [Finset.mul_sum] using memLp_finset_sum Finset.univ (fun i _ => hf i P)

theorem packet_regular (β : ℝ) (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ) :
    Regular (packet β b P) := by
  intro Q
  simpa only [KFCausalNeutralLinePackets.packet_polynomial] using
    KFCausalNeutralLinePackets.packet_memLp β hβ b (Q*P)

theorem translated_regular (β : ℝ) (hβ : 0 < β) (b z : ℂ) (P : Polynomial ℂ) :
    Regular (fun x : ℝ => entire β b P ((x:ℂ)+z)) := by
  simp_rw [KFCausalNeutralLinePackets.translated_packet]
  exact packet_regular β hβ _ _

def family (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ i, c i*entire β (b i) (P i) z

theorem family_regular (n : ℕ) (β : ℝ) (hβ : 0 < β) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) :
    Regular (fun x : ℝ => family n β b c P ((x:ℂ)+z)) :=
  regular_sum n _ (fun i => regular_const_mul _ (translated_regular β hβ (b i) z (P i)) (c i))

theorem family_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (z : ℂ) :
    HasDerivAt (family n β b c P) (family n β b c (fun i => step β (b i) (P i)) z) z := by
  exact HasDerivAt.fun_sum (fun i _ => (KFCausalNeutralLinePackets.entire_derivative β (b i) (P i) z).const_mul (c i))

theorem polynomial_cross_integrable (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (P : Polynomial ℂ) : Integrable (fun x : ℝ => P.eval (x:ℂ)*(conj (f x)*g x)) := by
  have hi := (regular_memLp f hf).star.integrable_mul (hg P)
  change Integrable (fun x => star (f x)*(P.eval (x:ℂ)*g x)) at hi
  simpa only [Complex.star_def,mul_left_comm] using hi

def weightPolynomial (j : Fin 3) : Polynomial ℂ :=
  ![1+Polynomial.C (1/2)*Polynomial.X^2+Polynomial.C (1/4)*Polynomial.X^4,
    Polynomial.X+Polynomial.X^3,1+Polynomial.C 3*Polynomial.X^2] j
def weight (j : Fin 3) (x : ℝ) : ℝ := ![potential x,potentialSlope x,potentialSecond x] j

theorem weight_eval (j : Fin 3) (x : ℝ) :
    (weightPolynomial j).eval (x:ℂ) = (weight j x:ℂ) := by
  fin_cases j <;> simp [weightPolynomial,weight,potential,potentialSlope,potentialSecond]
  ring

theorem weight_cross_integrable (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) (j : Fin 3) :
    Integrable (fun x => (weight j x:ℂ)*(conj (f x)*g x)) := by
  simpa only [weight_eval] using polynomial_cross_integrable f g hf hg (weightPolynomial j)

theorem weight_re_integrable (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) (j : Fin 3) :
    Integrable (fun x => weight j x*(conj (f x)*g x).re) := by
  have hi := (weight_cross_integrable f g hf hg j).re
  change Integrable (fun x => ((weight j x:ℂ)*(conj (f x)*g x)).re) at hi
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hi

theorem weight_im_integrable (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) (j : Fin 3) :
    Integrable (fun x => weight j x*(conj (f x)*g x).im) := by
  have hi := (weight_cross_integrable f g hf hg j).im
  change Integrable (fun x => ((weight j x:ℂ)*(conj (f x)*g x)).im) at hi
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using hi

theorem weight_norm_integrable (f : ℝ → ℂ) (hf : Regular f) (j : Fin 3) :
    Integrable (fun x => weight j x*‖f x‖^2) := by
  simpa only [Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re] using
    weight_re_integrable f f hf hf j

#print axioms regular_memLp
#print axioms regular_add
#print axioms regular_const_mul
#print axioms regular_sum
#print axioms packet_regular
#print axioms translated_regular
#print axioms family_regular
#print axioms family_derivative
#print axioms polynomial_cross_integrable
#print axioms weight_eval
#print axioms weight_cross_integrable
#print axioms weight_re_integrable
#print axioms weight_im_integrable
#print axioms weight_norm_integrable
end
end UnifiedTheory.Audit.KFCausalNeutralLineDomain
