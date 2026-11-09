/- A strict sign for the paired quadratic excitation under unequal
Gaussian widths. Reflection removes odd field terms; interchange of
the pair then gives a nonnegative density with nonempty support. -/
import UnifiedTheory.Audit.KFCausalPolynomialGaussianIntegrals
import UnifiedTheory.Audit.KFCausalQuarticPlaneDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalChargedPairIntegral
noncomputable section
open MeasureTheory
open KFCausalPolynomialGaussianIntegrals
open KFCausalQuarticPlaneDomination (potential)

abbrev Space := Fin 3 → ℝ

def gaussian (A B C : ℝ) (u : Space) : ℝ :=
  Real.exp (-A*(u 0)^2-B*(u 1)^2-C*(u 2)^2)

def evenPotential (d z x : ℝ) : ℝ :=
  1+(z^2+d^2*x^2)/2+(z^4+6*z^2*d^2*x^2+d^4*x^4)/4

def density (A B C d : ℝ) (u : Space) : ℝ :=
  ((u 0)^2-(u 1)^2)*potential (u 2+d*u 0)*gaussian A B C u

def evenDensity (A B C d : ℝ) (u : Space) : ℝ :=
  ((u 0)^2-(u 1)^2)*evenPotential d (u 2) (u 0)*gaussian A B C u

def swap (u : Space) : Space := ![u 1,u 0,u 2]
def reflect (u : Space) : Space := ![u 0,u 1,-u 2]

def symmetricDensity (A B C d : ℝ) (u : Space) : ℝ :=
  (evenDensity A B C d u+evenDensity A B C d (swap u))/2

theorem gaussian_weight (A B C : ℝ) (u : Space) :
    gaussian A B C u = weight ![A,B,C] u := by
  simp only [weight,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,mul_one,← Real.exp_add,gaussian]
  congr 1
  change -A*(u 0)^2-B*(u 1)^2-C*(u 2)^2 =
    -A*(u 0)^2+(-B*(u 1)^2+-C*(u 2)^2)
  ring

theorem density_integrable (A B C d : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    Integrable (density A B C d) volume := by
  let X := fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) ℝ)
  let V := X 2+MvPolynomial.C d*X 0
  let P := (X 0^2-X 1^2)*(1+MvPolynomial.C (1/2)*V^2+MvPolynomial.C (1/4)*V^4)
  have hi := polynomial_integrable 3 ![A,B,C]
    (by intro i; fin_cases i; exact hA; exact hB; exact hC) P
  convert hi using 1
  funext u
  simp only [density,potential,gaussian_weight,P,V,X,map_mul,map_sub,map_add,map_one,
    map_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
  ring

theorem evenPotential_reflection (d z x : ℝ) :
    (potential (z+d*x)+potential (-z+d*x))/2 = evenPotential d z x := by
  unfold potential evenPotential
  ring

theorem evenPotential_positive (d z x : ℝ) : 0 < evenPotential d z x := by
  unfold evenPotential
  positivity

theorem evenPotential_mono (d z x y : ℝ) (hxy : y^2 ≤ x^2) :
    evenPotential d z y ≤ evenPotential d z x := by
  have hp : 0 ≤ x^4-y^4 := by nlinarith [sq_nonneg (x^2-y^2)]
  have h1 := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hxy)
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg d)) (sub_nonneg.mpr hxy)
  have h3 := mul_nonneg (by positivity : 0 ≤ d^4) hp
  unfold evenPotential
  nlinarith

theorem swap_twice (u : Space) : swap (swap u) = u := by
  funext i
  fin_cases i <;> simp [swap]

theorem swap_preserving : MeasurePreserving swap volume volume := by
  have hm := volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ)
    (Equiv.swap (0 : Fin 3) 1)
  convert hm using 1
  funext u i
  fin_cases i <;> simp [swap,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
    Equiv.swap_apply_def]

def swapEquiv : Space ≃ᵐ Space :=
  { toEquiv := ⟨swap,swap,swap_twice,swap_twice⟩
    measurable_toFun := by change Measurable swap; exact swap_preserving.measurable
    measurable_invFun := by change Measurable swap; exact swap_preserving.measurable }

theorem reflect_twice (u : Space) : reflect (reflect u) = u := by
  funext i
  fin_cases i <;> simp [reflect]

theorem reflect_preserving : MeasurePreserving reflect volume volume := by
  have hm := volume_preserving_pi (f := fun i : Fin 3 =>
    fun x : ℝ => if i=2 then -x else x) (by
      intro i
      by_cases hi : i=2
      · simpa only [if_pos hi] using Measure.measurePreserving_neg (volume : Measure ℝ)
      · simpa only [if_neg hi] using MeasurePreserving.id (volume : Measure ℝ))
  convert hm using 1
  funext u i
  fin_cases i <;> simp [reflect]

def reflectEquiv : Space ≃ᵐ Space :=
  { toEquiv := ⟨reflect,reflect,reflect_twice,reflect_twice⟩
    measurable_toFun := by change Measurable reflect; exact reflect_preserving.measurable
    measurable_invFun := by change Measurable reflect; exact reflect_preserving.measurable }

theorem density_reflection (A B C d : ℝ) (u : Space) :
    (density A B C d u+density A B C d (reflect u))/2 = evenDensity A B C d u := by
  simp [density,evenDensity,reflect,gaussian,potential,evenPotential]
  ring

theorem evenDensity_integrable (A B C d : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    Integrable (evenDensity A B C d) volume := by
  have hi := density_integrable A B C d hA hB hC
  convert (hi.add (reflect_preserving.integrable_comp_of_integrable hi)).div_const 2 using 1
  funext u
  exact (density_reflection A B C d u).symm

theorem symmetricDensity_integrable (A B C d : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    Integrable (symmetricDensity A B C d) volume := by
  have hi := evenDensity_integrable A B C d hA hB hC
  exact (hi.add (swap_preserving.integrable_comp_of_integrable hi)).div_const 2

theorem integral_symmetrize (A B C d : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    ∫ u, density A B C d u = ∫ u, symmetricDensity A B C d u := by
  have hi := density_integrable A B C d hA hB hC
  have he := evenDensity_integrable A B C d hA hB hC
  have hr := reflect_preserving.integral_comp reflectEquiv.measurableEmbedding (density A B C d)
  have hs := swap_preserving.integral_comp swapEquiv.measurableEmbedding (evenDensity A B C d)
  have hir : Integrable (fun u => density A B C d (reflect u)) volume :=
    reflect_preserving.integrable_comp_of_integrable hi
  have hes : Integrable (fun u => evenDensity A B C d (swap u)) volume :=
    swap_preserving.integrable_comp_of_integrable he
  have hfirst : ∫ u, evenDensity A B C d u = ∫ u, density A B C d u := by
    simp_rw [← density_reflection]
    rw [integral_div,integral_add hi hir,hr]
    ring
  simp only [symmetricDensity]
  rw [integral_div,integral_add he hes,hs,hfirst]
  ring

private theorem ordered_difference_nonnegative (A B C d : ℝ) (hAB : A ≤ B)
    (x y z : ℝ) (hxy : y^2 ≤ x^2) :
    0 ≤ evenPotential d z x*Real.exp (-A*x^2-B*y^2-C*z^2)-
      evenPotential d z y*Real.exp (-A*y^2-B*x^2-C*z^2) := by
  have hexp : Real.exp (-A*y^2-B*x^2-C*z^2) ≤
      Real.exp (-A*x^2-B*y^2-C*z^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hxy)]
  exact sub_nonneg.mpr (mul_le_mul (evenPotential_mono d z x y hxy) hexp
    (Real.exp_pos _).le (evenPotential_positive d z x).le)

theorem symmetricDensity_nonnegative (A B C d : ℝ) (hAB : A ≤ B) (u : Space) :
    0 ≤ symmetricDensity A B C d u := by
  have hid : symmetricDensity A B C d u =
      (((u 0)^2-(u 1)^2)*
        (evenPotential d (u 2) (u 0)*gaussian A B C u-
          evenPotential d (u 2) (u 1)*gaussian A B C (swap u)))/2 := by
    simp [symmetricDensity,evenDensity,swap]
    ring
  rw [hid]
  apply div_nonneg _ (by norm_num)
  rcases le_total ((u 1)^2) ((u 0)^2) with hxy | hyx
  · exact mul_nonneg (sub_nonneg.mpr hxy)
      (ordered_difference_nonnegative A B C d hAB (u 0) (u 1) (u 2) hxy)
  · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hyx)
    have hn := ordered_difference_nonnegative A B C d hAB (u 1) (u 0) (u 2) hyx
    change _ ≤ 0
    dsimp [gaussian,swap]
    linarith

theorem symmetricDensity_positive_at (A B C d : ℝ) (hAB : A < B) :
    0 < symmetricDensity A B C d ![1,0,0] := by
  have he : Real.exp (-B) < Real.exp (-A) := Real.exp_lt_exp.mpr (neg_lt_neg hAB)
  have hp := evenPotential_mono d 0 1 0 (by norm_num)
  have hp0 : evenPotential d 0 0 = 1 := by norm_num [evenPotential]
  rw [hp0] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-A)).le
  change 0 < ((1^2-0^2)*evenPotential d 0 1*Real.exp (-A*1^2-B*0^2-C*0^2)+
    (0^2-1^2)*evenPotential d 0 0*Real.exp (-A*0^2-B*1^2-C*0^2))/2
  norm_num [evenPotential]
  norm_num [evenPotential] at hm
  nlinarith

theorem integral_positive (A B C d : ℝ) (hA : 0 < A) (hAB : A < B) (hC : 0 < C) :
    0 < ∫ u, density A B C d u := by
  rw [integral_symmetrize A B C d hA (hA.trans hAB) hC]
  apply integral_pos_of_integrable_nonneg_nonzero
    (f := symmetricDensity A B C d) (x := ![1,0,0])
  · change Continuous (fun u : Space =>
      (((u 0)^2-(u 1)^2)*evenPotential d (u 2) (u 0)*
        Real.exp (-A*(u 0)^2-B*(u 1)^2-C*(u 2)^2)+
      ((u 1)^2-(u 0)^2)*evenPotential d (u 2) (u 1)*
        Real.exp (-A*(u 1)^2-B*(u 0)^2-C*(u 2)^2))/2)
    unfold evenPotential
    fun_prop
  · exact symmetricDensity_integrable A B C d hA (hA.trans hAB) hC
  · exact symmetricDensity_nonnegative A B C d hAB.le
  · exact (symmetricDensity_positive_at A B C d hAB).ne'

#print axioms gaussian_weight
#print axioms density_integrable
#print axioms evenPotential_reflection
#print axioms evenPotential_positive
#print axioms evenPotential_mono
#print axioms swap_twice
#print axioms swap_preserving
#print axioms reflect_twice
#print axioms reflect_preserving
#print axioms density_reflection
#print axioms evenDensity_integrable
#print axioms symmetricDensity_integrable
#print axioms integral_symmetrize
#print axioms symmetricDensity_nonnegative
#print axioms symmetricDensity_positive_at
#print axioms integral_positive
end
end UnifiedTheory.Audit.KFCausalChargedPairIntegral
