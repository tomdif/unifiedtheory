/- Polynomial integrability on the actual Gaussian/Laplace joint measure.
All Gaussian linear sources and all finite polynomial degrees are allowed.
No integrability of a limiting clustered-width density is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralLinePackets
import UnifiedTheory.Audit.KFCausalClusteredWidthProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointPolynomialIntegrability
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)

def coordinates (p : Joint) : Fin 4 → ℂ :=
  ![(p.1.1:ℂ),(p.1.2 0:ℂ),(p.1.2 1:ℂ),(p.2:ℂ)]
def weight (a c d l m : ℝ) (p : Joint) : ℝ :=
  Real.exp (-a*p.1.1^2)*Real.exp (-c*(p.1.2 0)^2+l*p.1.2 0)*
    Real.exp (-d*(p.1.2 1)^2+m*p.1.2 1)*Real.exp (-a*p.2)

theorem gaussian_moment_integrable (a b : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (x:ℂ)^k*(Real.exp (-a*x^2+b*x):ℂ)) := by
  convert KFCausalNeutralLinePackets.monomial_integrable a ha (b:ℂ) k using 1
  funext x
  unfold KFCausalNeutralLinePackets.monomial
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem laplace_moment_integrable (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : ℝ => (x:ℂ)^k*(Real.exp (-a*x):ℂ)) (volume.restrict (Set.Ioi 0)) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (show (-1:ℝ) < (k:ℝ) by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    (show (1:ℝ) ≤ 1 by rfl) ha
  have hr : IntegrableOn (fun x : ℝ => x^k*Real.exp (-a*x)) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast,Real.rpow_one] using hi
  have hi : Integrable (fun x : ℝ => ((x^k*Real.exp (-a*x):ℝ):ℂ))
      (volume.restrict (Set.Ioi 0)) := hr.ofReal
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using hi

theorem monomial_integrable (a c d l m : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (k : Fin 4 → ℕ) :
    Integrable (fun p : Joint => (∏ i, (coordinates p i)^(k i))*(weight a c d l m p:ℂ)) jointMeasure := by
  have hpos : ∀ i : Fin 2, 0 < (![c,d] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> assumption
  have hp := Integrable.fintype_prod (fun i : Fin 2 =>
    gaussian_moment_integrable (![c,d] i) (![l,m] i) (hpos i) (![k 1,k 2] i))
  have hp' : Integrable (fun u : Fin 2 → ℝ =>
      ((u 0:ℂ)^(k 1)*(Real.exp (-c*(u 0)^2+l*u 0):ℂ))*
      ((u 1:ℂ)^(k 2)*(Real.exp (-d*(u 1)^2+m*u 1):ℂ))) := by
    simpa only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.prod_univ_zero,mul_one] using hp
  have hu := (gaussian_moment_integrable a 0 ha (k 0)).mul_prod hp'
  rw [← Measure.volume_eq_prod ℝ (Fin 2 → ℝ)] at hu
  have hi := hu.mul_prod (laplace_moment_integrable a ha (k 3))
  convert hi using 1
  funext p
  simp only [coordinates,weight,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,mul_one,zero_mul,add_zero,Complex.ofReal_mul]
  simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  rw [show (2:Fin 3).succ = (3:Fin 4) from rfl]
  ring

theorem polynomial_integrable (a c d l m : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (P : MvPolynomial (Fin 4) ℂ) :
    Integrable (fun p : Joint => MvPolynomial.eval (coordinates p) P*(weight a c d l m p:ℂ)) jointMeasure := by
  have hi := integrable_finset_sum P.support (fun k _ =>
    (monomial_integrable a c d l m ha hc hd k).const_mul (P.coeff k))
  convert hi using 1
  funext p
  simp only [MvPolynomial.eval_eq',Finset.sum_mul,mul_assoc]

theorem conjugate_evaluation (P : MvPolynomial (Fin 4) ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (MvPolynomial.map (starRingEnd ℂ) P) =
      conj (MvPolynomial.eval (coordinates p) P) := by
  rw [MvPolynomial.map_eval]
  have he : (starRingEnd ℂ) ∘ coordinates p = coordinates p := by
    funext i
    fin_cases i <;> simp [coordinates]
  rw [he]

theorem squared_polynomial_integrable (a c d l m : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (P : MvPolynomial (Fin 4) ℂ) :
    Integrable (fun p : Joint => ‖MvPolynomial.eval (coordinates p) P‖^2*weight a c d l m p) jointMeasure := by
  have hi := (polynomial_integrable a c d l m ha hc hd
    (MvPolynomial.map (starRingEnd ℂ) P*P)).re
  convert hi using 1
  funext p
  change _ = ((MvPolynomial.eval (coordinates p) _)*(weight a c d l m p:ℂ)).re
  rw [MvPolynomial.eval_mul,conjugate_evaluation,Complex.conj_mul']
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

#print axioms gaussian_moment_integrable
#print axioms laplace_moment_integrable
#print axioms monomial_integrable
#print axioms polynomial_integrable
#print axioms conjugate_evaluation
#print axioms squared_polynomial_integrable
end
end UnifiedTheory.Audit.KFCausalJointPolynomialIntegrability
