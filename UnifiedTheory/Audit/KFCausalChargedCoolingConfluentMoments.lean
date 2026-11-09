/- Actual Gaussian times positive-halfline moments for the repeated-width
polynomial Gram. All integrability is derived from positive Gaussian rates. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeCoercivity
import UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingConfluentMoments
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalShiftedComplexGaussianMoments (normalized)

def laplaceMoment (s : ℝ) (n : ℕ) (Y : ℝ) : ℂ :=
  (Y:ℂ)^n*Complex.exp (-(s:ℂ)*(Y:ℂ))

theorem laplace_moment_integrable (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Integrable (laplaceMoment s n) (volume.restrict (Set.Ioi 0)) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n:ℝ)) (p := 1) (b := s)
    (by exact lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n)) (by norm_num) hs
  simp only [Real.rpow_natCast,Real.rpow_one] at hi
  have hic : Integrable (fun Y : ℝ => ((Y^n*Real.exp (-s*Y):ℝ):ℂ))
      (volume.restrict (Set.Ioi 0)) := hi.ofReal
  simpa only [laplaceMoment,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_exp,
    Complex.ofReal_neg] using hic

theorem laplace_moment_integral (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (∫ Y : ℝ, laplaceMoment s n Y ∂volume.restrict (Set.Ioi 0)) =
      (n.factorial:ℂ)/(s:ℂ)^(n+1) := by
  have hi := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := (n:ℂ)+1) (r := s) (by simp; positivity) hs
  rw [Complex.Gamma_nat_eq_factorial] at hi
  simp only [add_sub_cancel_right,Complex.cpow_natCast] at hi
  rw [show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring,Complex.cpow_natCast] at hi
  convert hi using 1
  · apply integral_congr_ae
    filter_upwards [] with Y
    unfold laplaceMoment
    congr 1
    ring
  · simp only [div_eq_mul_inv,one_mul]
    ring

def monomial (s : ℝ) (m n : ℕ) (q : ℝ × ℝ) : ℂ :=
  (q.1:ℂ)^(2*m)*(q.2:ℂ)^n*Complex.exp (-(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ)))

theorem monomial_product (s : ℝ) (m n : ℕ) (q : ℝ × ℝ) :
    monomial s m n q =
      KFCausalShiftedComplexGaussianMoments.moment (s:ℂ) 0 (2*m) q.1 *
        laplaceMoment s n q.2 := by
  simp only [monomial,KFCausalShiftedComplexGaussianMoments.moment,laplaceMoment,
    zero_mul,add_zero]
  rw [show -(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ)) =
    -(s:ℂ)*(q.1:ℂ)^2+(-(s:ℂ)*(q.2:ℂ)) by ring,Complex.exp_add]
  ring

theorem monomial_integrable (s : ℝ) (hs : 0 < s) (m n : ℕ) :
    Integrable (monomial s m n) planeMeasure := by
  change Integrable (fun q => monomial s m n q) planeMeasure
  simp_rw [monomial_product]
  exact (KFCausalShiftedComplexGaussianMoments.moment_integrable (s:ℂ) 0
    (by simpa using hs) (2*m)).mul_prod (laplace_moment_integrable s hs n)

theorem monomial_integral (s : ℝ) (hs : 0 < s) (m n : ℕ) :
    (∫ q, monomial s m n q ∂planeMeasure) =
      KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)*normalized (s:ℂ) 0 (2*m)*
        ((n.factorial:ℂ)/(s:ℂ)^(n+1)) := by
  simp_rw [monomial_product]
  rw [planeMeasure,integral_prod_mul,laplace_moment_integral s hs]
  change KFCausalShiftedComplexGaussianMoments.value (s:ℂ) 0 (2*m)*_ = _
  rw [KFCausalShiftedComplexGaussianMoments.value_all (s:ℂ) 0 (by simpa using hs)]
  simp [KFCausalShiftedComplexGaussianMoments.mass]

def chargedCoordinate (p : ℂ) (q : ℝ × ℝ) : ℂ :=
  p*(q.1:ℂ)^2+conj p*(q.2:ℂ)

def cross (s : ℝ) (p : ℂ) (m n : Fin 3) (q : ℝ × ℝ) : ℂ :=
  chargedCoordinate p q^m.val*chargedCoordinate (conj p) q^n.val*
    Complex.exp (-(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ)))

def coefficient (p : ℂ) (m n i j : ℕ) : ℂ :=
  (m.choose i:ℂ)*(n.choose j:ℂ)*p^i*(conj p)^(m-i)*(conj p)^j*p^(n-j)

theorem cross_expansion (s : ℝ) (p : ℂ) (m n : Fin 3) (q : ℝ × ℝ) :
    cross s p m n q =
      ∑ i ∈ Finset.range (m.val+1), ∑ j ∈ Finset.range (n.val+1),
        coefficient p m.val n.val i j*monomial s (i+j) ((m.val-i)+(n.val-j)) q := by
  fin_cases m <;> fin_cases n <;>
    norm_num [cross,chargedCoordinate,coefficient,monomial,Finset.sum_range_succ] <;> ring

theorem cross_integrable (s : ℝ) (hs : 0 < s) (p : ℂ) (m n : Fin 3) :
    Integrable (cross s p m n) planeMeasure := by
  change Integrable (fun q => cross s p m n q) planeMeasure
  simp_rw [cross_expansion]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (monomial_integrable s hs (i+j) ((m.val-i)+(n.val-j))).const_mul _))

theorem cross_integral (s : ℝ) (hs : 0 < s) (p : ℂ) (m n : Fin 3) :
    (∫ q, cross s p m n q ∂planeMeasure) =
      ∑ i ∈ Finset.range (m.val+1), ∑ j ∈ Finset.range (n.val+1),
        coefficient p m.val n.val i j*
          (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)*normalized (s:ℂ) 0 (2*(i+j))*
            ((((m.val-i)+(n.val-j)).factorial:ℂ)/(s:ℂ)^((m.val-i)+(n.val-j)+1))) := by
  simp_rw [cross_expansion]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (monomial_integrable s hs (i+j) ((m.val-i)+(n.val-j))).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ =>
    (monomial_integrable s hs (i+j) ((m.val-i)+(n.val-j))).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,monomial_integral s hs]

def halfParameter (x : ℝ) : ℂ := ((1/2:ℝ):ℂ)+(x:ℂ)*Complex.I

theorem scaled_gram_integral (s x : ℝ) (hs : 0 < s) (m n : Fin 3) :
    (∫ q, cross s ((s:ℂ)*halfParameter x) m n q ∂planeMeasure) =
      (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ))*
        KFCausalChargedCoolingConfluentThreeCoercivity.gram x m n := by
  rw [cross_integral s hs]
  have hs0 : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  fin_cases m <;> fin_cases n <;>
    simp only [coefficient,halfParameter,map_mul,map_add,Complex.conj_ofReal,
      Complex.conj_I]
  all_goals
    norm_num [Finset.sum_range_succ,normalized,
      KFCausalChargedCoolingConfluentThreeCoercivity.gram,
      KFCausalChargedCoolingConfluentThreeCoercivity.hermitianThree]
  all_goals field_simp
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat] <;> ring

#print axioms laplace_moment_integrable
#print axioms laplace_moment_integral
#print axioms monomial_product
#print axioms monomial_integrable
#print axioms monomial_integral
#print axioms cross_expansion
#print axioms cross_integrable
#print axioms cross_integral
#print axioms scaled_gram_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingConfluentMoments
