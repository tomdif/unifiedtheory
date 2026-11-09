/- Actual smooth L2 Hermite functions and their oscillator differential
equation. This does not identify the domain of the full physical operator. -/
import UnifiedTheory.Audit.KFCausalHermiteL2Completeness
import UnifiedTheory.Audit.KFCausalHermiteOscillatorPolynomial
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHermiteOscillatorFunctions
noncomputable section
open MeasureTheory Polynomial
open KFCausalGaussianSliceDomain (gaussian)
open KFCausalGaussianPolynomialTotality (polynomialState polynomialState_coe)
open KFCausalNeutralHermiteDomain (multiplier)
open KFCausalHermiteOscillatorPolynomial (oscillator multiplier_eigenvalue)

def packet (a : ℝ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  P.eval (x:ℂ)*gaussian a x

def step (a : ℝ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P.derivative-C (2*(a:ℂ))*X*P

theorem packet_memLp (a : ℝ) (ha : 0 < a) (P : Polynomial ℂ) :
    MemLp (packet a P) 2 volume :=
  (memLp_congr_ae (polynomialState_coe a ha P)).mp (Lp.memLp (polynomialState a ha P))

theorem packet_derivative (a : ℝ) (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (packet a P) (packet a (step a P) x) x := by
  have hg := (((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-(a:ℂ))).cexp
  convert ((P.hasDerivAt (x:ℂ)).comp_ofReal).mul hg using 1
  simp only [packet,step,gaussian,eval_sub,eval_mul,eval_C,eval_X,
    Pi.pow_apply,id_eq,Complex.ofReal_one]
  ring

theorem polynomialState_ne_zero (a : ℝ) (ha : 0 < a) (P : Polynomial ℂ) (hP : P ≠ 0) :
    polynomialState a ha P ≠ 0 := by
  intro hz
  have hae : packet a P =ᵐ[volume] 0 :=
    (polynomialState_coe a ha P).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz)
  have he : packet a P = 0 := Measure.eq_of_ae_eq hae
    (by unfold packet gaussian; fun_prop) continuous_zero
  apply hP
  apply P.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨x,rfl⟩
  have hx := congrFun he x
  change P.eval (x:ℂ)*gaussian a x = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_right (Complex.exp_ne_zero _)

theorem deriv_packet (a : ℝ) (P : Polynomial ℂ) :
    deriv (packet a P) = packet a (step a P) :=
  funext (fun x => (packet_derivative a P x).deriv)

theorem oscillator_conjugation (a : ℝ) (P : Polynomial ℂ) (x : ℝ) :
    -deriv (deriv (packet a P)) x+4*(a:ℂ)^2*(x:ℂ)^2*packet a P x =
      packet a (oscillator (a:ℂ) P) x := by
  rw [deriv_packet,deriv_packet]
  simp only [packet,step,oscillator,derivative_sub,derivative_mul,derivative_C,
    derivative_X,zero_mul,zero_add,mul_one,eval_sub,eval_add,eval_neg,eval_mul,eval_C,eval_X]
  ring

/-- The pointwise Hermite oscillator eigen-equation, with no spectral premise. -/
theorem hermite_equation (a : ℝ) (ha : 0 < a) (n : ℕ) (x : ℝ) :
    -deriv (deriv (packet a (multiplier a 0 n))) x+
        4*(a:ℂ)^2*(x:ℂ)^2*packet a (multiplier a 0 n) x =
      (2*(a:ℂ)*(2*(n:ℂ)+1))*packet a (multiplier a 0 n) x := by
  rw [oscillator_conjugation,multiplier_eigenvalue a ha n]
  simp only [packet,eval_mul,eval_C,mul_assoc]

/-- Every derivative stays in L2: the differential calculation has actual domains. -/
theorem derivative_memLp (a : ℝ) (ha : 0 < a) (P : Polynomial ℂ) (k : ℕ) :
    MemLp (deriv^[k] (packet a P)) 2 volume := by
  have he : ∀ (k : ℕ) (P : Polynomial ℂ),
      deriv^[k] (packet a P) = packet a ((step a)^[k] P) := by
    intro k
    induction k with
    | zero => intro P; rfl
    | succ k ih =>
      intro P
      rw [Function.iterate_succ_apply',ih,deriv_packet,Function.iterate_succ_apply']
  rw [he]
  exact packet_memLp a ha _

#print axioms packet_memLp
#print axioms packet_derivative
#print axioms polynomialState_ne_zero
#print axioms oscillator_conjugation
#print axioms hermite_equation
#print axioms derivative_memLp
end
end UnifiedTheory.Audit.KFCausalHermiteOscillatorFunctions
