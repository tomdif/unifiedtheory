/- Weighted L2 domains for every finite Gaussian exponential-polynomial
profile on a real line. Complex translations and polynomial derivatives
stay in this class; no degree or coefficient cutoff is imposed. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHolomorphic
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralLinePackets
noncomputable section
open MeasureTheory

def entire (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-(β:ℂ)*z^2+b*z)*P.eval z
def packet (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ := entire β b P (x:ℂ)
def monomial (β : ℝ) (b : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x:ℂ)^n*Complex.exp (-(β:ℂ)*(x:ℂ)^2+b*(x:ℂ))
def step (β : ℝ) (b : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P.derivative+(Polynomial.C b-Polynomial.C (2*(β:ℂ))*Polynomial.X)*P

theorem monomial_norm (β : ℝ) (b : ℂ) (n : ℕ) (x : ℝ) :
    ‖monomial β b n x‖ = |x|^n*Real.exp (-β*x^2+b.re*x) := by
  simp [monomial,norm_pow,Complex.norm_exp,Complex.mul_re,Complex.mul_im,pow_two]

theorem source_exponent_bound (β : ℝ) (hβ : 0 < β) (b x : ℝ) :
    -β*x^2+b*x ≤ b^2/(2*β)-(β/2)*x^2 := by
  have hn := sq_nonneg (β*x-b)
  have hd : 0 < 2*β := by positivity
  have he : (β/2)*x^2+b*x-β*x^2 ≤ b^2/(2*β) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  linarith

theorem monomial_integrable (β : ℝ) (hβ : 0 < β) (b : ℂ) (n : ℕ) :
    Integrable (monomial β b n) := by
  have hi := (KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable (β/2) (by positivity) n).norm.const_mul
    (Real.exp (b.re^2/(2*β)))
  apply hi.mono' (by unfold monomial; fun_prop)
  filter_upwards [] with x
  rw [monomial_norm]
  have he := Real.exp_le_exp.mpr (source_exponent_bound β hβ b.re x)
  rw [Real.exp_sub] at he
  have hn : ‖x^n*Real.exp (-(β/2)*x^2)‖ = |x|^n*Real.exp (-(β/2)*x^2) := by
    rw [norm_mul,Real.norm_eq_abs,abs_pow,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [hn]
  have hh := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg x) n)
  rw [div_eq_mul_inv,← Real.exp_neg] at hh
  simpa only [neg_mul,mul_left_comm,mul_assoc] using hh

theorem monomial_norm_square (β : ℝ) (b : ℂ) (n : ℕ) (x : ℝ) :
    ‖monomial β b n x‖^2 = ‖monomial (2*β) (2*b) (2*n) x‖ := by
  rw [monomial_norm,monomial_norm,mul_pow,← Real.exp_nat_mul,← pow_mul]
  simp only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [Nat.mul_comm n 2]
  congr 2
  ring

theorem monomial_memLp (β : ℝ) (hβ : 0 < β) (b : ℂ) (n : ℕ) :
    MemLp (monomial β b n) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold monomial; fun_prop)).mpr
  simpa only [monomial_norm_square] using (monomial_integrable (2*β) (by positivity) (2*b) (2*n)).norm

theorem packet_expansion (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    packet β b P x = ∑ n ∈ P.support, P.coeff n*monomial β b n x := by
  simp only [packet,entire,Polynomial.eval_eq_sum,Polynomial.sum,Finset.mul_sum,monomial]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem packet_memLp (β : ℝ) (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ) :
    MemLp (packet β b P) 2 volume := by
  have hi := memLp_finset_sum P.support (fun n _ => (monomial_memLp β hβ b n).const_mul (P.coeff n))
  change MemLp (fun x => packet β b P x) 2 volume
  simpa only [packet_expansion] using hi

theorem packet_polynomial (β : ℝ) (b : ℂ) (P Q : Polynomial ℂ) (x : ℝ) :
    Q.eval (x:ℂ)*packet β b P x = packet β b (Q*P) x := by
  simp only [packet,entire,Polynomial.eval_mul]
  ring

theorem entire_derivative (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (entire β b P) (entire β b (step β b P) z) z := by
  have he := ((((hasDerivAt_id z).pow 2).const_mul (-(β:ℂ))).add
    ((hasDerivAt_id z).const_mul b)).cexp
  convert he.mul (P.hasDerivAt z) using 1
  dsimp [entire,step]
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  ring

theorem packet_derivative (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (packet β b P) (packet β b (step β b P) x) x :=
  (entire_derivative β b P (x:ℂ)).comp_ofReal

def translatedPolynomial (β : ℝ) (b z : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C (Complex.exp (-(β:ℂ)*z^2+b*z))*P.comp (Polynomial.X+Polynomial.C z)

theorem translated_packet (β : ℝ) (b z : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    entire β b P ((x:ℂ)+z) = packet β (b-2*(β:ℂ)*z) (translatedPolynomial β b z P) x := by
  simp only [entire,packet,translatedPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  ring

#print axioms monomial_norm
#print axioms source_exponent_bound
#print axioms monomial_integrable
#print axioms monomial_norm_square
#print axioms monomial_memLp
#print axioms packet_expansion
#print axioms packet_memLp
#print axioms packet_polynomial
#print axioms entire_derivative
#print axioms packet_derivative
#print axioms translated_packet
end
end UnifiedTheory.Audit.KFCausalNeutralLinePackets
