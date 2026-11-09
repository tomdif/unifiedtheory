/- The formal polynomial oscillator is the actual second directional
derivative of its smooth Gaussian representative. -/
import UnifiedTheory.Audit.KFCausalCircularOscillatorBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPlaneOscillatorFunctions
noncomputable section
open MvPolynomial MeasureTheory
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPlanePolynomialGaussian (Poly packet packet_memLp)
open KFCausalGaussianSliceDomain (gaussian)
open KFCausalPlaneOscillatorPolynomial (axis)

def shift (i : Fin 2) (x : Block 2) (t : ℝ) : Block 2 :=
  WithLp.toLp 2 (fun j => x j + if j = i then t else 0)

theorem shift_zero (i : Fin 2) (x : Block 2) : shift i x 0 = x := by
  ext j
  simp [shift]

theorem eval_derivative (P : Poly) (i : Fin 2) (x : Block 2) :
    HasDerivAt (fun t : ℝ => eval (fun j => (shift i x t j:ℂ)) P)
      (eval (fun j => (x j:ℂ)) (pderiv i P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C z => simpa [pderiv_C] using hasDerivAt_const (0:ℝ) z
  | add P Q hp hq => simpa only [map_add] using hp.add hq
  | mul_X P j hp =>
    have hx : HasDerivAt (fun t : ℝ => (shift i x t j:ℂ))
        (if j = i then (1:ℂ) else 0) 0 := by
      by_cases hj : j = i
      · simpa [shift, hj] using ((hasDerivAt_id (0:ℝ)).const_add (x j)).ofReal_comp
      · simpa [shift, hj] using hasDerivAt_const (0:ℝ) (x j:ℂ)
    convert hp.mul hx using 1
    · ext t
      simp only [eval_mul, eval_X, Pi.mul_apply]
    · simp [pderiv_mul, shift_zero, pderiv_X, Pi.single_apply]
      split_ifs <;> (try simp only [map_zero]) <;> ring

def step (a : ℂ) (i : Fin 2) (P : Poly) : Poly := pderiv i P-C (2*a)*X i*P

theorem gaussian_derivative (a b : ℝ) (i : Fin 2) (x : Block 2) :
    HasDerivAt (fun t : ℝ => gaussian a (shift i x t 0)*gaussian b (shift i x t 1))
      (-2*(if i = 0 then (a:ℂ) else (b:ℂ))*(x i:ℂ)*
        (gaussian a (x 0)*gaussian b (x 1))) 0 := by
  fin_cases i
  · have h := ((((hasDerivAt_id (0:ℝ)).const_add (x 0)).ofReal_comp.pow 2).const_mul
      (-(a:ℂ))).cexp.mul_const (gaussian b (x 1))
    convert h using 1 <;> simp [shift, gaussian] <;> ring
  · have h := ((((hasDerivAt_id (0:ℝ)).const_add (x 1)).ofReal_comp.pow 2).const_mul
      (-(b:ℂ))).cexp.const_mul (gaussian a (x 0))
    convert h using 1 <;> simp [shift, gaussian] <;> ring

theorem packet_derivative (a b : ℝ) (P : Poly) (i : Fin 2) (x : Block 2) :
    HasDerivAt (fun t : ℝ => packet a b P (shift i x t))
      (packet a b (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P) x) 0 := by
  convert (eval_derivative P i x).mul (gaussian_derivative a b i x) using 1
  simp only [packet, step, eval_sub, eval_mul, eval_C, eval_X, shift_zero]
  ring

def differential (i : Fin 2) (F : Block 2 → ℂ) (x : Block 2) : ℂ :=
  deriv (fun t => F (shift i x t)) 0

theorem differential_packet (a b : ℝ) (P : Poly) (i : Fin 2) :
    differential i (packet a b P) =
      packet a b (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P) :=
  funext (fun x => (packet_derivative a b P i x).deriv)

theorem axis_step (a : ℂ) (i : Fin 2) (P : Poly) :
    axis a i P = -step a i (step a i P)+C (4*a^2)*X i^2*P := by
  simp only [axis, LinearMap.coe_mk, AddHom.coe_mk, step, map_sub,
    pderiv_mul, pderiv_C, pderiv_X_self, zero_mul, zero_add, mul_one]
  simp only [map_mul, map_pow, map_ofNat]
  ring

theorem oscillator_equation (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (n : ℕ)
    (x : Block 2) :
    let F := packet (b*c^2) b (KFCausalCircularOscillatorBasis.normalizedPolynomial c hc b hb n);
    -differential 0 (differential 0 F) x-(c:ℂ)^2*differential 1 (differential 1 F) x+
      (4*(b:ℂ)^2*(c:ℂ)^4*(x 0:ℂ)^2+4*(b:ℂ)^2*(c:ℂ)^2*(x 1:ℂ)^2)*F x =
        (KFCausalCircularOscillatorTriangular.energy c b n:ℂ)*F x := by
  dsimp only
  rw [differential_packet, differential_packet, differential_packet, differential_packet]
  have he := congrArg (fun P => packet (b*c^2) b P x)
    (KFCausalCircularOscillatorBasis.polynomial_eigenvalue c hc b hb n)
  simp only [KFCausalCircularOscillatorPolynomial.oscillator, LinearMap.add_apply,
    LinearMap.smul_apply, axis_step, packet, eval_add, eval_neg, eval_mul,
    eval_C, eval_X, eval_pow, smul_eval, smul_eq_mul] at he
  simp only [packet, Complex.ofReal_mul, Complex.ofReal_pow, ↓reduceIte,
    show (1:Fin 2) ≠ 0 by decide] at he ⊢
  linear_combination he

#print axioms packet_derivative
#print axioms oscillator_equation
end
end UnifiedTheory.Audit.KFCausalPlaneOscillatorFunctions
