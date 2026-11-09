/- The kinetic part of the polynomial Gaussian oscillator agrees with
the actual L2 Fourier multiplier, including the 2*pi normalization. -/
import UnifiedTheory.Audit.KFCausalPlaneOscillatorFunctions
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPlaneKineticFourier
noncomputable section
open MeasureTheory MvPolynomial
open KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open KFCausalPlanePolynomialGaussian (Poly state state_coe packet packet_memLp)
open KFCausalPlaneOscillatorFunctions (step shift packet_derivative)

def vector (i : Fin 2) : Block 2 := WithLp.toLp 2 (Pi.single i 1)

theorem shift_eq (i : Fin 2) (x : Block 2) (t : ℝ) : shift i x t = x+t • vector i := by
  ext j
  by_cases hj : j = i <;> simp [shift, vector, Pi.single_apply, hj]

theorem inner_vector (i : Fin 2) (x : Block 2) : inner ℝ x (vector i) = x i := by
  fin_cases i <;> simp [vector, PiLp.inner_apply, Fin.sum_univ_two, Pi.single_apply]

theorem state_eq_toLp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P : Poly) :
    state a b ha hb P = (packet_memLp a b ha hb P).toLp (packet a b P) :=
  Lp.ext ((state_coe a b ha hb P).trans (packet_memLp a b ha hb P).coeFn_toLp.symm)

theorem derivative_fourier (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P : Poly) (i : Fin 2) :
    (Lp.fourierTransformₗᵢ (Block 2) ℂ)
      (state a b ha hb (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P)) =ᵐ[volume]
        fun x => (2*(Real.pi:ℂ)*Complex.I)*(x i:ℂ)*
          ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (state a b ha hb P)) x := by
  have hd (x : Block 2) : HasLineDerivAt ℝ (packet a b P)
      (packet a b (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P) x) x (vector i) := by
    change HasDerivAt (fun t => packet a b P (x+t • vector i)) _ 0
    simpa only [shift_eq] using packet_derivative a b P i x
  have he := KFCausalL2DirectionalDerivative.derivative_fourier (packet a b P)
    (packet a b (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P)) (vector i)
    (packet_memLp a b ha hb P) (packet_memLp a b ha hb _) hd
  rw [state_eq_toLp a b ha hb (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P),
    state_eq_toLp a b ha hb P]
  simpa only [inner_vector] using he

theorem second_fourier (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (P : Poly) (i : Fin 2) :
    (Lp.fourierTransformₗᵢ (Block 2) ℂ)
      (state a b ha hb (step (if i = 0 then (a:ℂ) else (b:ℂ)) i
        (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P))) =ᵐ[volume]
      fun x => -(4*(Real.pi:ℂ)^2*(x i:ℂ)^2)*
        ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (state a b ha hb P)) x := by
  filter_upwards [derivative_fourier a b ha hb (step (if i = 0 then (a:ℂ) else (b:ℂ)) i P) i,
    derivative_fourier a b ha hb P i] with x h1 h2
  rw [h1, h2]
  have hI := Complex.I_sq
  linear_combination 4*(Real.pi:ℂ)^2*(x i:ℂ)^2*
    (((Lp.fourierTransformₗᵢ (Block 2) ℂ) (state a b ha hb P)) x)*hI

def kinetic (c b : ℝ) (P : Poly) : Poly :=
  -step ((b:ℂ)*(c:ℂ)^2) 0 (step ((b:ℂ)*(c:ℂ)^2) 0 P) -
    C ((c:ℂ)^2)*step (b:ℂ) 1 (step (b:ℂ) 1 P)

def potential (c b : ℝ) (P : Poly) : Poly :=
  (C (4*(b:ℂ)^2*(c:ℂ)^4)*X 0^2+C (4*(b:ℂ)^2*(c:ℂ)^2)*X 1^2)*P

theorem oscillator_split (c b : ℝ) (P : Poly) :
    KFCausalCircularOscillatorPolynomial.oscillator c b P = kinetic c b P+potential c b P := by
  simp only [KFCausalCircularOscillatorPolynomial.oscillator, LinearMap.add_apply,
    LinearMap.smul_apply, KFCausalPlaneOscillatorFunctions.axis_step, kinetic, potential,
    smul_eq_C_mul, map_mul, map_pow, map_ofNat]
  ring

theorem kinetic_fourier (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (P : Poly) :
    (Lp.fourierTransformₗᵢ (Block 2) ℂ)
      (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
        (kinetic c b P)) =ᵐ[volume] fun x =>
      (4*(Real.pi:ℂ)^2*((x 0:ℂ)^2+(c:ℂ)^2*(x 1:ℂ)^2))*
        ((Lp.fourierTransformₗᵢ (Block 2) ℂ)
          (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P)) x := by
  let J := state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
  let F := Lp.fourierTransformₗᵢ (Block 2) ℂ
  let P0 := step ((b:ℂ)*(c:ℂ)^2) 0 (step ((b:ℂ)*(c:ℂ)^2) 0 P)
  let P1 := step (b:ℂ) 1 (step (b:ℂ) 1 P)
  have h0 : F (J P0) =ᵐ[volume] fun x =>
      -(4*(Real.pi:ℂ)^2*(x 0:ℂ)^2)*(F (J P)) x := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, ↓reduceIte] using
      second_fourier (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P 0
  have h1 : F (J P1) =ᵐ[volume] fun x =>
      -(4*(Real.pi:ℂ)^2*(x 1:ℂ)^2)*(F (J P)) x := by
    simpa using
      second_fourier (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P 1
  have hm : F (J (kinetic c b P)) = -F (J P0)-(c:ℂ)^2 • F (J P1) := by
    simp only [kinetic, ← smul_eq_C_mul, map_sub, map_neg, map_smul, P0, P1]
  change F (J (kinetic c b P)) =ᵐ[volume] _
  rw [hm]
  filter_upwards [Lp.coeFn_sub (-F (J P0)) ((c:ℂ)^2 • F (J P1)),
    Lp.coeFn_neg (F (J P0)), Lp.coeFn_smul ((c:ℂ)^2) (F (J P1)), h0, h1]
      with x hs hn hc' h0' h1'
  simp only [hs, Pi.sub_apply, hn, Pi.neg_apply, hc', Pi.smul_apply, smul_eq_mul, h0', h1']
  ring

theorem potential_coe (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b) (P : Poly) :
    state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
      (potential c b P) =ᵐ[volume] fun x =>
        (4*(b:ℂ)^2*(c:ℂ)^4*(x 0:ℂ)^2+4*(b:ℂ)^2*(c:ℂ)^2*(x 1:ℂ)^2)*
          (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P) x := by
  filter_upwards [state_coe (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
    (potential c b P), state_coe (b*c^2) b
      (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P] with x hx hy
  rw [hx, hy]
  simp only [packet, potential, eval_mul, eval_add, eval_C, eval_pow, eval_X]
  ring

#print axioms derivative_fourier
#print axioms second_fourier
#print axioms kinetic_fourier
#print axioms potential_coe
end
end UnifiedTheory.Audit.KFCausalPlaneKineticFourier
