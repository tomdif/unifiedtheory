/- An unconditional full-clock potential response bound for finite
reciprocal superpositions with independent positive clock widths.
Actual L2 outputs supply integrability; the matrix rate bound and exact
clock transport supply the inequality, including endpoint control. -/
import UnifiedTheory.Audit.KFCausalFiniteClockKernel
import UnifiedTheory.Audit.KFCausalMatrixClockIntegral
import UnifiedTheory.Audit.KFCausalReciprocalGramUniformResponse
import UnifiedTheory.Audit.KFCausalReciprocalCrossPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalSuperpositionClockResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalFiniteClockKernel (form)
open KFCausalClockResponseTransport (clock coefficient)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalCrossGram (pairing)
open KFCausalReciprocalCrossPhysical (coefficients momentumCoefficients)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

def matrix (n : ℕ) (ε h : ℝ) (w : Fin n → ℝ) (s : ℝ) (i j : Fin n) : ℂ :=
  KFCausalReciprocalCrossResponse.actualKernel (groundWidth h) (neutralWidth h) ε (-h/2) (w i) (w j) s

def energy (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  (pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
    (coefficients n ε h a c s) (coefficients n ε h a c s)).re
def response (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  (-2/h)*(pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
    (coefficients n ε h a c s) (momentumCoefficients n ε h a c s)).im
def rate (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  KFCausalReciprocalGramUniformResponse.slope n (groundWidth h) (neutralWidth h) ε (-h/2) w
    (coefficients n ε h a c s) s

private theorem smaller_shift (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) : |-h/2| ≤ Real.pi*ε/6 := by
  rw [abs_div,abs_neg]
  norm_num
  linarith

theorem matrix_hermitian (n : ℕ) (ε h : ℝ) (w : Fin n → ℝ) (s : ℝ) (i j : Fin n) :
    conj (matrix n ε h w s i j) = matrix n ε h w s j i :=
  KFCausalReciprocalCrossGram.kernel_conj _ _ _ _ _

theorem matrix_derivative (n : ℕ) (ε h : ℝ) (w : Fin n → ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
    (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u => matrix n ε h w u i j) (deriv (fun u => matrix n ε h w u i j) s) s :=
  KFCausalReciprocalCrossResponse.actual_derivative _ _ ε (-h/2) (w i) (w j) s
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) (hw i) (hw j)

theorem response_weak (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (s : ℝ) (hh : h ≠ 0) : response n ε h a w c s =
      2*(form n (matrix n ε h w s) (KFCausalFiniteClockKernel.coefficients n ε (-h/2) a c s)
        (KFCausalFiniteClockKernel.weakCoefficients n ε (-h/2) a c s)).re := by
  have hm : momentumCoefficients n ε h a c s = fun i =>
      (-Complex.I*(h:ℂ))*KFCausalFiniteClockKernel.weakCoefficients n ε (-h/2) a c s i := by
    funext i
    unfold momentumCoefficients KFCausalFiniteClockKernel.weakCoefficients
    change (-Complex.I*(h:ℂ))*_*(coefficients n ε h a c s i) =
      (-Complex.I*(h:ℂ))*(_*coefficients n ε h a c s i)
    ring
  change (-2/h)*(form n (matrix n ε h w s)
    (KFCausalFiniteClockKernel.coefficients n ε (-h/2) a c s) (momentumCoefficients n ε h a c s)).im = _
  rw [hm,KFCausalFiniteClockKernel.form_const_right]
  norm_num [Complex.mul_re,Complex.mul_im]
  field_simp

theorem boundary_derivative (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (fun u => energy n ε h a w c u/clock ε u)
      (response n ε h a w c s-coefficient ε (-h/2) s*energy n ε h a w c s+
        rate n ε h a w c s/clock ε s) s := by
  rw [response_weak n ε h a w c s hh]
  exact KFCausalFiniteClockKernel.boundary_real_derivative n ε (-h/2) a c
    (matrix n ε h w) (fun i j => deriv (fun u => matrix n ε h w u i j) s) s hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
    (matrix_derivative n ε h w hε hh hw hb s) (matrix_hermitian n ε h w s)

theorem energy_nonnegative (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    0 ≤ energy n ε h a w c s :=
  KFCausalReciprocalGramUniformResponse.gram_nonnegative n (groundWidth h) (neutralWidth h) ε (-h/2) w
    (coefficients n ε h a c s) (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) hw s

theorem energy_integrable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) : Integrable (energy n ε h a w c) :=
  KFCausalReciprocalCrossPhysical.clock_energy_integrable n ε h a w c hε ha hh hw hb

theorem response_integrable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) : Integrable (response n ε h a w c) :=
  (KFCausalReciprocalCrossPhysical.clock_pairing_integrable n ε h a w c hε ha hh hw hb).im.const_mul (-2/h)

theorem response_integral (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    (∫ s, response n ε h a w c s) = (-2/h)*(∫ x, KFCausalReciprocalCrossPhysical.potentialPair n ε h a w c x).im := by
  unfold response
  have him := integral_im (KFCausalReciprocalCrossPhysical.clock_pairing_integrable n ε h a w c hε ha hh hw hb)
  simp only [RCLike.im_eq_complex_im] at him
  rw [integral_const_mul,him,
    ← KFCausalReciprocalCrossPhysical.potentialPair_clock_integral n ε h a w c hε ha hh hw hb]

theorem exists_uniform_full_clock_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ),
      0 < ε → (∀ i, 0 < a i) → h ≠ 0 → (∀ i, 1 ≤ w i) → |h| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*(∫ s, energy n ε h a w c s) ≤ ∫ s, response n ε h a w c s := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalGramUniformResponse.exists_uniform_matrix_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb
  have hb' : |h| ≤ 2*Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  apply KFCausalMatrixClockIntegral.full_clock_bound ε (-h/2) C
    (energy n ε h a w c) (response n ε h a w c) (rate n ε h a w c) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb') hC
    (energy_integrable n ε h a w c hε ha hh hw hb')
    (response_integrable n ε h a w c hε ha hh hw hb')
    (energy_nonnegative n ε h a w c hε hh hw hb')
    (boundary_derivative n ε h a w c hε hh hw hb')
  intro s
  exact hbound n (groundWidth h) (neutralWidth h) ε (-h/2) w (coefficients n ε h a c s)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε
    (smaller_shift ε h hb) (by simpa using hh) hw s

theorem exists_uniform_potential_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ),
      0 < ε → (∀ i, 0 < a i) → h ≠ 0 → (∀ i, 1 ≤ w i) → |h| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*(∫ x, KFCausalReciprocalCrossPhysical.energyDensity n ε h a w c x) ≤
        (-2/h)*(∫ x, KFCausalReciprocalCrossPhysical.potentialPair n ε h a w c x).im := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_full_clock_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb
  have hb' : |h| ≤ 2*Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  have hi := hbound n ε h a w c hε ha hh hw hb
  rw [response_integral n ε h a w c hε ha hh hw hb'] at hi
  rw [KFCausalReciprocalCrossPhysical.energyDensity_clock_integral n ε h a w c hε ha hh hw hb']
  exact hi

#print axioms matrix_hermitian
#print axioms matrix_derivative
#print axioms response_weak
#print axioms boundary_derivative
#print axioms energy_nonnegative
#print axioms energy_integrable
#print axioms response_integrable
#print axioms response_integral
#print axioms exists_uniform_full_clock_response
#print axioms exists_uniform_potential_response
end
end UnifiedTheory.Audit.KFCausalReciprocalSuperpositionClockResponse
