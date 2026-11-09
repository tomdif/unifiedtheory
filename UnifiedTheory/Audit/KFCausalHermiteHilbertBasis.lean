/- A scalar Hermite Hilbert basis, constructed from integration by parts,
the proved oscillator equation and Gaussian completeness. -/
import UnifiedTheory.Audit.KFCausalHermiteOscillatorFunctions
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHermiteHilbertBasis
noncomputable section
open MeasureTheory Polynomial
open KFCausalGaussianPolynomialTotality (ScalarHilbert polynomialState polynomialState_coe)
open KFCausalHermiteOscillatorFunctions
open KFCausalHermiteOscillatorPolynomial (oscillator multiplier_eigenvalue)
open KFCausalNeutralHermiteDomain (multiplier)
open KFCausalHermiteL2Completeness (state)

theorem inner_eq_integral (a : ℝ) (ha : 0 < a) (P Q : Polynomial ℂ) :
    inner ℂ (polynomialState a ha P) (polynomialState a ha Q) =
      ∫ x : ℝ, star (packet a P x)*packet a Q x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialState_coe a ha P,polynomialState_coe a ha Q] with x hp hq
  rw [hp,hq,RCLike.inner_apply']
  rfl

private theorem cross_integrable (a : ℝ) (ha : 0 < a) (P Q : Polynomial ℂ) :
    Integrable (fun x => star (packet a P x)*packet a Q x) :=
  (packet_memLp a ha P).star.integrable_mul (packet_memLp a ha Q)

theorem step_skew (a : ℝ) (ha : 0 < a) (P Q : Polynomial ℂ) :
    inner ℂ (polynomialState a ha P) (polynomialState a ha (step a Q)) =
      -inner ℂ (polynomialState a ha (step a P)) (polynomialState a ha Q) := by
  rw [inner_eq_integral,inner_eq_integral]
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x => (packet_derivative a P x).star) (packet_derivative a Q)
    (cross_integrable a ha P (step a Q)) (cross_integrable a ha (step a P) Q)
    (cross_integrable a ha P Q)

private theorem oscillator_step (a : ℝ) (P : Polynomial ℂ) :
    oscillator (a:ℂ) P = -step a (step a P)+C (4*(a:ℂ)^2)*X^2*P := by
  simp only [oscillator,step,derivative_sub,derivative_mul,derivative_C,derivative_X,
    derivative_ofNat,zero_mul,zero_add,mul_one,map_mul,map_ofNat,map_pow]
  ring

private theorem potential_symmetric (a : ℝ) (ha : 0 < a) (P Q : Polynomial ℂ) :
    inner ℂ (polynomialState a ha P) (polynomialState a ha (C (4*(a:ℂ)^2)*X^2*Q)) =
      inner ℂ (polynomialState a ha (C (4*(a:ℂ)^2)*X^2*P)) (polynomialState a ha Q) := by
  rw [inner_eq_integral,inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [packet,eval_mul,eval_C,eval_pow,eval_X,star_mul,star_pow,
    star_ofNat,Complex.star_def,Complex.conj_ofReal]
  ring

theorem oscillator_symmetric (a : ℝ) (ha : 0 < a) (P Q : Polynomial ℂ) :
    inner ℂ (polynomialState a ha P) (polynomialState a ha (oscillator (a:ℂ) Q)) =
      inner ℂ (polynomialState a ha (oscillator (a:ℂ) P)) (polynomialState a ha Q) := by
  rw [oscillator_step,oscillator_step]
  simp only [map_add,map_neg,inner_add_right,inner_add_left,inner_neg_right,inner_neg_left]
  rw [potential_symmetric,step_skew a ha P (step a Q),step_skew a ha (step a P) Q]
  simp only [neg_neg]

theorem state_orthogonal (a : ℝ) (ha : 0 < a) {n m : ℕ} (hnm : n ≠ m) :
    inner ℂ (state a ha a 0 n) (state a ha a 0 m) = 0 := by
  have hs := oscillator_symmetric a ha (multiplier a 0 n) (multiplier a 0 m)
  rw [multiplier_eigenvalue a ha n,multiplier_eigenvalue a ha m] at hs
  simp only [← smul_eq_C_mul,map_smul,inner_smul_right,inner_smul_left] at hs
  simp only [map_mul,map_add,map_ofNat,map_natCast,Complex.conj_ofReal,map_one] at hs
  have he : (2*(a:ℂ)*(2*(m:ℂ)+1)-2*(a:ℂ)*(2*(n:ℂ)+1)) ≠ 0 := by
    intro hz
    have ha' : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hm : (m:ℂ) = (n:ℂ) := by
      apply mul_left_cancel₀ (show (4:ℂ)*(a:ℂ) ≠ 0 by exact mul_ne_zero (by norm_num) ha')
      linear_combination hz
    exact hnm (Nat.cast_injective hm.symm)
  apply (mul_eq_zero.mp (show
      (2*(a:ℂ)*(2*(m:ℂ)+1)-2*(a:ℂ)*(2*(n:ℂ)+1))*
        inner ℂ (state a ha a 0 n) (state a ha a 0 m) = 0 from by
      change _ * inner ℂ (polynomialState a ha (multiplier a 0 n))
        (polynomialState a ha (multiplier a 0 m)) = 0
      linear_combination hs)).resolve_left he

theorem state_ne_zero (a : ℝ) (ha : 0 < a) (n : ℕ) : state a ha a 0 n ≠ 0 := by
  apply polynomialState_ne_zero
  exact (KFCausalNeutralHermiteBasis.sequence a 0 ha).ne_zero n

def normalizedState (a : ℝ) (ha : 0 < a) (n : ℕ) : ScalarHilbert :=
  ((‖state a ha a 0 n‖⁻¹:ℝ):ℂ) • state a ha a 0 n

theorem orthonormal (a : ℝ) (ha : 0 < a) : Orthonormal ℂ (normalizedState a ha) := by
  constructor
  · intro n
    simp only [normalizedState,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
      abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (state_ne_zero a ha n))]
  · intro n m hnm
    simp only [normalizedState,inner_smul_left,inner_smul_right,state_orthogonal a ha hnm,
      mul_zero]

theorem normalized_dense_span (a : ℝ) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (normalizedState a ha))).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← KFCausalHermiteL2Completeness.oscillator_dense_span a ha]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n,rfl⟩
  have hn := Submodule.smul_mem (Submodule.span ℂ (Set.range (normalizedState a ha)))
    (‖state a ha a 0 n‖:ℂ) (Submodule.subset_span ⟨n,rfl⟩)
  simpa only [normalizedState,smul_smul,← Complex.ofReal_mul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (state_ne_zero a ha n)),Complex.ofReal_one,one_smul] using hn

/-- A genuine scalar unitary Hermite expansion, derived without spectral assumptions. -/
def basis (a : ℝ) (ha : 0 < a) : HilbertBasis ℕ ℂ ScalarHilbert :=
  HilbertBasis.mk (orthonormal a ha) (by rw [normalized_dense_span])

theorem basis_apply (a : ℝ) (ha : 0 < a) (n : ℕ) :
    basis a ha n = normalizedState a ha n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

theorem expansion (a : ℝ) (ha : 0 < a) (f : ScalarHilbert) :
    HasSum (fun n => inner ℂ (normalizedState a ha n) f • normalizedState a ha n) f := by
  simpa only [HilbertBasis.repr_apply_apply,basis_apply] using (basis a ha).hasSum_repr f

def transform (a : ℝ) (ha : 0 < a) : ScalarHilbert ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ) :=
  (basis a ha).repr

theorem transform_apply (a : ℝ) (ha : 0 < a) (f : ScalarHilbert) (n : ℕ) :
    transform a ha f n = inner ℂ (normalizedState a ha n) f := by
  exact ((basis a ha).repr_apply_apply f n).trans (congrArg (fun u => inner ℂ u f)
    (basis_apply a ha n))

/-- On the dense polynomial Gaussian domain, the actual differential expression
is diagonalized by the unitary transform. This does not assert a maximal domain. -/
theorem transform_oscillator (a : ℝ) (ha : 0 < a) (P : Polynomial ℂ) (n : ℕ) :
    transform a ha (polynomialState a ha (oscillator (a:ℂ) P)) n =
      (2*(a:ℂ)*(2*(n:ℂ)+1))*transform a ha (polynomialState a ha P) n := by
  have hs := oscillator_symmetric a ha (multiplier a 0 n) P
  rw [multiplier_eigenvalue a ha n] at hs
  simp only [← smul_eq_C_mul,map_smul,inner_smul_left] at hs
  simp only [map_mul,map_add,map_ofNat,map_natCast,Complex.conj_ofReal,map_one] at hs
  simp only [transform_apply,normalizedState,inner_smul_left,state]
  rw [hs]
  ring

#print axioms step_skew
#print axioms oscillator_symmetric
#print axioms state_orthogonal
#print axioms orthonormal
#print axioms normalized_dense_span
#print axioms basis
#print axioms expansion
#print axioms transform
#print axioms transform_oscillator
end
end UnifiedTheory.Audit.KFCausalHermiteHilbertBasis
