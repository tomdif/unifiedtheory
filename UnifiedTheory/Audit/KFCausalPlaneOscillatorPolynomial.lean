/- The two-dimensional oscillator differential expression on the actual
polynomial Gaussian domain. Its symmetry is inherited from scalar integration
by parts, rather than assumed from the desired eigenvalues. -/
import UnifiedTheory.Audit.KFCausalPlanePolynomialGaussian
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPlaneOscillatorPolynomial
noncomputable section
open MeasureTheory MvPolynomial
open KFCausalPlanePolynomialGaussian
open KFCausalGaussianPolynomialTotality (polynomialState)
open KFCausalHermiteOscillatorPolynomial (oscillator)

def axis (a : ℂ) (i : Fin 2) : Poly →ₗ[ℂ] Poly where
  toFun P := -pderiv i (pderiv i P) + C (4*a)*X i*pderiv i P + C (2*a)*P
  map_add' P Q := by simp only [map_add]; ring
  map_smul' z P := by simp only [smul_eq_C_mul, pderiv_C_mul, RingHom.id_apply]; ring

theorem pderiv_univariate (P : Polynomial ℂ) (i j : Fin 2) :
    pderiv i (Polynomial.aeval (X j : Poly) P) =
      if i = j then Polynomial.aeval (X j : Poly) P.derivative else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq]
    split_ifs <;> simp
  | monomial n z =>
    by_cases hij : i = j
    · subst j
      simp [Polynomial.aeval_monomial, Polynomial.derivative_monomial,
        pderiv_C_mul, pderiv_pow]
      ring
    · simp [Polynomial.aeval_monomial, pderiv_C_mul, pderiv_pow,
        pderiv_X_of_ne (Ne.symm hij), hij]

theorem pderiv_separable_zero (P Q : Polynomial ℂ) :
    pderiv 0 (separable P Q) = separable P.derivative Q := by
  simp [separable, pderiv_mul, pderiv_univariate, mul_comm]

theorem pderiv_separable_one (P Q : Polynomial ℂ) :
    pderiv 1 (separable P Q) = separable P Q.derivative := by
  simp [separable, pderiv_mul, pderiv_univariate]

theorem axis_separable_zero (a : ℂ) (P Q : Polynomial ℂ) :
    axis a 0 (separable P Q) = separable (oscillator a P) Q := by
  simp only [axis, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pderiv_separable_zero, pderiv_separable_zero]
  simp only [separable, oscillator, map_add, map_neg, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, MvPolynomial.algebraMap_eq, map_ofNat]
  ring

theorem axis_separable_one (a : ℂ) (P Q : Polynomial ℂ) :
    axis a 1 (separable P Q) = separable P (oscillator a Q) := by
  simp only [axis, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pderiv_separable_one, pderiv_separable_one]
  simp only [separable, oscillator, map_add, map_neg, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, MvPolynomial.algebraMap_eq, map_ofNat]
  ring

theorem separable_inner (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (P Q R S : Polynomial ℂ) :
    inner ℂ (state a b ha hb (separable P Q)) (state a b ha hb (separable R S)) =
      inner ℂ (polynomialState a ha P) (polynomialState a ha R) *
        inner ℂ (polynomialState b hb Q) (polynomialState b hb S) := by
  rw [separable_state, separable_state, LinearIsometryEquiv.inner_map_map,
    KFCausalL2TensorEmbedding.productState_inner,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

theorem monomial_separable (d : Fin 2 →₀ ℕ) (z : ℂ) :
    monomial d z = separable (Polynomial.monomial (d 0) z)
      (Polynomial.monomial (d 1) 1) := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  simp only [separable, Polynomial.aeval_monomial, X_pow_eq_monomial,
    MvPolynomial.algebraMap_eq, map_one, one_mul]
  rw [C_mul_monomial, monomial_mul]
  simp

theorem axis_symmetric (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i : Fin 2)
    (P Q : Poly) :
    inner ℂ (state a b ha hb (axis (if i = 0 then (a:ℂ) else (b:ℂ)) i P))
      (state a b ha hb Q) =
    inner ℂ (state a b ha hb P)
      (state a b ha hb (axis (if i = 0 then (a:ℂ) else (b:ℂ)) i Q)) := by
  induction P using MvPolynomial.induction_on' with
  | add P R hp hr => simp only [map_add, inner_add_left, hp, hr]
  | monomial d z =>
    induction Q using MvPolynomial.induction_on' with
    | add Q R hq hr => simp only [map_add, inner_add_right, hq, hr]
    | monomial e w =>
      rw [monomial_separable, monomial_separable]
      fin_cases i
      · simp [axis_separable_zero, separable_inner,
          KFCausalHermiteHilbertBasis.oscillator_symmetric]
      · simp [axis_separable_one, separable_inner,
          KFCausalHermiteHilbertBasis.oscillator_symmetric]

#print axioms axis_separable_zero
#print axioms axis_symmetric
end
end UnifiedTheory.Audit.KFCausalPlaneOscillatorPolynomial
