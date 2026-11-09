/- Circular polynomial coordinates and a complete, independent family of
actual Gaussian states. Orthonormalization will preserve their charges. -/
import UnifiedTheory.Audit.KFCausalPlanePolynomialGaussian
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularPolynomialBasis
noncomputable section
open MvPolynomial Module
open KFCausalEuclideanProductCoordinates
open KFCausalPlanePolynomialGaussian (Poly state state_injective state_dense_range packet)

def forward : Poly →ₐ[ℂ] Poly := aeval ![X 0+C Complex.I*X 1,X 0-C Complex.I*X 1]
def backward : Poly →ₐ[ℂ] Poly :=
  aeval ![C (2⁻¹:ℂ)*(X 0+X 1),-C Complex.I*C (2⁻¹:ℂ)*(X 0-X 1)]

private theorem half_twice : (2:Poly)*C (2⁻¹:ℂ) = 1 := by
  rw [← map_ofNat C 2,← map_mul]
  norm_num

private theorem I_square : (C Complex.I : Poly)^2 = -1 := by
  rw [← map_pow,Complex.I_sq,map_neg,map_one]

theorem forward_backward : forward.comp backward = AlgHom.id ℂ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [forward,backward,AlgHom.comp_apply]
  · linear_combination (X 0)*half_twice
  · linear_combination -2*C (2⁻¹:ℂ)*(X 1)*I_square+(X 1)*half_twice

theorem backward_forward : backward.comp forward = AlgHom.id ℂ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [forward,backward,AlgHom.comp_apply]
  · linear_combination -C (2⁻¹:ℂ)*(X 0-X 1)*I_square+(X 0)*half_twice
  · linear_combination C (2⁻¹:ℂ)*(X 0-X 1)*I_square+(X 1)*half_twice

def circularChange : Poly ≃ₐ[ℂ] Poly :=
  AlgEquiv.ofAlgHom forward backward forward_backward backward_forward

def exponent : ℕ ≃ (Fin 2 →₀ ℕ) where
  toFun n := Finsupp.equivFunOnFinite.symm ![(Nat.unpair n).1,(Nat.unpair n).2]
  invFun e := Nat.pair (e 0) (e 1)
  left_inv n := Nat.pair_unpair n
  right_inv e := by ext i; fin_cases i <;> simp [Nat.unpair_pair]

def polynomialBasis : Basis ℕ ℂ Poly :=
  ((MvPolynomial.basisMonomials (Fin 2) ℂ).map circularChange.toLinearEquiv).reindex exponent.symm

theorem polynomialBasis_apply (n : ℕ) :
    polynomialBasis n = forward (monomial (exponent n) 1) := by
  simp only [polynomialBasis,Basis.reindex_apply,Basis.map_apply,MvPolynomial.coe_basisMonomials]
  rfl

def states (a : ℝ) (ha : 0 < a) (n : ℕ) : BlockHilbert 2 := state a a ha ha (polynomialBasis n)

theorem states_independent (a : ℝ) (ha : 0 < a) : LinearIndependent ℂ (states a ha) :=
  polynomialBasis.linearIndependent.map' (state a a ha ha) (LinearMap.ker_eq_bot.mpr (state_injective a a ha ha))

theorem states_span (a : ℝ) (ha : 0 < a) :
    Submodule.span ℂ (Set.range (states a ha)) = (state a a ha ha).range := by
  rw [show Set.range (states a ha) = (state a a ha ha) '' Set.range polynomialBasis from
    Set.range_comp (state a a ha ha) polynomialBasis]
  rw [← Submodule.map_span,polynomialBasis.span_eq,Submodule.map_top]

theorem states_dense (a : ℝ) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (states a ha))).topologicalClosure = ⊤ := by
  rw [states_span,state_dense_range]

def coordinate (x : Block 2) : ℂ := (x 0:ℂ)+Complex.I*(x 1:ℂ)

theorem polynomialBasis_eval (n : ℕ) (x : Block 2) :
    eval (fun i => (x i:ℂ)) (polynomialBasis n) =
      coordinate x^(exponent n 0)*star (coordinate x)^(exponent n 1) := by
  rw [polynomialBasis_apply]
  simp only [forward,aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fin.prod_univ_two]
  simp [coordinate,eval_add,eval_mul,eval_C,eval_X,Complex.conj_ofReal,sub_eq_add_neg]

theorem states_coe (a : ℝ) (ha : 0 < a) (n : ℕ) : states a ha n =ᵐ[MeasureTheory.volume]
    fun x => coordinate x^(exponent n 0)*star (coordinate x)^(exponent n 1)*
      (KFCausalGaussianSliceDomain.gaussian a (x 0)*KFCausalGaussianSliceDomain.gaussian a (x 1)) := by
  filter_upwards [KFCausalPlanePolynomialGaussian.state_coe a a ha ha (polynomialBasis n)] with x hx
  simpa only [packet,polynomialBasis_eval] using hx

#print axioms circularChange
#print axioms states_independent
#print axioms states_dense
#print axioms states_coe
end
end UnifiedTheory.Audit.KFCausalCircularPolynomialBasis
