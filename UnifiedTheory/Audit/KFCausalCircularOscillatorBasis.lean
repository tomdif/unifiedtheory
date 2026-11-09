/- The already constructed physical circular basis has the oscillator
energy of its two occupation indices. The result is proved on the actual
polynomial Gaussian domain, without a spectral or eigenvector assumption. -/
import UnifiedTheory.Audit.KFCausalCircularOscillatorTriangular
import UnifiedTheory.Audit.KFCausalSymmetricTriangularGramSchmidt
import UnifiedTheory.Audit.KFCausalCircularChargeBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Transport through the polynomial range expands several dependent coercions.
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCircularOscillatorBasis
noncomputable section
open InnerProductSpace
open KFCausalPlanePolynomialGaussian (Poly state state_injective)
open KFCausalScaledCircularPolynomials (width_positive polynomialBasis states)
open KFCausalCircularOscillatorPolynomial (oscillator)
open KFCausalCircularOscillatorTriangular (energy triangular)

variable (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "J" => state (b*c^2) b (width_positive c b hc hb) hb

abbrev Domain := (J).range

def polynomialEquiv : Poly ≃ₗ[ℂ] Domain c hc b hb :=
  LinearEquiv.ofInjective (J) (state_injective _ _ _ _)

local notation "E" => polynomialEquiv c hc b hb

def vectors (n : ℕ) : Domain c hc b hb := E (polynomialBasis c hc n)

def operator : Domain c hc b hb →ₗ[ℂ] Domain c hc b hb :=
  (E).toLinearMap.comp ((oscillator c b).comp (E).symm.toLinearMap)

theorem operator_apply (P : Poly) :
    operator c hc b hb (E P) = E (oscillator c b P) := by
  simp only [operator, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

theorem operator_symmetric (x y : Domain c hc b hb) :
    inner ℂ (operator c hc b hb x) y = inner ℂ x (operator c hc b hb y) := by
  obtain ⟨P, rfl⟩ := (E).surjective x
  obtain ⟨Q, rfl⟩ := (E).surjective y
  rw [operator_apply, operator_apply]
  exact KFCausalCircularOscillatorPolynomial.oscillator_symmetric c hc b hb P Q

theorem operator_triangular (n : ℕ) :
    operator c hc b hb (vectors c hc b hb n) -
      (energy c b n:ℂ) • vectors c hc b hb n ∈
      Submodule.span ℂ (vectors c hc b hb '' Set.Iio n) := by
  have hm (P : Poly) (hp : P ∈ Submodule.span ℂ (polynomialBasis c hc '' Set.Iio n)) :
      E P ∈ Submodule.span ℂ (vectors c hc b hb '' Set.Iio n) := by
    induction hp using Submodule.span_induction with
    | mem P hp =>
      obtain ⟨j, hj, rfl⟩ := hp
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | add P Q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
    | smul z P _ hp => simpa only [map_smul] using Submodule.smul_mem _ z hp
  change operator c hc b hb (E _) - (energy c b n:ℂ) • E _ ∈ _
  rw [operator_apply, ← map_smul, ← map_sub]
  exact hm _ (triangular c hc b n)

def normalizedPolynomial (n : ℕ) : Poly :=
  (E).symm (gramSchmidtNormed ℂ (vectors c hc b hb) n)

theorem normalized_state (n : ℕ) :
    J (normalizedPolynomial c hc b hb n) = KFCausalCircularChargeBasis.basis c hc b hb n := by
  have hg := KFCausalSymmetricTriangularGramSchmidt.isometry_gramSchmidtNormed
    (Domain c hc b hb).subtypeₗᵢ (vectors c hc b hb) n
  change (gramSchmidtNormed ℂ (vectors c hc b hb) n).val =
    gramSchmidtNormed ℂ (states c hc b hb) n at hg
  have he : J (normalizedPolynomial c hc b hb n) =
      (gramSchmidtNormed ℂ (vectors c hc b hb) n).val := by
    exact LinearEquiv.ofInjective_symm_apply _ _
  rw [he, hg]
  exact (KFCausalGramSchmidtEigenvectors.basis_apply (states c hc b hb)
    (KFCausalScaledCircularPolynomials.states_independent c hc b hb)
    (KFCausalScaledCircularPolynomials.states_dense c hc b hb) n).symm

theorem polynomial_eigenvalue (n : ℕ) :
    oscillator c b (normalizedPolynomial c hc b hb n) =
      (energy c b n:ℂ) • normalizedPolynomial c hc b hb n := by
  apply (E).injective
  rw [← operator_apply, map_smul]
  have he : E (normalizedPolynomial c hc b hb n) =
      gramSchmidtNormed ℂ (vectors c hc b hb) n := (E).apply_symm_apply _
  rw [he]
  exact KFCausalSymmetricTriangularGramSchmidt.normed_diagonal
    (operator c hc b hb) (vectors c hc b hb) (energy c b)
    (operator_symmetric c hc b hb) (operator_triangular c hc b hb) n

theorem basis_oscillator (n : ℕ) :
    J (oscillator c b (normalizedPolynomial c hc b hb n)) =
      (energy c b n:ℂ) • KFCausalCircularChargeBasis.basis c hc b hb n := by
  rw [polynomial_eigenvalue, map_smul, normalized_state]

#print axioms normalized_state
#print axioms polynomial_eigenvalue
#print axioms basis_oscillator
end
end UnifiedTheory.Audit.KFCausalCircularOscillatorBasis
