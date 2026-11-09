/- Finite `Q`-Channel Three-Profile $3 \times 3$ Sylvester-Jacobi Spectral Covariance Gram
Determinant `Det3_Q(w₁, w₂, w₃, x)`, Orthogonal Residual Profile `w_{1 ⊥ 2}`, Partial Covariance
Minor `PartialCov_Q(w₁, w₃ | w₂, x)`, Sylvester Factorization Identity, Partial Covariance
Cauchy-Schwarz Inequality, Unconditional $3 \times 3$ Gram Determinant Nonnegativity, Hadamard's
$3 \times 3$ Determinant Inequality, Trilateral Shift Invariance, and Sharp $3 \times 3$ Popoviciu
Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
   multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
   multiChannelSpectralVarianceFunctional_shift_invariance)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional
   multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
   multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant
   multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
   multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
   multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds)

section MultiChannelThreeProfileSylvesterGramDeterminantAndHadamard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unnormalized orthogonal residual weight profile
`w_{1 ⊥ 2}(q) = Var_Q(w₂, x) * w₁(q) - Cov_Q(w₁, w₂, x) * w₂(q)` eliminating the spectral covariance
with `w₂` across the `Q`-channel family `P`. -/
def multiChannelSpectralOrthogonalResidual
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) : Fin Q → ℝ :=
  fun q =>
    multiChannelSpectralVarianceFunctional P w₂ x * w₁ q -
      multiChannelSpectralCovarianceFunctional P w₁ w₂ x * w₂ q

/-- Partial spectral covariance minor
`PartialCov_Q(w₁, w₃ | w₂, x) = Var_Q(w₂, x) * Cov_Q(w₁, w₃, x) - Cov_Q(w₁, w₂, x) * Cov_Q(w₂, w₃, x)`
representing the off-diagonal $2 \times 2$ cofactor of the $3 \times 3$ spectral covariance matrix
after conditioning on `w₂`. -/
def multiChannelSpectralPartialCovariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₃ w₂ : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelSpectralVarianceFunctional P w₂ x *
    multiChannelSpectralCovarianceFunctional P w₁ w₃ x -
    multiChannelSpectralCovarianceFunctional P w₁ w₂ x *
      multiChannelSpectralCovarianceFunctional P w₂ w₃ x

/-- $3 \times 3$ spectral covariance Gram determinant
`Det3_Q(w₁, w₂, w₃, x) = V₁ V₂ V₃ + 2 C₁₂ C₂₃ C₁₃ - V₁ C₂₃² - V₂ C₁₃² - V₃ C₁₂²`
of three real weight profiles `w₁ w₂ w₃ : Fin Q → ℝ` at state `x : E`. -/
def multiChannelThreeByThreeSpectralGramDeterminant
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelSpectralVarianceFunctional P w₁ x *
    multiChannelSpectralVarianceFunctional P w₂ x *
    multiChannelSpectralVarianceFunctional P w₃ x +
  2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x *
    multiChannelSpectralCovarianceFunctional P w₂ w₃ x *
    multiChannelSpectralCovarianceFunctional P w₁ w₃ x -
  multiChannelSpectralVarianceFunctional P w₁ x *
    (multiChannelSpectralCovarianceFunctional P w₂ w₃ x) ^ 2 -
  multiChannelSpectralVarianceFunctional P w₂ x *
    (multiChannelSpectralCovarianceFunctional P w₁ w₃ x) ^ 2 -
  multiChannelSpectralVarianceFunctional P w₃ x *
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2

/-- Exact spectral orthogonality `Cov_Q(w_{1 ⊥ 2}, w₂, x) = 0`, single-residual partial covariance
projection `Cov_Q(w_{1 ⊥ 2}, w₃, x) = PartialCov_Q(w₁, w₃ | w₂, x)`, and double-residual covariance
identity `Cov_Q(w_{1 ⊥ 2}, w_{3 ⊥ 2}, x) = Var_Q(w₂, x) * PartialCov_Q(w₁, w₃ | w₂, x)`. -/
theorem multiChannelSpectralOrthogonalResidual_orthogonality_and_partial_covariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) :
    multiChannelSpectralCovarianceFunctional P
      (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) w₂ x = 0 ∧
    multiChannelSpectralCovarianceFunctional P
      (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) w₃ x =
      multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x ∧
    multiChannelSpectralCovarianceFunctional P
      (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
      (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x := by
  let V₂ := multiChannelSpectralVarianceFunctional P w₂ x
  let C₁₂ := multiChannelSpectralCovarianceFunctional P w₁ w₂ x
  let C₃₂ := multiChannelSpectralCovarianceFunctional P w₃ w₂ x
  have hres1 :
      multiChannelSpectralOrthogonalResidual P w₁ w₂ x =
        fun q => V₂ * w₁ q + (-C₁₂) * w₂ q := by
    ext q
    dsimp only [multiChannelSpectralOrthogonalResidual, V₂, C₁₂]
    ring
  have hres3 :
      multiChannelSpectralOrthogonalResidual P w₃ w₂ x =
        fun q => V₂ * w₃ q + (-C₃₂) * w₂ q := by
    ext q
    dsimp only [multiChannelSpectralOrthogonalResidual, V₂, C₃₂]
    ring
  have hlin2 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₂ V₂ (-C₁₂) x).1
  have hdiag2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ w₁ x).2.2
  have horth :
      multiChannelSpectralCovarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) w₂ x = 0 := by
    rw [hres1, hlin2, hdiag2]
    dsimp only [V₂, C₁₂]
    ring
  have hlin3 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₃ V₂ (-C₁₂) x).1
  have hpart :
      multiChannelSpectralCovarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) w₃ x =
        multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x := by
    rw [hres1, hlin3]
    dsimp only [multiChannelSpectralPartialCovariance, V₂, C₁₂]
    ring
  have hsymm_res := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
      (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x).2.1
  have hlin_res3 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₃ w₂ (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) V₂ (-C₃₂) x).1
  have hsymm_w3 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₃ (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) x).2.1
  have hsymm_w2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) x).2.1
  have hdouble :
      multiChannelSpectralCovarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
        (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x =
        V₂ * multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x := by
    rw [hsymm_res, hres3, hlin_res3, hsymm_w3, hsymm_w2, hpart, horth]
    ring
  exact ⟨horth, hpart, hdouble⟩

/-- Sylvester's $3 \times 3$ determinant identity
`Det_Q(w₁, w₂, x) * Det_Q(w₃, w₂, x) - PartialCov_Q(w₁, w₃ | w₂, x)^2 = Var_Q(w₂, x) * Det3_Q(w₁, w₂, w₃, x)`,
orthogonal-residual Gram determinant factorization
`Det_Q(w_{1 ⊥ 2}, w_{3 ⊥ 2}, x) = Var_Q(w₂, x)^2 * (Det_Q(w₁, w₂, x) * Det_Q(w₃, w₂, x) - PartialCov_Q(w₁, w₃ | w₂, x)^2)`,
and the partial covariance Cauchy-Schwarz inequality
`PartialCov_Q(w₁, w₃ | w₂, x)^2 ≤ Det_Q(w₁, w₂, x) * Det_Q(w₃, w₂, x)`. -/
theorem multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) :
    multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
      multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    multiChannelSpectralCovarianceGramDeterminant P
      (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
      (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x =
      (multiChannelSpectralVarianceFunctional P w₂ x) ^ 2 *
        (multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
          multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
          (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2) ∧
    (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 ≤
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
        multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x := by
  have hsymm32 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₃ w₂ x).2.1
  have hsylv :
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
        multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
        (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 =
        multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
    unfold multiChannelSpectralCovarianceGramDeterminant
      multiChannelSpectralPartialCovariance
      multiChannelThreeByThreeSpectralGramDeterminant
    rw [hsymm32]
    ring
  have hv_res1 :
      multiChannelSpectralVarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) x =
        multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x :=
    (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ x).1
  have hv_res3 :
      multiChannelSpectralVarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x =
        multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x :=
    (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₃ w₂ x).1
  have hcov_res := (multiChannelSpectralOrthogonalResidual_orthogonality_and_partial_covariance
    P w₁ w₂ w₃ x).2.2
  have hdet_res :
      multiChannelSpectralCovarianceGramDeterminant P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
        (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x =
        (multiChannelSpectralVarianceFunctional P w₂ x) ^ 2 *
          (multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
            multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
            (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2) := by
    change multiChannelSpectralVarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x) x *
      multiChannelSpectralVarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x -
      (multiChannelSpectralCovarianceFunctional P
        (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
        (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x) ^ 2 = _
    rw [hv_res1, hv_res3, hcov_res]
    ring
  have hdet_res_nn := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
    P (multiChannelSpectralOrthogonalResidual P w₁ w₂ x)
      (multiChannelSpectralOrthogonalResidual P w₃ w₂ x) x).2.1
  let V₂ := multiChannelSpectralVarianceFunctional P w₂ x
  have hV₂_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).2.1
  have hpcs :
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 ≤
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
          multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x := by
    by_cases hV₂0 : V₂ = 0
    · have hcs12 := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
        P w₁ w₂ x).2.2
      change (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        multiChannelSpectralVarianceFunctional P w₁ x * V₂ at hcs12
      rw [hV₂0, mul_zero] at hcs12
      have hC12_sq_0 : (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 = 0 :=
        le_antisymm hcs12 (sq_nonneg _)
      have hC12_0 : multiChannelSpectralCovarianceFunctional P w₁ w₂ x = 0 :=
        sq_eq_zero_iff.mp hC12_sq_0
      have hp0 : multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x = 0 := by
        unfold multiChannelSpectralPartialCovariance
        change V₂ * multiChannelSpectralCovarianceFunctional P w₁ w₃ x -
          multiChannelSpectralCovarianceFunctional P w₁ w₂ x *
            multiChannelSpectralCovarianceFunctional P w₂ w₃ x = 0
        rw [hV₂0, hC12_0]
        ring
      have hd12_nn := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
        P w₁ w₂ x).2.1
      have hd32_nn := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
        P w₃ w₂ x).2.1
      rw [hp0]
      nlinarith [mul_nonneg hd12_nn hd32_nn]
    · have hV₂_pos : 0 < V₂ := lt_of_le_of_ne hV₂_nn (Ne.symm hV₂0)
      have hV₂_sq_pos : 0 < V₂ ^ 2 := sq_pos_of_pos hV₂_pos
      nlinarith [hdet_res, hdet_res_nn, hV₂_sq_pos]
  exact ⟨hsylv, hdet_res, hpcs⟩

/-- Unconditional $3 \times 3$ spectral covariance Gram determinant nonnegativity
`0 ≤ Det3_Q(w₁, w₂, w₃, x)`, Laplace-Sylvester block upper bound
`Det3_Q(w₁, w₂, w₃, x) ≤ Var_Q(w₁, x) * Det_Q(w₂, w₃, x)`, and Hadamard's $3 \times 3$ determinant
inequality
`Det3_Q(w₁, w₂, w₃, x) ≤ Var_Q(w₁, x) * Var_Q(w₂, x) * Var_Q(w₃, x)`. -/
theorem multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) :
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralVarianceFunctional P w₃ x := by
  let V₁ := multiChannelSpectralVarianceFunctional P w₁ x
  let V₂ := multiChannelSpectralVarianceFunctional P w₂ x
  let V₃ := multiChannelSpectralVarianceFunctional P w₃ x
  let C₁₂ := multiChannelSpectralCovarianceFunctional P w₁ w₂ x
  let C₂₃ := multiChannelSpectralCovarianceFunctional P w₂ w₃ x
  let C₁₃ := multiChannelSpectralCovarianceFunctional P w₁ w₃ x
  have hV₁_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).2.1
  have hV₂_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).2.1
  have hsylv_pkg := multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    P w₁ w₂ w₃ x
  have hdet23_nn := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
    P w₂ w₃ x).2.1
  have hblock_id :
      V₂ * (V₁ * multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x -
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x) =
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 +
        C₁₂ ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x := by
    unfold multiChannelSpectralCovarianceGramDeterminant
      multiChannelThreeByThreeSpectralGramDeterminant
      multiChannelSpectralPartialCovariance
    dsimp only [V₁, V₂, V₃, C₁₂, C₂₃, C₁₃]
    ring
  have hdet3_nn_and_block :
      0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        V₁ * multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x := by
    by_cases hV₂0 : V₂ = 0
    · have hcs12 := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
        P w₁ w₂ x).2.2
      change C₁₂ ^ 2 ≤ V₁ * V₂ at hcs12
      rw [hV₂0, mul_zero] at hcs12
      have hC12_0 : C₁₂ = 0 := sq_eq_zero_iff.mp (le_antisymm hcs12 (sq_nonneg _))
      have hcs23 := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
        P w₂ w₃ x).2.2
      change C₂₃ ^ 2 ≤ V₂ * V₃ at hcs23
      rw [hV₂0, zero_mul] at hcs23
      have hC23_0 : C₂₃ = 0 := sq_eq_zero_iff.mp (le_antisymm hcs23 (sq_nonneg _))
      have hdet3_0 : multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x = 0 := by
        unfold multiChannelThreeByThreeSpectralGramDeterminant
        change V₁ * V₂ * V₃ + 2 * C₁₂ * C₂₃ * C₁₃ - V₁ * C₂₃ ^ 2 - V₂ * C₁₃ ^ 2 - V₃ * C₁₂ ^ 2 = 0
        rw [hV₂0, hC12_0, hC23_0]
        ring
      rw [hdet3_0]
      exact ⟨le_rfl, mul_nonneg hV₁_nn hdet23_nn⟩
    · have hV₂_pos : 0 < V₂ := lt_of_le_of_ne hV₂_nn (Ne.symm hV₂0)
      have hdet3_nn : 0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
        nlinarith [hsylv_pkg.1, hsylv_pkg.2.2, hV₂_pos]
      have h_rhs_nn :
          0 ≤ (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 +
            C₁₂ ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x :=
        add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg C₁₂) hdet23_nn)
      have hblock_le :
          multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
            V₁ * multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x := by
        nlinarith [hblock_id, h_rhs_nn, hV₂_pos]
      exact ⟨hdet3_nn, hblock_le⟩
  have hdet23_le :
      multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x ≤ V₂ * V₃ := by
    unfold multiChannelSpectralCovarianceGramDeterminant
    dsimp only [V₂, V₃, C₂₃]
    linarith [sq_nonneg C₂₃]
  have hhadamard :
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤ V₁ * V₂ * V₃ := by
    have hm := mul_le_mul_of_nonneg_left hdet23_le hV₁_nn
    linarith [hdet3_nn_and_block.2, hm]
  exact ⟨hdet3_nn_and_block.1, hdet3_nn_and_block.2, hhadamard⟩

/-- Trilateral shift invariance
`Det3_Q(w₁ + c₁, w₂ + c₂, w₃ + c₃, x) = Det3_Q(w₁, w₂, w₃, x)` and sharp $3 \times 3$
Hadamard-Popoviciu upper bounds
`Det3_Q(w₁, w₂, w₃, x) ≤ Var_Q(w₁, x) * Var_Q(w₂, x) * Var_Q(w₃, x) ≤ ((w₁_max - w₁_min)/2)^2 * ((w₂_max - w₂_min)/2)^2 * ((w₃_max - w₃_min)/2)^2 * E_Q(x)^6`. -/
theorem multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (c₁ c₂ c₃ w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E) :
    multiChannelThreeByThreeSpectralGramDeterminant P
      (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) (fun q => w₃ q + c₃) x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    multiChannelSpectralVarianceFunctional P w₁ x *
      multiChannelSpectralVarianceFunctional P w₂ x *
      multiChannelSpectralVarianceFunctional P w₃ x ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 := by
  have hv1_sh := (multiChannelSpectralVarianceFunctional_shift_invariance P w₁ c₁ x).2
  have hv2_sh := (multiChannelSpectralVarianceFunctional_shift_invariance P w₂ c₂ x).2
  have hv3_sh := (multiChannelSpectralVarianceFunctional_shift_invariance P w₃ c₃ x).2
  have hc12_sh := (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    P w₁ w₂ c₁ c₂ x).2
  have hc23_sh := (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    P w₂ w₃ c₂ c₃ x).2
  have hc13_sh := (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    P w₁ w₃ c₁ c₃ x).2
  have hshift :
      multiChannelThreeByThreeSpectralGramDeterminant P
        (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) (fun q => w₃ q + c₃) x =
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
    unfold multiChannelThreeByThreeSpectralGramDeterminant
    rw [hv1_sh, hv2_sh, hv3_sh, hc12_sh, hc23_sh, hc13_sh]
  have hpop12 := (multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ x).2.2.1
  have hpop3 := (multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w₃ w₃_min w₃_max hmin₃ hmax₃ x).2.2
  have hv3_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₃ x).2.1
  have hE4_nn : 0 ≤ (multiChannelProjectedEnergy P x) ^ 4 := by
    have h4 : (multiChannelProjectedEnergy P x) ^ 4 = ((multiChannelProjectedEnergy P x) ^ 2) ^ 2 := by ring
    rw [h4]
    exact sq_nonneg _
  have hb12_nn :
      0 ≤ ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        (multiChannelProjectedEnergy P x) ^ 4 :=
    mul_nonneg
      (mul_nonneg (sq_nonneg ((w₁_max - w₁_min) / 2)) (sq_nonneg ((w₂_max - w₂_min) / 2)))
      hE4_nn
  have hprod_raw := mul_le_mul hpop12 hpop3 hv3_nn hb12_nn
  have hprod3 :
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralVarianceFunctional P w₃ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 := by
    calc
      multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralVarianceFunctional P w₃ x
        ≤ (((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
            (multiChannelProjectedEnergy P x) ^ 4) *
            (((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2) := hprod_raw
      _ = ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
            ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 := by ring
  have hhad := (multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x).2.2
  exact ⟨hshift, hprod3, hhad.trans hprod3⟩

/-- `Q`-channel $3 \times 3$ Sylvester-Jacobi Gram determinant nonnegativity, Sylvester identity,
Hadamard's $3 \times 3$ determinant inequality, and $3 \times 3$ Popoviciu bound on
`arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_multiChannel_threeByThreeGramDeterminant_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c_poly : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c_poly PK
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ *
      multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ Ψ -
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ Ψ) ^ 2 =
      multiChannelSpectralVarianceFunctional P w₂ Ψ *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ *
        multiChannelSpectralVarianceFunctional P w₂ Ψ *
        multiChannelSpectralVarianceFunctional P w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P Ψ) ^ 6 := by
  intro Ψ
  have hsylv := multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    P w₁ w₂ w₃ Ψ
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ Ψ
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ Ψ
  exact ⟨hhad.1, hsylv.1, hhad.2.2, hpop.2.2⟩

/-- Master Synthesis of the Finite `Q`-Channel Three-Profile $3 \times 3$ Sylvester-Jacobi Spectral
Covariance Gram Determinant, Orthogonal Residual Projection, Partial Covariance Cauchy-Schwarz
Inequality, Hadamard's $3 \times 3$ Determinant Inequality, Trilateral Shift Invariance, and Sharp
$3 \times 3$ Popoviciu Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_multiChannel_threeByThree_spectralGramDeterminant_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (c₁_sh c₂_sh c₃_sh w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max)
    (M : ℕ) (c_poly : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c_poly
      (identicalPackets ψ)
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ Ψ) ^ 2 ≤
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ *
        multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ *
        multiChannelSpectralVarianceFunctional P w₂ Ψ *
        multiChannelSpectralVarianceFunctional P w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P
      (fun q => w₁ q + c₁_sh) (fun q => w₂ q + c₂_sh) (fun q => w₃ q + c₃_sh) Ψ =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P Ψ) ^ 6 := by
  intro Ψ
  have hsylv := multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    P w₁ w₂ w₃ Ψ
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ Ψ
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ c₁_sh c₂_sh c₃_sh w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ Ψ
  exact ⟨hhad.1, hsylv.2.2, hhad.2.2, hpop.1, hpop.2.2⟩

end MultiChannelThreeProfileSylvesterGramDeterminantAndHadamard

#print axioms multiChannelSpectralOrthogonalResidual_orthogonality_and_partial_covariance
#print axioms multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
#print axioms multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
#print axioms multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
#print axioms arbitrarySourceDegreeMPolyState_multiChannel_threeByThreeGramDeterminant_package
#print axioms arbitrary_source_multiChannel_threeByThree_spectralGramDeterminant_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
