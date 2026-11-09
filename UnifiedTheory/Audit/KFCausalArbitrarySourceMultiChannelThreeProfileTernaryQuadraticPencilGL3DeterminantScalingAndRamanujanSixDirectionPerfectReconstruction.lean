/- Finite `Q`-Channel Three-Profile Ternary Quadratic Variance Pencil
`Var_Q(a w₁ + b w₂ + c w₃, x)`, Exact $\mathrm{GL}_3(\mathbb{R})$ Determinant Scaling
`Det3_Q(A(w₁, w₂, w₃), x) = (\det A)^2 Det3_Q(w₁, w₂, w₃, x)`, $\mathrm{SL}_3(\mathbb{R})$
Unimodular & Upper-Triangular Shear Invariance, and Ramanujan Six-Direction Perfect-Set
Reconstruction of all 6 Entries of the $3 \times 3$ Spectral Covariance Matrix and `Det3_Q` on
Arbitrary-Source Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional
   multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant
   multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelSpectralPartialCovariance
   multiChannelThreeByThreeSpectralGramDeterminant
   multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
   multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds)

section TernaryQuadraticPencilGL3ScalingAndRamanujanSixDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Linear combination of three `Q`-channel weight profiles `a • w₁ + b • w₂ + c • w₃`. -/
def multiChannelTernaryLinearCombination
    {Q : ℕ} (w₁ w₂ w₃ : Fin Q → ℝ) (a b c : ℝ) : Fin Q → ℝ :=
  fun q => a * w₁ q + b * w₂ q + c * w₃ q

/-- Classical $3 \times 3$ determinant
`det A = a₁₁(a₂₂ a₃₃ - a₂₃ a₃₂) - a₁₂(a₂₁ a₃₃ - a₂₃ a₃₁) + a₁₃(a₂₁ a₃₂ - a₂₂ a₃₁)`
of a $3 \times 3$ real transformation matrix `(aᵢⱼ)`. -/
def gl3Determinant (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) : ℝ :=
  a₁₁ * (a₂₂ * a₃₃ - a₂₃ * a₃₂) -
    a₁₂ * (a₂₁ * a₃₃ - a₂₃ * a₃₁) +
    a₁₃ * (a₂₁ * a₃₂ - a₂₂ * a₃₁)

/-- Ramanujan six-direction perfect-set directional variance tuple
`(D₁, D₂, D₃, D₄, D₅, D₆)` along the six primitive integer directions
`(1, 1, 1), (-1, 1, 1), (1, -1, 1), (1, 1, -1), (2, 1, 1), (1, 2, 1)` of a ternary quadratic form. -/
def ramanujanSixDirectionVarianceVector
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  (multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) x,
   multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) x,
   multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) x,
   multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) x,
   multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ 2 1 1) x,
   multiChannelSpectralVarianceFunctional P (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 2 1) x)

/-- Trilinear expansion of `multiChannelSpectralCovarianceFunctional` on ternary linear combinations
`a • w₁ + b • w₂ + c • w₃`, bilinear expansion of the covariance of two ternary linear combinations,
and the exact ternary quadratic variance pencil identity
`Var_Q(a w₁ + b w₂ + c w₃, x) = a^2 V₁ + b^2 V₂ + c^2 V₃ + 2 a b C₁₂ + 2 a c C₁₃ + 2 b c C₂₃ ≥ 0`. -/
theorem multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ u : Fin Q → ℝ)
    (a b c a' b' c' : ℝ) (x : E) :
    multiChannelSpectralCovarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ a b c) u x =
      a * multiChannelSpectralCovarianceFunctional P w₁ u x +
        b * multiChannelSpectralCovarianceFunctional P w₂ u x +
        c * multiChannelSpectralCovarianceFunctional P w₃ u x ∧
    multiChannelSpectralCovarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ a b c)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ a' b' c') x =
      a * a' * multiChannelSpectralVarianceFunctional P w₁ x +
        b * b' * multiChannelSpectralVarianceFunctional P w₂ x +
        c * c' * multiChannelSpectralVarianceFunctional P w₃ x +
        (a * b' + b * a') * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        (a * c' + c * a') * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
        (b * c' + c * b') * multiChannelSpectralCovarianceFunctional P w₂ w₃ x ∧
    multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ a b c) x =
      a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
        b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x +
        c ^ 2 * multiChannelSpectralVarianceFunctional P w₃ x +
        2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        2 * a * c * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
        2 * b * c * multiChannelSpectralCovarianceFunctional P w₂ w₃ x ∧
    0 ≤ a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
        b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x +
        c ^ 2 * multiChannelSpectralVarianceFunctional P w₃ x +
        2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        2 * a * c * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
        2 * b * c * multiChannelSpectralCovarianceFunctional P w₂ w₃ x := by
  have hdecomp :
      ∀ α β γ : ℝ,
        multiChannelTernaryLinearCombination w₁ w₂ w₃ α β γ =
          fun q => 1 * (α * w₁ q + β * w₂ q) + γ * w₃ q := by
    intro α β γ
    ext q
    unfold multiChannelTernaryLinearCombination
    ring
  have hlin_left :
      ∀ (v : Fin Q → ℝ) (α β γ : ℝ),
        multiChannelSpectralCovarianceFunctional P
          (multiChannelTernaryLinearCombination w₁ w₂ w₃ α β γ) v x =
          α * multiChannelSpectralCovarianceFunctional P w₁ v x +
            β * multiChannelSpectralCovarianceFunctional P w₂ v x +
            γ * multiChannelSpectralCovarianceFunctional P w₃ v x := by
    intro v α β γ
    rw [hdecomp α β γ]
    have h1 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
      P (fun q => α * w₁ q + β * w₂ q) w₃ v 1 γ x).1
    have h2 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
      P w₁ w₂ v α β x).1
    rw [h1, h2]
    ring
  have hlin_u := hlin_left u a b c
  let u' := multiChannelTernaryLinearCombination w₁ w₂ w₃ a' b' c'
  have h1_u' := hlin_left u' a b c
  have hsymm1 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₁ u' x).2.1
  have hsymm2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₂ u' x).2.1
  have hsymm3 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₃ u' x).2.1
  have h_u'1 := hlin_left w₁ a' b' c'
  have h_u'2 := hlin_left w₂ a' b' c'
  have h_u'3 := hlin_left w₃ a' b' c'
  have hdiag1 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₁ w₁ x).2.2
  have hdiag2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₂ w₂ x).2.2
  have hdiag3 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₃ w₃ x).2.2
  have hsymm21 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₂ w₁ x).2.1
  have hsymm31 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₃ w₁ x).2.1
  have hsymm32 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₃ w₂ x).2.1
  have hbilin :
      multiChannelSpectralCovarianceFunctional P
        (multiChannelTernaryLinearCombination w₁ w₂ w₃ a b c) u' x =
        a * a' * multiChannelSpectralVarianceFunctional P w₁ x +
          b * b' * multiChannelSpectralVarianceFunctional P w₂ x +
          c * c' * multiChannelSpectralVarianceFunctional P w₃ x +
          (a * b' + b * a') * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
          (a * c' + c * a') * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
          (b * c' + c * b') * multiChannelSpectralCovarianceFunctional P w₂ w₃ x := by
    rw [h1_u', hsymm1, hsymm2, hsymm3, h_u'1, h_u'2, h_u'3,
      hdiag1, hdiag2, hdiag3, hsymm21, hsymm31, hsymm32]
    ring
  let u_abc := multiChannelTernaryLinearCombination w₁ w₂ w₃ a b c
  have hdiag_abc := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P u_abc u_abc x).2.2
  have hbilin_self :
      multiChannelSpectralCovarianceFunctional P u_abc u_abc x =
        a * a * multiChannelSpectralVarianceFunctional P w₁ x +
          b * b * multiChannelSpectralVarianceFunctional P w₂ x +
          c * c * multiChannelSpectralVarianceFunctional P w₃ x +
          (a * b + b * a) * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
          (a * c + c * a) * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
          (b * c + c * b) * multiChannelSpectralCovarianceFunctional P w₂ w₃ x := by
    rw [hlin_left u_abc a b c,
      (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₁ u_abc x).2.1,
      (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₂ u_abc x).2.1,
      (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry P w₃ u_abc x).2.1,
      hlin_left w₁ a b c, hlin_left w₂ a b c, hlin_left w₃ a b c,
      hdiag1, hdiag2, hdiag3, hsymm21, hsymm31, hsymm32]
    ring
  have hpencil :
      multiChannelSpectralVarianceFunctional P u_abc x =
        a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
          b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x +
          c ^ 2 * multiChannelSpectralVarianceFunctional P w₃ x +
          2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
          2 * a * c * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
          2 * b * c * multiChannelSpectralCovarianceFunctional P w₂ w₃ x := by
    rw [← hdiag_abc, hbilin_self]
    ring
  have hv_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P u_abc x).2.1
  exact ⟨hlin_u, hbilin, hpencil, by linarith [hpencil, hv_nn]⟩

/-- **Ramanujan Six-Direction Perfect-Set Reconstruction Theorem for Ternary Spectral Covariance
Forms**: The six directional variances
`D₁ = Var_Q(w₁ + w₂ + w₃, x)`, `D₂ = Var_Q(-w₁ + w₂ + w₃, x)`, `D₃ = Var_Q(w₁ - w₂ + w₃, x)`,
`D₄ = Var_Q(w₁ + w₂ - w₃, x)`, `D₅ = Var_Q(2 w₁ + w₂ + w₃, x)`, `D₆ = Var_Q(w₁ + 2 w₂ + w₃, x)`
along the Ramanujan perfect set `{(1,1,1), (-1,1,1), (1,-1,1), (1,1,-1), (2,1,1), (1,2,1)}` uniquely
and linearly reconstruct all three spectral covariances `Cov_Q(w₁, w₂, x)`, `Cov_Q(w₁, w₃, x)`,
`Cov_Q(w₂, w₃, x)` and all three channel variances `Var_Q(w₁, x)`, `Var_Q(w₂, x)`, `Var_Q(w₃, x)`. -/
theorem multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (x : E) :
    let D₁ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) x
    let D₂ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) x
    let D₃ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) x
    let D₄ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) x
    let D₅ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 2 1 1) x
    let D₆ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 2 1) x
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x = D₁ - D₂ - D₃ + D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₃ x = D₁ - D₂ + D₃ - D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₂ w₃ x = D₁ + D₂ - D₃ - D₄ ∧
    4 * (multiChannelSpectralVarianceFunctional P w₁ x +
      multiChannelSpectralVarianceFunctional P w₂ x +
      multiChannelSpectralVarianceFunctional P w₃ x) = D₁ + D₂ + D₃ + D₄ ∧
    6 * multiChannelSpectralVarianceFunctional P w₁ x = 2 * D₅ - 3 * D₁ + D₂ ∧
    6 * multiChannelSpectralVarianceFunctional P w₂ x = 2 * D₆ - 3 * D₁ + D₃ ∧
    12 * multiChannelSpectralVarianceFunctional P w₃ x =
      15 * D₁ + D₂ + D₃ + 3 * D₄ - 4 * D₅ - 4 * D₆ := by
  intro D₁ D₂ D₃ D₄ D₅ D₆
  have hD₁ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ 1 1 1 1 1 1 x).2.2.1
  have hD₂ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ (-1) 1 1 1 1 1 x).2.2.1
  have hD₃ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ 1 (-1) 1 1 1 1 x).2.2.1
  have hD₄ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ 1 1 (-1) 1 1 1 x).2.2.1
  have hD₅ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ 2 1 1 1 1 1 x).2.2.1
  have hD₆ := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
    P w₁ w₂ w₃ w₁ 1 2 1 1 1 1 x).2.2.1
  dsimp only [D₁, D₂, D₃, D₄, D₅, D₆]
  rw [hD₁, hD₂, hD₃, hD₄, hD₅, hD₆]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- **Exact $\mathrm{GL}_3(\mathbb{R})$ Determinant Scaling Law and $\mathrm{SL}_3(\mathbb{R})$ / Shear
Invariance of the $3 \times 3$ Spectral Covariance Gram Determinant**:
For any $3 \times 3$ real matrix `A = (aᵢⱼ)` transforming `(w₁, w₂, w₃)` into `(u₁, u₂, u₃)`:
1. `Det3_Q(u₁, u₂, u₃, x) = (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃)^2 * Det3_Q(w₁, w₂, w₃, x)`;
2. Whenever `(gl3Determinant ...)^2 = 1` (e.g. `A ∈ SL₃(ℝ)` or `A ∈ O(3)`), `Det3_Q(u₁, u₂, u₃, x) = Det3_Q(w₁, w₂, w₃, x)`;
3. Upper-triangular 3D shear invariance:
   `Det3_Q(w₁ + α w₂ + β w₃, w₂ + γ w₃, w₃, x) = Det3_Q(w₁, w₂, w₃, x)`. -/
theorem multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ α β γ : ℝ) (x : E) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
      (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    ((gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 →
      multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x) ∧
    multiChannelThreeByThreeSpectralGramDeterminant P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 α β)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 1 γ)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 0 1) x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
  intro u₁ u₂ u₃
  have hscale :
      ∀ (b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : ℝ),
        multiChannelThreeByThreeSpectralGramDeterminant P
          (multiChannelTernaryLinearCombination w₁ w₂ w₃ b₁₁ b₁₂ b₁₃)
          (multiChannelTernaryLinearCombination w₁ w₂ w₃ b₂₁ b₂₂ b₂₃)
          (multiChannelTernaryLinearCombination w₁ w₂ w₃ b₃₁ b₃₂ b₃₃) x =
          (gl3Determinant b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃) ^ 2 *
            multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
    intro b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃
    have hv1 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₁₁ b₁₂ b₁₃ b₁₁ b₁₂ b₁₃ x).2.2.1
    have hv2 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₂₁ b₂₂ b₂₃ b₂₁ b₂₂ b₂₃ x).2.2.1
    have hv3 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₃₁ b₃₂ b₃₃ b₃₁ b₃₂ b₃₃ x).2.2.1
    have hc12 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ x).2.1
    have hc23 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ x).2.1
    have hc13 := (multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
      P w₁ w₂ w₃ w₁ b₁₁ b₁₂ b₁₃ b₃₁ b₃₂ b₃₃ x).2.1
    unfold multiChannelThreeByThreeSpectralGramDeterminant gl3Determinant
    rw [hv1, hv2, hv3, hc12, hc23, hc13]
    ring
  have hmain := hscale a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
  have hshear := hscale 1 α β 0 1 γ 0 0 1
  have hdet_shear : gl3Determinant 1 α β 0 1 γ 0 0 1 = 1 := by
    unfold gl3Determinant
    ring
  rw [hdet_shear] at hshear
  refine ⟨hmain, fun hdet1 => by rw [hmain, hdet1, one_mul], by linarith [hshear]⟩

/-- $\mathrm{GL}_3(\mathbb{R})$-transformed $3 \times 3$ Gram determinant nonnegativity,
$\mathrm{GL}_3(\mathbb{R})$-scaled Hadamard inequality, and $\mathrm{GL}_3(\mathbb{R})$-scaled
$3 \times 3$ Popoviciu upper bound. -/
theorem multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    let detA := gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x ≤
      detA ^ 2 *
        (multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralVarianceFunctional P w₃ x) ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x ≤
      detA ^ 2 *
        (((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6) := by
  intro u₁ u₂ u₃ detA
  have hgl3 := (multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ 0 0 0 x).1
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  have hdetA_sq_nn : 0 ≤ detA ^ 2 := sq_nonneg detA
  dsimp only [u₁, u₂, u₃, detA]
  rw [hgl3]
  exact ⟨mul_nonneg hdetA_sq_nn hhad.1,
    mul_le_mul_of_nonneg_left hhad.2.2 hdetA_sq_nn,
    mul_le_mul_of_nonneg_left hpop.2.2 hdetA_sq_nn⟩

/-- Ternary quadratic variance pencil, $\mathrm{GL}_3(\mathbb{R})$ determinant scaling, and Ramanujan
Six-Direction Perfect-Set Reconstruction on `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_ternaryQuadraticPencil_gl3_and_ramanujanSixDirection_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c_poly : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c_poly PK
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    let D₁ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) Ψ
    let D₂ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) Ψ
    let D₃ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) Ψ
    let D₄ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) Ψ
    let D₅ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 2 1 1) Ψ
    let D₆ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 2 1) Ψ
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ Ψ =
      (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ = D₁ - D₂ - D₃ + D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₃ Ψ = D₁ - D₂ + D₃ - D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₂ w₃ Ψ = D₁ + D₂ - D₃ - D₄ ∧
    6 * multiChannelSpectralVarianceFunctional P w₁ Ψ = 2 * D₅ - 3 * D₁ + D₂ ∧
    6 * multiChannelSpectralVarianceFunctional P w₂ Ψ = 2 * D₆ - 3 * D₁ + D₃ ∧
    12 * multiChannelSpectralVarianceFunctional P w₃ Ψ =
      15 * D₁ + D₂ + D₃ + 3 * D₄ - 4 * D₅ - 4 * D₆ := by
  intro Ψ u₁ u₂ u₃ D₁ D₂ D₃ D₄ D₅ D₆
  have hgl3 := (multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ 0 0 0 Ψ).1
  have hram := multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    P w₁ w₂ w₃ Ψ
  exact ⟨hgl3, hram.1, hram.2.1, hram.2.2.1, hram.2.2.2.2.1, hram.2.2.2.2.2.1, hram.2.2.2.2.2.2⟩

/-- Master Synthesis of the Finite `Q`-Channel Three-Profile Ternary Quadratic Variance Pencil,
$\mathrm{GL}_3(\mathbb{R})$ Determinant Scaling, $\mathrm{SL}_3(\mathbb{R})$ Shear Invariance,
$\mathrm{GL}_3(\mathbb{R})$-Scaled Hadamard & Popoviciu Bounds, and Ramanujan Six-Direction
Perfect-Set Reconstruction on Neutral Antipodal Polynomial States. -/
theorem arbitrary_source_multiChannel_threeProfile_gl3_ramanujanSixDirection_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ α β γ : ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max)
    (M : ℕ) (c_poly : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c_poly
      (identicalPackets ψ)
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    let detA := gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ Ψ =
      detA ^ 2 * multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 α β)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 1 γ)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 0 1) Ψ =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ Ψ ≤
      detA ^ 2 *
        (((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P Ψ) ^ 6) ∧
    4 * (multiChannelSpectralVarianceFunctional P w₁ Ψ +
      multiChannelSpectralVarianceFunctional P w₂ Ψ +
      multiChannelSpectralVarianceFunctional P w₃ Ψ) =
      multiChannelSpectralVarianceFunctional P
        (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) Ψ +
      multiChannelSpectralVarianceFunctional P
        (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) Ψ +
      multiChannelSpectralVarianceFunctional P
        (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) Ψ +
      multiChannelSpectralVarianceFunctional P
        (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) Ψ := by
  intro Ψ u₁ u₂ u₃ detA
  have hgl3 := multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ α β γ Ψ
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
    w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ Ψ
  have hram := multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    P w₁ w₂ w₃ Ψ
  exact ⟨hgl3.1, hgl3.2.2, hpop.2.2, hram.2.2.2.1⟩

end TernaryQuadraticPencilGL3ScalingAndRamanujanSixDirection

#print axioms multiChannelTernaryLinearCombination_covariance_and_quadratic_variance_pencil
#print axioms multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
#print axioms multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
#print axioms multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds
#print axioms arbitrarySourceDegreeMPolyState_ternaryQuadraticPencil_gl3_and_ramanujanSixDirection_package
#print axioms arbitrary_source_multiChannel_threeProfile_gl3_ramanujanSixDirection_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction
