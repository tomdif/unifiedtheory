/- Finite `Q`-Channel Spectral Covariance $2 \times 2$ Gram Determinant, Quadratic Variance Pencil,
Completing-the-Square Identity, Multiplicative Cauchy-Schwarz Inequality
`Cov_Q(w₁, w₂, x)^2 ≤ Var_Q(w₁, x) * Var_Q(w₂, x)`, Exact $\mathrm{GL}_2(\mathbb{R})$ Determinant
Scaling & $\mathrm{SL}_2(\mathbb{R})$ Shear Invariance, and Sharp Multiplicative Popoviciu Bounds
on Arbitrary-Source Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyResponse)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (hilbertEnergy)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelLagrangeDoubleSpread
   multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
   multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
   multiChannelSpectralVarianceFunctional_shift_invariance)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional
   multiChannelLagrangeDoubleCoSpread
   multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
   multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance)

section MultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- $2 \times 2$ spectral covariance Gram determinant
`Det_Q(w₁, w₂, x) = Var_Q(w₁, x) * Var_Q(w₂, x) - Cov_Q(w₁, w₂, x) ^ 2` across a finite
`Q`-channel operator family `P : Fin Q → (E →L[ℂ] E)` and two real weight profiles
`w₁ w₂ : Fin Q → ℝ`. -/
def multiChannelSpectralCovarianceGramDeterminant
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelSpectralVarianceFunctional P w₁ x *
    multiChannelSpectralVarianceFunctional P w₂ x -
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2

/-- Bilinear expansion of `multiChannelSpectralCovarianceFunctional` in linear combinations
`a • w₁ + b • w₂` and exact quadratic variance pencil expansion
`Var_Q(a • w₁ + b • w₂, x) = a^2 * Var_Q(w₁, x) + 2 * a * b * Cov_Q(w₁, w₂, x) + b^2 * Var_Q(w₂, x) ≥ 0`. -/
theorem multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ) (a b : ℝ) (x : E) :
    multiChannelSpectralCovarianceFunctional P (fun q => a * w₁ q + b * w₂ q) w₃ x =
      a * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
        b * multiChannelSpectralCovarianceFunctional P w₂ w₃ x ∧
    multiChannelSpectralVarianceFunctional P (fun q => a * w₁ q + b * w₂ q) x =
      a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
        2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x ∧
    0 ≤ a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
        2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x := by
  have hco_lin :
      multiChannelLagrangeDoubleCoSpread P (fun q => a * w₁ q + b * w₂ q) w₃ x =
        a * multiChannelLagrangeDoubleCoSpread P w₁ w₃ x +
          b * multiChannelLagrangeDoubleCoSpread P w₂ w₃ x := by
    unfold multiChannelLagrangeDoubleCoSpread
    have hpt : ∀ q₁ q₂ : Fin Q,
        (a * w₁ q₁ + b * w₂ q₁ - (a * w₁ q₂ + b * w₂ q₂)) * (w₃ q₁ - w₃ q₂) *
            hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          a * ((w₁ q₁ - w₁ q₂) * (w₃ q₁ - w₃ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) +
          b * ((w₂ q₁ - w₂ q₂) * (w₃ q₁ - w₃ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) := by
      intro q₁ q₂
      ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hvar_quad :
      multiChannelLagrangeDoubleSpread P (fun q => a * w₁ q + b * w₂ q) x =
        a ^ 2 * multiChannelLagrangeDoubleSpread P w₁ x +
          2 * a * b * multiChannelLagrangeDoubleCoSpread P w₁ w₂ x +
          b ^ 2 * multiChannelLagrangeDoubleSpread P w₂ x := by
    unfold multiChannelLagrangeDoubleSpread multiChannelLagrangeDoubleCoSpread
    have hpt : ∀ q₁ q₂ : Fin Q,
        (a * w₁ q₁ + b * w₂ q₁ - (a * w₁ q₂ + b * w₂ q₂)) ^ 2 *
            hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          a ^ 2 * ((w₁ q₁ - w₁ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) +
          2 * a * b * ((w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) +
          b ^ 2 * ((w₂ q₁ - w₂ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) := by
      intro q₁ q₂
      ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcov_ab := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P (fun q => a * w₁ q + b * w₂ q) w₃ x).1
  have hcov_13 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₃ x).1
  have hcov_23 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ w₃ x).1
  have hcov_12 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ x).1
  have hv_ab := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => a * w₁ q + b * w₂ q) x
  have hv1 := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).1
  have hv2 := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).1
  have hco_eq :
      multiChannelSpectralCovarianceFunctional P (fun q => a * w₁ q + b * w₂ q) w₃ x =
        a * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
          b * multiChannelSpectralCovarianceFunctional P w₂ w₃ x := by
    have h2 :
        2 * multiChannelSpectralCovarianceFunctional P (fun q => a * w₁ q + b * w₂ q) w₃ x =
          2 * (a * multiChannelSpectralCovarianceFunctional P w₁ w₃ x +
            b * multiChannelSpectralCovarianceFunctional P w₂ w₃ x) := by
      rw [← hcov_ab, hco_lin, hcov_13, hcov_23]
      ring
    linarith [h2]
  have hpencil :
      multiChannelSpectralVarianceFunctional P (fun q => a * w₁ q + b * w₂ q) x =
        a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
          2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
          b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x := by
    have h2 :
        2 * multiChannelSpectralVarianceFunctional P (fun q => a * w₁ q + b * w₂ q) x =
          2 * (a ^ 2 * multiChannelSpectralVarianceFunctional P w₁ x +
            2 * a * b * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
            b ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x) := by
      rw [← hv_ab.1, hvar_quad, hv1, hcov_12, hv2]
      ring
    linarith [h2]
  exact ⟨hco_eq, hpencil, by linarith [hpencil, hv_ab.2.1]⟩

/-- Exact completing-the-square variance identity
`Var_Q(Var_Q(w₂, x) • w₁ - Cov_Q(w₁, w₂, x) • w₂, x) = Var_Q(w₂, x) * Det_Q(w₁, w₂, x)`,
unconditional Gram determinant nonnegativity `0 ≤ Det_Q(w₁, w₂, x)`, and multiplicative
Cauchy-Schwarz inequality `Cov_Q(w₁, w₂, x)^2 ≤ Var_Q(w₁, x) * Var_Q(w₂, x)`. -/
theorem multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) :
    multiChannelSpectralVarianceFunctional P
      (fun q => multiChannelSpectralVarianceFunctional P w₂ x * w₁ q -
        multiChannelSpectralCovarianceFunctional P w₁ w₂ x * w₂ q) x =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x := by
  let A := multiChannelSpectralVarianceFunctional P w₁ x
  let C := multiChannelSpectralVarianceFunctional P w₂ x
  let B := multiChannelSpectralCovarianceFunctional P w₁ w₂ x
  have hcomp_raw := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₁ C (-B) x).2.1
  have hfun_eq :
      (fun q => C * w₁ q - B * w₂ q) = (fun q => C * w₁ q + (-B) * w₂ q) := by
    ext q
    ring
  have hcomp :
      multiChannelSpectralVarianceFunctional P (fun q => C * w₁ q - B * w₂ q) x =
        C * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
    rw [hfun_eq, hcomp_raw]
    dsimp only [multiChannelSpectralCovarianceGramDeterminant, A, B, C]
    ring
  have hA_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).2.1
  have hC_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).2.1
  have hcomp_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => C * w₁ q - B * w₂ q) x).2.1
  have hdet_nn : 0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
    by_cases hC0 : C = 0
    · have hpencil0 : 0 ≤ B ^ 2 * A + 2 * B * (-(A + 1)) * B + (-(A + 1)) ^ 2 * C :=
        (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
          P w₁ w₂ w₁ B (-(A + 1)) x).2.2
      rw [hC0] at hpencil0
      have hrew :
          B ^ 2 * A + 2 * B * (-(A + 1)) * B + (-(A + 1)) ^ 2 * 0 = -((A + 2) * B ^ 2) := by
        ring
      rw [hrew] at hpencil0
      have hB2_nn : 0 ≤ B ^ 2 := sq_nonneg B
      have hB2_zero : B ^ 2 = 0 := by nlinarith [hpencil0, hA_nn, hB2_nn]
      dsimp only [multiChannelSpectralCovarianceGramDeterminant]
      change 0 ≤ A * C - B ^ 2
      rw [hC0, hB2_zero]
      norm_num
    · have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC0)
      nlinarith [hcomp, hcomp_nn, hC_pos]
  have hcs : B ^ 2 ≤ A * C := by
    dsimp only [multiChannelSpectralCovarianceGramDeterminant] at hdet_nn
    linarith [hdet_nn]
  exact ⟨hcomp, hdet_nn, hcs⟩

/-- Exact $\mathrm{GL}_2(\mathbb{R})$ determinant scaling law
`Det_Q(a • w₁ + b • w₂, c • w₁ + d • w₂, x) = (a * d - b * c)^2 * Det_Q(w₁, w₂, x)`,
unimodular $\mathrm{SL}_2(\mathbb{R})$ shear invariance
`Det_Q(w₁ + c • w₂, w₂, x) = Det_Q(w₁, w₂, x)`, and bilateral shift invariance
`Det_Q(w₁ + c₁, w₂ + c₂, x) = Det_Q(w₁, w₂, x)`. -/
theorem multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (a b c d c₁ c₂ : ℝ) (x : E) :
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) x =
      (a * d - b * c) ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
    multiChannelSpectralCovarianceGramDeterminant P (fun q => w₁ q + c * w₂ q) w₂ x =
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x =
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
  have hv_ab := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₁ a b x).2.1
  have hv_cd := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₁ c d x).2.1
  have hcov_left := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ (fun q => c * w₁ q + d * w₂ q) a b x).1
  have hsymm1 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ (fun q => c * w₁ q + d * w₂ q) x).2.1
  have hsymm2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ (fun q => c * w₁ q + d * w₂ q) x).2.1
  have hcov_r1 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₁ c d x).1
  have hcov_r2 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
    P w₁ w₂ w₂ c d x).1
  have hdiag1 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ x).2.2
  have hdiag2 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ w₁ x).2.2
  have hsymm12 := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₂ w₁ x).2.1
  have hcov_abcd :
      multiChannelSpectralCovarianceFunctional P
        (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) x =
      a * c * multiChannelSpectralVarianceFunctional P w₁ x +
        (a * d + b * c) * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        b * d * multiChannelSpectralVarianceFunctional P w₂ x := by
    rw [hcov_left, hsymm1, hsymm2, hcov_r1, hcov_r2, hdiag1, hdiag2, hsymm12]
    ring
  have hgl2 :
      multiChannelSpectralCovarianceGramDeterminant P
        (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) x =
      (a * d - b * c) ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
    unfold multiChannelSpectralCovarianceGramDeterminant
    rw [hv_ab, hv_cd, hcov_abcd]
    ring
  have hshear_fun1 : (fun q => w₁ q + c * w₂ q) = (fun q => 1 * w₁ q + c * w₂ q) := by
    ext q
    ring
  have hshear_fun2 : w₂ = (fun q => 0 * w₁ q + 1 * w₂ q) := by
    ext q
    ring
  have hshear :
      multiChannelSpectralCovarianceGramDeterminant P (fun q => w₁ q + c * w₂ q) w₂ x =
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
    have hgl_sp := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
      P w₁ w₂ w₁ 1 c x).2.1
    have hcov_sp :
        multiChannelSpectralCovarianceFunctional P (fun q => w₁ q + c * w₂ q) w₂ x =
          multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
            c * multiChannelSpectralVarianceFunctional P w₂ x := by
      have h1 := (multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
        P w₁ w₂ w₂ 1 c x).1
      rw [← hshear_fun1, hdiag2] at h1
      linarith [h1]
    have hv_sp :
        multiChannelSpectralVarianceFunctional P (fun q => w₁ q + c * w₂ q) x =
          multiChannelSpectralVarianceFunctional P w₁ x +
            2 * c * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
            c ^ 2 * multiChannelSpectralVarianceFunctional P w₂ x := by
      rw [← hshear_fun1] at hgl_sp
      linarith [hgl_sp]
    unfold multiChannelSpectralCovarianceGramDeterminant
    rw [hv_sp, hcov_sp]
    ring
  have hsh_v1 := (multiChannelSpectralVarianceFunctional_shift_invariance P w₁ c₁ x).2
  have hsh_v2 := (multiChannelSpectralVarianceFunctional_shift_invariance P w₂ c₂ x).2
  have hsh_cov := (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    P w₁ w₂ c₁ c₂ x).2
  have hshift :
      multiChannelSpectralCovarianceGramDeterminant P
        (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x =
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x := by
    unfold multiChannelSpectralCovarianceGramDeterminant
    rw [hsh_v1, hsh_v2, hsh_cov]
  exact ⟨hgl2, hshear, hshift⟩

/-- Multiplicative Cauchy-Schwarz inequality, Gram determinant upper bound, and sharp
multiplicative Popoviciu variance-product and covariance-squared bounds
`Cov_Q(w₁, w₂, x)^2 ≤ Var_Q(w₁, x) * Var_Q(w₂, x) ≤ ((w₁_max - w₁_min)/2)^2 * ((w₂_max - w₂_min)/2)^2 * E_Q(x)^4`. -/
theorem multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E) :
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        (multiChannelProjectedEnergy P x) ^ 4 ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        (multiChannelProjectedEnergy P x) ^ 4 := by
  have hcs := (multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
    P w₁ w₂ x).2.2
  have hdet_le :
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x := by
    unfold multiChannelSpectralCovarianceGramDeterminant
    linarith [sq_nonneg (multiChannelSpectralCovarianceFunctional P w₁ w₂ x)]
  have hv1_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).2.1
  have hv2_nn := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).2.1
  have hpop₁ := (multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w₁ w₁_min w₁_max hmin₁ hmax₁ x).2.2
  have hpop₂ := (multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w₂ w₂_min w₂_max hmin₂ hmax₂ x).2.2
  have hprod_raw := mul_le_mul hpop₁ hpop₂ hv2_nn
    (mul_nonneg (sq_nonneg ((w₁_max - w₁_min) / 2)) (sq_nonneg (multiChannelProjectedEnergy P x)))
  have hprod :
      multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P x) ^ 4 := by
    calc
      multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x
        ≤ (((w₁_max - w₁_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2) *
            (((w₂_max - w₂_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2) := hprod_raw
      _ = ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
            (multiChannelProjectedEnergy P x) ^ 4 := by ring
  exact ⟨hcs, hdet_le, hprod, hcs.trans hprod⟩

/-- `Q`-channel $2 \times 2$ spectral covariance Gram determinant nonnegativity, multiplicative
Cauchy-Schwarz inequality, $\mathrm{GL}_2(\mathbb{R})$ determinant scaling, and multiplicative
Popoviciu bounds on `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_multiChannel_gramDeterminant_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (a b c d w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c_poly : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c_poly PK
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ) ^ 2 ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ *
        multiChannelSpectralVarianceFunctional P w₂ Ψ ∧
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) Ψ =
      (a * d - b * c) ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ) ^ 2 ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        (multiChannelProjectedEnergy P Ψ) ^ 4 := by
  intro Ψ
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ Ψ
  have hgl := multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
    P w₁ w₂ a b c d 0 0 Ψ
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ Ψ
  exact ⟨hcs.2.1, hcs.2.2, hgl.1, hpop.2.2.2⟩

/-- Master Synthesis of the Finite `Q`-Channel $2 \times 2$ Spectral Covariance Gram Determinant,
Completing-the-Square Identity, Multiplicative Cauchy-Schwarz Inequality, $\mathrm{GL}_2(\mathbb{R})$
Determinant Scaling, Bilateral Shift Invariance, and Sharp Multiplicative Popoviciu Bounds on
Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_multiChannel_spectralCovariance_gramDeterminant_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (a b c d c₁_shift c₂_shift w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (M : ℕ) (c_poly : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c_poly
      (identicalPackets ψ)
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ) ^ 2 ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ *
        multiChannelSpectralVarianceFunctional P w₂ Ψ ∧
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) Ψ =
      (a * d - b * c) ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ ∧
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => w₁ q + c₁_shift) (fun q => w₂ q + c₂_shift) Ψ =
      multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ Ψ ∧
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ) ^ 2 ≤
      ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
        (multiChannelProjectedEnergy P Ψ) ^ 4 := by
  intro Ψ
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ Ψ
  have hgl := multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
    P w₁ w₂ a b c d c₁_shift c₂_shift Ψ
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ Ψ
  exact ⟨hcs.2.1, hcs.2.2, hgl.1, hgl.2.2, hpop.2.2.2⟩

end MultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarz

#print axioms multiChannelSpectralCovariance_linear_combination_and_quadratic_pencil
#print axioms multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
#print axioms multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
#print axioms multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
#print axioms arbitrarySourceDegreeMPolyState_multiChannel_gramDeterminant_package
#print axioms arbitrary_source_multiChannel_spectralCovariance_gramDeterminant_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
