/- Finite `Q`-Channel Normalized Spectral Covariance Functional, Exact `Q × Q` Double-Sum Bilinear
Lagrange Pairwise Co-Spread Identity, Sum/Difference Variance Polarization Identities, Bilateral
Shift Invariance, and Arithmetic-Mean / Popoviciu Covariance Envelope Bounds on Arbitrary-Source
Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyResponse)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (hilbertEnergy)
open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
  (multiChannelWeightedExpectation)
open UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
  (multiChannelWeightedSecondMoment)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelLagrangeDoubleSpread
   multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
   multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
   multiChannelSpectralVarianceFunctional_shift_invariance)

section MultiChannelCenteredSpectralCovarianceAndLagrangeCoSpread

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Cross-weighted second moment `∑ q : Fin Q, (w₁ q * w₂ q) * hilbertEnergy (P q x)` across a
finite `Q`-channel operator family `P : Fin Q → (E →L[ℂ] E)` and two real weight profiles
`w₁ w₂ : Fin Q → ℝ`. -/
def multiChannelWeightedCrossSecondMoment
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) : ℝ :=
  ∑ q : Fin Q, (w₁ q * w₂ q) * hilbertEnergy (P q x)

/-- Homogeneous degree-4 `Q`-channel normalized spectral covariance functional:
`multiChannelProjectedEnergy P x * multiChannelWeightedCrossSecondMoment P w₁ w₂ x - multiChannelWeightedExpectation P w₁ x * multiChannelWeightedExpectation P w₂ x`. -/
def multiChannelSpectralCovarianceFunctional
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelProjectedEnergy P x * multiChannelWeightedCrossSecondMoment P w₁ w₂ x -
    multiChannelWeightedExpectation P w₁ x * multiChannelWeightedExpectation P w₂ x

/-- Double-sum `Q × Q` bilinear Lagrange pairwise channel co-spread functional
`∑ q₁ : Fin Q, ∑ q₂ : Fin Q, (w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)`. -/
def multiChannelLagrangeDoubleCoSpread
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) : ℝ :=
  ∑ q₁ : Fin Q, ∑ q₂ : Fin Q,
    (w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)

/-- Exact `Q × Q` bilinear Lagrange double-sum pairwise channel co-spread identity
`multiChannelLagrangeDoubleCoSpread P w₁ w₂ x = 2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x`,
symmetry `Cov(w₁, w₂) = Cov(w₂, w₁)`, and diagonal reduction `Cov(w₁, w₁) = Var(w₁)`. -/
theorem multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) :
    multiChannelLagrangeDoubleCoSpread P w₁ w₂ x =
      2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x ∧
    multiChannelSpectralCovarianceFunctional P w₁ w₂ x =
      multiChannelSpectralCovarianceFunctional P w₂ w₁ x ∧
    multiChannelSpectralCovarianceFunctional P w₁ w₁ x =
      multiChannelSpectralVarianceFunctional P w₁ x := by
  have hterm : ∀ q₁ q₂ : Fin Q,
      (w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
        ((w₁ q₁ * w₂ q₁) * hilbertEnergy (P q₁ x)) * hilbertEnergy (P q₂ x) +
        hilbertEnergy (P q₁ x) * ((w₁ q₂ * w₂ q₂) * hilbertEnergy (P q₂ x)) -
        ((w₁ q₁ * hilbertEnergy (P q₁ x)) * (w₂ q₂ * hilbertEnergy (P q₂ x)) +
         (w₂ q₁ * hilbertEnergy (P q₁ x)) * (w₁ q₂ * hilbertEnergy (P q₂ x))) := by
    intro q₁ q₂
    ring
  have hsum_id :
      multiChannelLagrangeDoubleCoSpread P w₁ w₂ x =
        2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x := by
    unfold multiChannelLagrangeDoubleCoSpread multiChannelSpectralCovarianceFunctional
      multiChannelProjectedEnergy multiChannelWeightedCrossSecondMoment
      multiChannelWeightedExpectation
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hsymm_co :
      multiChannelLagrangeDoubleCoSpread P w₁ w₂ x =
        multiChannelLagrangeDoubleCoSpread P w₂ w₁ x := by
    unfold multiChannelLagrangeDoubleCoSpread
    refine Finset.sum_congr rfl (fun q₁ _ => Finset.sum_congr rfl (fun q₂ _ => ?_))
    ring
  have hsum_id_rev :
      multiChannelLagrangeDoubleCoSpread P w₂ w₁ x =
        2 * multiChannelSpectralCovarianceFunctional P w₂ w₁ x := by
    unfold multiChannelLagrangeDoubleCoSpread multiChannelSpectralCovarianceFunctional
      multiChannelProjectedEnergy multiChannelWeightedCrossSecondMoment
      multiChannelWeightedExpectation
    have hterm_rev : ∀ q₁ q₂ : Fin Q,
        (w₂ q₁ - w₂ q₂) * (w₁ q₁ - w₁ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          ((w₂ q₁ * w₁ q₁) * hilbertEnergy (P q₁ x)) * hilbertEnergy (P q₂ x) +
          hilbertEnergy (P q₁ x) * ((w₂ q₂ * w₁ q₂) * hilbertEnergy (P q₂ x)) -
          ((w₂ q₁ * hilbertEnergy (P q₁ x)) * (w₁ q₂ * hilbertEnergy (P q₂ x)) +
           (w₁ q₁ * hilbertEnergy (P q₁ x)) * (w₂ q₂ * hilbertEnergy (P q₂ x))) := by
      intro q₁ q₂
      ring
    simp_rw [hterm_rev, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hdiag_co :
      multiChannelLagrangeDoubleCoSpread P w₁ w₁ x =
        multiChannelLagrangeDoubleSpread P w₁ x := by
    unfold multiChannelLagrangeDoubleCoSpread multiChannelLagrangeDoubleSpread
    refine Finset.sum_congr rfl (fun q₁ _ => Finset.sum_congr rfl (fun q₂ _ => ?_))
    ring
  have hsum_id_diag :
      multiChannelLagrangeDoubleCoSpread P w₁ w₁ x =
        2 * multiChannelSpectralCovarianceFunctional P w₁ w₁ x := by
    unfold multiChannelLagrangeDoubleCoSpread multiChannelSpectralCovarianceFunctional
      multiChannelProjectedEnergy multiChannelWeightedCrossSecondMoment
      multiChannelWeightedExpectation
    have hterm_diag : ∀ q₁ q₂ : Fin Q,
        (w₁ q₁ - w₁ q₂) * (w₁ q₁ - w₁ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          ((w₁ q₁ * w₁ q₁) * hilbertEnergy (P q₁ x)) * hilbertEnergy (P q₂ x) +
          hilbertEnergy (P q₁ x) * ((w₁ q₂ * w₁ q₂) * hilbertEnergy (P q₂ x)) -
          ((w₁ q₁ * hilbertEnergy (P q₁ x)) * (w₁ q₂ * hilbertEnergy (P q₂ x)) +
           (w₁ q₁ * hilbertEnergy (P q₁ x)) * (w₁ q₂ * hilbertEnergy (P q₂ x))) := by
      intro q₁ q₂
      ring
    simp_rw [hterm_diag, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hvar_id := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).1
  exact ⟨hsum_id, by linarith [hsum_id, hsymm_co, hsum_id_rev],
    by linarith [hdiag_co, hsum_id_diag, hvar_id]⟩

/-- Exact sum and difference variance polarization identities:
`Var(w₁ + w₂) = Var(w₁) + 2 * Cov(w₁, w₂) + Var(w₂)`,
`Var(w₁ - w₂) = Var(w₁) - 2 * Cov(w₁, w₂) + Var(w₂)`, and
`4 * Cov(w₁, w₂) = Var(w₁ + w₂) - Var(w₁ - w₂)`. -/
theorem multiChannelSpectralVarianceFunctional_sum_and_sub_polarization
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (x : E) :
    multiChannelSpectralVarianceFunctional P (fun q => w₁ q + w₂ q) x =
      multiChannelSpectralVarianceFunctional P w₁ x +
        2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    multiChannelSpectralVarianceFunctional P (fun q => w₁ q - w₂ q) x =
      multiChannelSpectralVarianceFunctional P w₁ x -
        2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x +
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    4 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x =
      multiChannelSpectralVarianceFunctional P (fun q => w₁ q + w₂ q) x -
        multiChannelSpectralVarianceFunctional P (fun q => w₁ q - w₂ q) x := by
  have hadd_lag :
      multiChannelLagrangeDoubleSpread P (fun q => w₁ q + w₂ q) x =
        multiChannelLagrangeDoubleSpread P w₁ x +
          2 * multiChannelLagrangeDoubleCoSpread P w₁ w₂ x +
          multiChannelLagrangeDoubleSpread P w₂ x := by
    unfold multiChannelLagrangeDoubleSpread multiChannelLagrangeDoubleCoSpread
    have hpt : ∀ q₁ q₂ : Fin Q,
        (w₁ q₁ + w₂ q₁ - (w₁ q₂ + w₂ q₂)) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          (w₁ q₁ - w₁ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) +
          2 * ((w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) +
          (w₂ q₁ - w₂ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) := by
      intro q₁ q₂
      ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsub_lag :
      multiChannelLagrangeDoubleSpread P (fun q => w₁ q - w₂ q) x =
        multiChannelLagrangeDoubleSpread P w₁ x -
          2 * multiChannelLagrangeDoubleCoSpread P w₁ w₂ x +
          multiChannelLagrangeDoubleSpread P w₂ x := by
    unfold multiChannelLagrangeDoubleSpread multiChannelLagrangeDoubleCoSpread
    have hpt : ∀ q₁ q₂ : Fin Q,
        (w₁ q₁ - w₂ q₁ - (w₁ q₂ - w₂ q₂)) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
          (w₁ q₁ - w₁ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) -
          2 * ((w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)) +
          (w₂ q₁ - w₂ q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) := by
      intro q₁ q₂
      ring
    simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hv_add := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => w₁ q + w₂ q) x).1
  have hv_sub := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => w₁ q - w₂ q) x).1
  have hv1 := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₁ x).1
  have hv2 := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w₂ x).1
  have hcov := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ x).1
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Arithmetic-mean Cauchy-Schwarz covariance inequality
`2 * |Cov(w₁, w₂)| ≤ Var(w₁) + Var(w₂)` and two-profile Popoviciu covariance envelope bound
`2 * |Cov(w₁, w₂)| ≤ (((w₁_max - w₁_min)/2)^2 + ((w₂_max - w₂_min)/2)^2) * E_Q(x)^2`. -/
theorem multiChannelSpectralCovarianceFunctional_arithmetic_mean_and_popoviciu_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E) :
    -(multiChannelSpectralVarianceFunctional P w₁ x +
        multiChannelSpectralVarianceFunctional P w₂ x) ≤
      2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x ∧
    2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x +
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ x| ≤
      multiChannelSpectralVarianceFunctional P w₁ x +
        multiChannelSpectralVarianceFunctional P w₂ x ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ x| ≤
      (((w₁_max - w₁_min) / 2) ^ 2 + ((w₂_max - w₂_min) / 2) ^ 2) *
        (multiChannelProjectedEnergy P x) ^ 2 := by
  have hpol := multiChannelSpectralVarianceFunctional_sum_and_sub_polarization P w₁ w₂ x
  have hnn_add := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => w₁ q + w₂ q) x).2.1
  have hnn_sub := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => w₁ q - w₂ q) x).2.1
  have hlow :
      -(multiChannelSpectralVarianceFunctional P w₁ x +
          multiChannelSpectralVarianceFunctional P w₂ x) ≤
        2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x := by
    linarith [hpol.1, hnn_add]
  have hhigh :
      2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x ≤
        multiChannelSpectralVarianceFunctional P w₁ x +
          multiChannelSpectralVarianceFunctional P w₂ x := by
    linarith [hpol.2.1, hnn_sub]
  have habs :
      2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ x| ≤
        multiChannelSpectralVarianceFunctional P w₁ x +
          multiChannelSpectralVarianceFunctional P w₂ x := by
    rcases le_or_gt 0 (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      exact hhigh
    · rw [abs_of_neg hneg]
      linarith [hlow]
  have hpop₁ := (multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w₁ w₁_min w₁_max hmin₁ hmax₁ x).2.2
  have hpop₂ := (multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w₂ w₂_min w₂_max hmin₂ hmax₂ x).2.2
  exact ⟨hlow, hhigh, habs, by linarith [habs, hpop₁, hpop₂]⟩

/-- Bilateral translation invariance `(w₁ q + c₁, w₂ q + c₂)` of `multiChannelLagrangeDoubleCoSpread`
and `multiChannelSpectralCovarianceFunctional` for any `Q : ℕ`. -/
theorem multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (c₁ c₂ : ℝ) (x : E) :
    multiChannelLagrangeDoubleCoSpread P (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x =
      multiChannelLagrangeDoubleCoSpread P w₁ w₂ x ∧
    multiChannelSpectralCovarianceFunctional P (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x =
      multiChannelSpectralCovarianceFunctional P w₁ w₂ x := by
  have h1 :
      multiChannelLagrangeDoubleCoSpread P (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x =
        multiChannelLagrangeDoubleCoSpread P w₁ w₂ x := by
    unfold multiChannelLagrangeDoubleCoSpread
    refine Finset.sum_congr rfl (fun q₁ _ => Finset.sum_congr rfl (fun q₂ _ => ?_))
    ring
  have hcov_shift := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P (fun q => w₁ q + c₁) (fun q => w₂ q + c₂) x).1
  have hcov_base := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ x).1
  exact ⟨h1, by linarith⟩

/-- `Q`-channel normalized spectral covariance Lagrange co-spread decomposition, polarization,
and Popoviciu covariance bounds on `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_multiChannel_spectralCovariance_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c PK
    2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ =
      ∑ q₁ : Fin Q, ∑ q₂ : Fin Q,
        (w₁ q₁ - w₁ q₂) * (w₂ q₁ - w₂ q₂) *
          hilbertEnergy (arbitrarySourceDegreeMPolyResponse (P q₁) M w_src b_src c PK) *
          hilbertEnergy (arbitrarySourceDegreeMPolyResponse (P q₂) M w_src b_src c PK) ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ| ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ +
        multiChannelSpectralVarianceFunctional P w₂ Ψ ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ| ≤
      (((w₁_max - w₁_min) / 2) ^ 2 + ((w₂_max - w₂_min) / 2) ^ 2) *
        (multiChannelProjectedEnergy P Ψ) ^ 2 := by
  intro Ψ
  have hlag := (multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ Ψ).1
  have hbd := multiChannelSpectralCovarianceFunctional_arithmetic_mean_and_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ Ψ
  exact ⟨hlag.symm, hbd.2.2.1, hbd.2.2.2⟩

/-- Master Synthesis of Finite `Q`-Channel Normalized Spectral Covariance, `Q × Q` Bilinear
Lagrange Pairwise Co-Spread Identity, Polarization, Bilateral Shift Invariance, and Arithmetic-Mean
/ Popoviciu Covariance Envelope Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_multiChannel_centered_projector_covariance_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ)
    (c₁_shift c₂_shift w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
      (identicalPackets ψ)
    multiChannelLagrangeDoubleCoSpread P w₁ w₂ Ψ =
      2 * multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ ∧
    multiChannelSpectralCovarianceFunctional P (fun q => w₁ q + c₁_shift)
        (fun q => w₂ q + c₂_shift) Ψ =
      multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ ∧
    4 * multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ =
      multiChannelSpectralVarianceFunctional P (fun q => w₁ q + w₂ q) Ψ -
        multiChannelSpectralVarianceFunctional P (fun q => w₁ q - w₂ q) Ψ ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ| ≤
      multiChannelSpectralVarianceFunctional P w₁ Ψ +
        multiChannelSpectralVarianceFunctional P w₂ Ψ ∧
    2 * |multiChannelSpectralCovarianceFunctional P w₁ w₂ Ψ| ≤
      (((w₁_max - w₁_min) / 2) ^ 2 + ((w₂_max - w₂_min) / 2) ^ 2) *
        (multiChannelProjectedEnergy P Ψ) ^ 2 := by
  intro Ψ
  have hlag := multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
    P w₁ w₂ Ψ
  have hsh := multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
    P w₁ w₂ c₁_shift c₂_shift Ψ
  have hpol := multiChannelSpectralVarianceFunctional_sum_and_sub_polarization P w₁ w₂ Ψ
  have hbd := multiChannelSpectralCovarianceFunctional_arithmetic_mean_and_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ Ψ
  exact ⟨hlag.1, hsh.2, hpol.2.2, hbd.2.2.1, hbd.2.2.2⟩

end MultiChannelCenteredSpectralCovarianceAndLagrangeCoSpread

#print axioms multiChannelSpectralCovarianceFunctional_eq_lagrangeDoubleCoSpread_and_symmetry
#print axioms multiChannelSpectralVarianceFunctional_sum_and_sub_polarization
#print axioms multiChannelSpectralCovarianceFunctional_arithmetic_mean_and_popoviciu_bounds
#print axioms multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance
#print axioms arbitrarySourceDegreeMPolyState_multiChannel_spectralCovariance_package
#print axioms arbitrary_source_multiChannel_centered_projector_covariance_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
