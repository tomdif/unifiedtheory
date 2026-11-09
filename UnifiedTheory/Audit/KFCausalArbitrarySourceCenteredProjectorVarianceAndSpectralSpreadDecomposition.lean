/- Normalized Three-Channel Spectral Variance Functional, Exact Lagrange Pairwise
Channel-Spread Identity, Bhatia-Davis Variance-Deficit Decomposition, and Two-Sided
Variance Envelope Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyResponse)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (hilbertEnergy)
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
  (AreMutuallyOrthogonalProjections residualTwoProjector
   twoProjector_three_channel_parseval_decomposition)
open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
  (threeChannelWeightedExpectation
   threeChannelWeightedExpectation_rayleigh_ritz_bounds)
open UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
  (threeChannelWeightedSecondMoment
   threeChannelBhatiaDavisFunctional
   threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
   threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound)

section CenteredSpectralVarianceAndLagrangeSpread

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma hilbertEnergy_nonneg (x : E) : 0 ≤ hilbertEnergy x := by
  unfold hilbertEnergy
  exact @inner_self_nonneg ℂ E _ _ _ x

/-- Homogeneous degree-4 three-channel spectral variance functional:
`hilbertEnergy x * threeChannelWeightedSecondMoment - (threeChannelWeightedExpectation)^2`. -/
def threeChannelSpectralVarianceFunctional
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res : ℝ) (x : E) : ℝ :=
  hilbertEnergy x * threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x -
    (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) ^ 2

/-- Pairwise channel-spread (Lagrange / Cauchy-Binet) sum across the three mutually orthogonal
channels `P₁ x`, `P₂ x`, and `residualTwoProjector P₁ P₂ x`. -/
def threeChannelLagrangePairwiseSpread
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res : ℝ) (x : E) : ℝ :=
  (w₁ - w₂) ^ 2 * hilbertEnergy (P₁ x) * hilbertEnergy (P₂ x) +
    (w₁ - w_res) ^ 2 * hilbertEnergy (P₁ x) * hilbertEnergy (residualTwoProjector P₁ P₂ x) +
    (w₂ - w_res) ^ 2 * hilbertEnergy (P₂ x) * hilbertEnergy (residualTwoProjector P₁ P₂ x)

/-- Exact Lagrange pairwise channel-spread identity and unconditional Cauchy-Schwarz nonnegativity
for `threeChannelSpectralVarianceFunctional` when `AreMutuallyOrthogonalProjections P₁ P₂`. -/
theorem threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
    0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₁ w₁ x = 0 := by
  have he1 : 0 ≤ hilbertEnergy (P₁ x) := hilbertEnergy_nonneg (P₁ x)
  have he2 : 0 ≤ hilbertEnergy (P₂ x) := hilbertEnergy_nonneg (P₂ x)
  have her : 0 ≤ hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_nonneg (residualTwoProjector P₁ P₂ x)
  have hparseval := (twoProjector_three_channel_parseval_decomposition hP x).2
  have hid :
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
        threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x := by
    unfold threeChannelSpectralVarianceFunctional threeChannelLagrangePairwiseSpread
      threeChannelWeightedSecondMoment threeChannelWeightedExpectation
    rw [hparseval]
    ring
  have hnn : 0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x := by
    rw [hid]
    unfold threeChannelLagrangePairwiseSpread
    positivity
  have hconst : threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₁ w₁ x = 0 := by
    have hid_c :
        threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₁ w₁ x =
          threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₁ w₁ x := by
      unfold threeChannelSpectralVarianceFunctional threeChannelLagrangePairwiseSpread
        threeChannelWeightedSecondMoment threeChannelWeightedExpectation
      rw [hparseval]
      ring
    rw [hid_c]
    unfold threeChannelLagrangePairwiseSpread
    ring
  exact ⟨hid, hnn, hconst⟩

/-- Exact algebraic deficit identity relating `hilbertEnergy x * threeChannelBhatiaDavisFunctional`
and `threeChannelSpectralVarianceFunctional`:
`E(x) * BD(x) + Var(x) = (w_max * E(x) - M₁(x)) * (M₁(x) - w_min * E(x))`. -/
theorem threeChannelBhatiaDavis_mul_energy_sub_spectralVariance_eq_rayleigh_deficit
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res w_min w_max : ℝ) (x : E) :
    hilbertEnergy x * threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x +
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) := by
  unfold threeChannelBhatiaDavisFunctional threeChannelSpectralVarianceFunctional
  ring

/-- Exact Bhatia-Davis variance inequality
`threeChannelSpectralVarianceFunctional ≤ (w_max * E(x) - M₁(x)) * (M₁(x) - w_min * E(x))`
and sharp Popoviciu / Bhatia-Davis variance upper bound
`threeChannelSpectralVarianceFunctional ≤ ((w_max - w_min) / 2)^2 * (hilbertEnergy x)^2`. -/
theorem threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
      (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
      ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 := by
  have hvar := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  have hdef := threeChannelBhatiaDavis_mul_energy_sub_spectralVariance_eq_rayleigh_deficit
    P₁ P₂ w₁ w₂ w_res w_min w_max x
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  have hex : 0 ≤ hilbertEnergy x := hilbertEnergy_nonneg x
  have hbd_nn : 0 ≤ hilbertEnergy x * threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x :=
    mul_nonneg hex hbd.1
  have hle_bd :
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
        (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
          (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) := by
    linarith
  have hsq :
      0 ≤ (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x -
        ((w_max + w_min) / 2) * hilbertEnergy x) ^ 2 :=
    sq_nonneg _
  have hring :
      ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 -
        (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
          (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) =
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x -
          ((w_max + w_min) / 2) * hilbertEnergy x) ^ 2 := by ring
  exact ⟨hvar.2.1, hle_bd, by linarith⟩

/-- Translation invariance `wᵢ ↦ wᵢ + c` of `threeChannelSpectralVarianceFunctional` and
`threeChannelLagrangePairwiseSpread`. -/
theorem threeChannelSpectralVarianceFunctional_shift_invariance
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res c : ℝ) (x : E) :
    threeChannelLagrangePairwiseSpread P₁ P₂ (w₁ + c) (w₂ + c) (w_res + c) x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ (w₁ + c) (w₂ + c) (w_res + c) x =
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x := by
  have h1 :
      threeChannelLagrangePairwiseSpread P₁ P₂ (w₁ + c) (w₂ + c) (w_res + c) x =
        threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x := by
    unfold threeChannelLagrangePairwiseSpread
    ring
  have hvar_shift := (threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP (w₁ + c) (w₂ + c) (w_res + c) x).1
  have hvar_base := (threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x).1
  exact ⟨h1, by rw [hvar_shift, h1, ← hvar_base]⟩

/-- Three-channel spectral variance Lagrange spread decomposition and Popoviciu variance-squared
bounds on `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_threeChannel_spectralVariance_package
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w b c PK
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ =
      (w₁ - w₂) ^ 2 *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₁ M w b c PK) *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₂ M w b c PK) +
      (w₁ - w_res) ^ 2 *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₁ M w b c PK) *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK) +
      (w₂ - w_res) ^ 2 *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₂ M w b c PK) *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK) ∧
    0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ≤
      ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy Ψ) ^ 2 := by
  intro Ψ
  have hlag := (threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res Ψ).1
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  exact ⟨hlag, hbd.1, hbd.2.2⟩

/-- Master Synthesis of Normalized Spectral Variance, Lagrange Pairwise Channel-Spread
Identity, Shift Invariance, and Bhatia-Davis / Popoviciu Variance Envelope Bounds on
Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_centered_projector_variance_and_spread_master_synthesis
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res c_shift w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
      (identicalPackets ψ)
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res Ψ ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ (w₁ + c_shift) (w₂ + c_shift) (w_res + c_shift) Ψ =
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ∧
    0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ≤
      (w_max * hilbertEnergy Ψ - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ) *
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ - w_min * hilbertEnergy Ψ) ∧
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res Ψ ≤
      ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy Ψ) ^ 2 := by
  intro Ψ
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res Ψ
  have hsh := threeChannelSpectralVarianceFunctional_shift_invariance
    hP w₁ w₂ w_res c_shift Ψ
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  exact ⟨hlag.1, hsh.2, hbd.1, hbd.2.1, hbd.2.2⟩

end CenteredSpectralVarianceAndLagrangeSpread

#print axioms threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
#print axioms threeChannelBhatiaDavis_mul_energy_sub_spectralVariance_eq_rayleigh_deficit
#print axioms threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
#print axioms threeChannelSpectralVarianceFunctional_shift_invariance
#print axioms arbitrarySourceDegreeMPolyState_threeChannel_spectralVariance_package
#print axioms arbitrary_source_centered_projector_variance_and_spread_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
