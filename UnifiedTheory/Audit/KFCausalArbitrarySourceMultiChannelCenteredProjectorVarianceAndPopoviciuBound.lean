/- Finite `Q`-Channel Normalized Spectral Variance Functional, Exact `Q`-Channel Double-Sum
Lagrange Pairwise Spread Identity, Bhatia-Davis Variance-Deficit Decomposition, and Popoviciu
Variance-Squared Envelope Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyResponse)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (hilbertEnergy)
open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
  (multiChannelWeightedExpectation
   multiChannelWeightedExpectation_rayleigh_ritz_bounds)
open UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
  (multiChannelWeightedSecondMoment
   multiChannelBhatiaDavisFunctional
   multiChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
   multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound)

section MultiChannelCenteredSpectralVarianceAndLagrangeSpread

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma hilbertEnergy_nonneg (x : E) : 0 ≤ hilbertEnergy x := by
  unfold hilbertEnergy
  exact @inner_self_nonneg ℂ E _ _ _ x

/-- Total projected Hilbert energy `∑ q : Fin Q, hilbertEnergy (P q x)` across a finite `Q`-channel
operator family `P : Fin Q → (E →L[ℂ] E)`. -/
def multiChannelProjectedEnergy {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (x : E) : ℝ :=
  ∑ q : Fin Q, hilbertEnergy (P q x)

/-- Homogeneous degree-4 `Q`-channel normalized spectral variance functional:
`multiChannelProjectedEnergy P x * multiChannelWeightedSecondMoment P w x - (multiChannelWeightedExpectation P w x)^2`. -/
def multiChannelSpectralVarianceFunctional
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelProjectedEnergy P x * multiChannelWeightedSecondMoment P w x -
    (multiChannelWeightedExpectation P w x) ^ 2

/-- Double-sum `Q × Q` Lagrange pairwise channel-spread functional
`∑ q₁ : Fin Q, ∑ q₂ : Fin Q, (w q₁ - w q₂)^2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)`. -/
def multiChannelLagrangeDoubleSpread
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (x : E) : ℝ :=
  ∑ q₁ : Fin Q, ∑ q₂ : Fin Q,
    (w q₁ - w q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x)

/-- Exact `Q × Q` Lagrange double-sum pairwise channel-spread identity
`multiChannelLagrangeDoubleSpread P w x = 2 * multiChannelSpectralVarianceFunctional P w x`
and unconditional Cauchy-Schwarz nonnegativity `0 ≤ multiChannelSpectralVarianceFunctional P w x`
for every `Q : ℕ`, `P : Fin Q → (E →L[ℂ] E)`, `w : Fin Q → ℝ`, and `x : E`. -/
theorem multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (x : E) :
    multiChannelLagrangeDoubleSpread P w x =
      2 * multiChannelSpectralVarianceFunctional P w x ∧
    0 ≤ multiChannelSpectralVarianceFunctional P w x ∧
    multiChannelSpectralVarianceFunctional P (fun _ => 0) x = 0 := by
  have hterm : ∀ q₁ q₂ : Fin Q,
      (w q₁ - w q₂) ^ 2 * hilbertEnergy (P q₁ x) * hilbertEnergy (P q₂ x) =
        ((w q₁) ^ 2 * hilbertEnergy (P q₁ x)) * hilbertEnergy (P q₂ x) +
        hilbertEnergy (P q₁ x) * ((w q₂) ^ 2 * hilbertEnergy (P q₂ x)) -
        2 * ((w q₁ * hilbertEnergy (P q₁ x)) * (w q₂ * hilbertEnergy (P q₂ x))) := by
    intro q₁ q₂
    ring
  have hsum_id :
      multiChannelLagrangeDoubleSpread P w x =
        2 * multiChannelSpectralVarianceFunctional P w x := by
    unfold multiChannelLagrangeDoubleSpread multiChannelSpectralVarianceFunctional
      multiChannelProjectedEnergy multiChannelWeightedSecondMoment
      multiChannelWeightedExpectation
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnn_double : 0 ≤ multiChannelLagrangeDoubleSpread P w x := by
    unfold multiChannelLagrangeDoubleSpread
    refine Finset.sum_nonneg (fun q₁ _ => Finset.sum_nonneg (fun q₂ _ => ?_))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hilbertEnergy_nonneg (P q₁ x)))
      (hilbertEnergy_nonneg (P q₂ x))
  have hnn : 0 ≤ multiChannelSpectralVarianceFunctional P w x := by
    linarith [hsum_id, hnn_double]
  have hzero : multiChannelSpectralVarianceFunctional P (fun _ => 0) x = 0 := by
    unfold multiChannelSpectralVarianceFunctional multiChannelWeightedSecondMoment
      multiChannelWeightedExpectation
    simp
  exact ⟨hsum_id, hnn, hzero⟩

/-- Exact algebraic deficit identity relating `multiChannelProjectedEnergy P x * multiChannelBhatiaDavisFunctional`
and `multiChannelSpectralVarianceFunctional`:
`E_Q(x) * BD_Q(x) + Var_Q(x) = (w_max * E_Q(x) - M₁(x)) * (M₁(x) - w_min * E_Q(x))`. -/
theorem multiChannelBhatiaDavis_mul_energy_add_spectralVariance_eq_rayleigh_deficit
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ) (x : E) :
    multiChannelProjectedEnergy P x * multiChannelBhatiaDavisFunctional P w w_min w_max x +
      multiChannelSpectralVarianceFunctional P w x =
      (w_max * multiChannelProjectedEnergy P x - multiChannelWeightedExpectation P w x) *
        (multiChannelWeightedExpectation P w x - w_min * multiChannelProjectedEnergy P x) := by
  unfold multiChannelBhatiaDavisFunctional multiChannelSpectralVarianceFunctional
    multiChannelProjectedEnergy
  ring

/-- Exact `Q`-channel Bhatia-Davis variance inequality
`multiChannelSpectralVarianceFunctional ≤ (w_max * E_Q(x) - M₁(x)) * (M₁(x) - w_min * E_Q(x))`
and sharp `Q`-channel Popoviciu / Bhatia-Davis variance-squared upper bound
`multiChannelSpectralVarianceFunctional ≤ ((w_max - w_min) / 2)^2 * (multiChannelProjectedEnergy P x)^2`. -/
theorem multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E) :
    0 ≤ multiChannelSpectralVarianceFunctional P w x ∧
    multiChannelSpectralVarianceFunctional P w x ≤
      (w_max * multiChannelProjectedEnergy P x - multiChannelWeightedExpectation P w x) *
        (multiChannelWeightedExpectation P w x - w_min * multiChannelProjectedEnergy P x) ∧
    multiChannelSpectralVarianceFunctional P w x ≤
      ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2 := by
  have hvar := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w x
  have hdef := multiChannelBhatiaDavis_mul_energy_add_spectralVariance_eq_rayleigh_deficit
    P w w_min w_max x
  have hbd := multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    P w w_min w_max hmin hmax x
  have he_nn : 0 ≤ multiChannelProjectedEnergy P x := by
    unfold multiChannelProjectedEnergy
    exact Finset.sum_nonneg (fun q _ => hilbertEnergy_nonneg (P q x))
  have hbd_nn : 0 ≤ multiChannelProjectedEnergy P x * multiChannelBhatiaDavisFunctional P w w_min w_max x :=
    mul_nonneg he_nn hbd.1
  have hle_bd :
      multiChannelSpectralVarianceFunctional P w x ≤
        (w_max * multiChannelProjectedEnergy P x - multiChannelWeightedExpectation P w x) *
          (multiChannelWeightedExpectation P w x - w_min * multiChannelProjectedEnergy P x) := by
    linarith
  have hsq :
      0 ≤ (multiChannelWeightedExpectation P w x -
        ((w_max + w_min) / 2) * multiChannelProjectedEnergy P x) ^ 2 :=
    sq_nonneg _
  have hring :
      ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2 -
        (w_max * multiChannelProjectedEnergy P x - multiChannelWeightedExpectation P w x) *
          (multiChannelWeightedExpectation P w x - w_min * multiChannelProjectedEnergy P x) =
        (multiChannelWeightedExpectation P w x -
          ((w_max + w_min) / 2) * multiChannelProjectedEnergy P x) ^ 2 := by ring
  exact ⟨hvar.2.1, hle_bd, by linarith⟩

/-- Translation invariance `w q ↦ w q + c` of `multiChannelLagrangeDoubleSpread` and
`multiChannelSpectralVarianceFunctional` for any `Q : ℕ`. -/
theorem multiChannelSpectralVarianceFunctional_shift_invariance
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (c : ℝ) (x : E) :
    multiChannelLagrangeDoubleSpread P (fun q => w q + c) x =
      multiChannelLagrangeDoubleSpread P w x ∧
    multiChannelSpectralVarianceFunctional P (fun q => w q + c) x =
      multiChannelSpectralVarianceFunctional P w x := by
  have h1 :
      multiChannelLagrangeDoubleSpread P (fun q => w q + c) x =
        multiChannelLagrangeDoubleSpread P w x := by
    unfold multiChannelLagrangeDoubleSpread
    refine Finset.sum_congr rfl (fun q₁ _ => Finset.sum_congr rfl (fun q₂ _ => ?_))
    ring
  have hvar_shift := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P (fun q => w q + c) x).1
  have hvar_base := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
    P w x).1
  exact ⟨h1, by linarith⟩

/-- `Q`-channel normalized spectral variance Lagrange spread decomposition and Popoviciu
variance-squared bounds on `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_multiChannel_spectralVariance_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c PK
    2 * multiChannelSpectralVarianceFunctional P w Ψ =
      ∑ q₁ : Fin Q, ∑ q₂ : Fin Q,
        (w q₁ - w q₂) ^ 2 *
          hilbertEnergy (arbitrarySourceDegreeMPolyResponse (P q₁) M w_src b_src c PK) *
          hilbertEnergy (arbitrarySourceDegreeMPolyResponse (P q₂) M w_src b_src c PK) ∧
    0 ≤ multiChannelSpectralVarianceFunctional P w Ψ ∧
    multiChannelSpectralVarianceFunctional P w Ψ ≤
      ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P Ψ) ^ 2 := by
  intro Ψ
  have hlag := (multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w Ψ).1
  have hbd := multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w w_min w_max hmin hmax Ψ
  exact ⟨hlag.symm, hbd.1, hbd.2.2⟩

/-- Master Synthesis of Finite `Q`-Channel Normalized Spectral Variance, `Q × Q` Double-Sum
Lagrange Pairwise Spread Identity, Shift Invariance, and Bhatia-Davis / Popoviciu Variance
Envelope Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_multiChannel_centered_projector_variance_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (c_shift w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
      (identicalPackets ψ)
    multiChannelLagrangeDoubleSpread P w Ψ =
      2 * multiChannelSpectralVarianceFunctional P w Ψ ∧
    multiChannelSpectralVarianceFunctional P (fun q => w q + c_shift) Ψ =
      multiChannelSpectralVarianceFunctional P w Ψ ∧
    0 ≤ multiChannelSpectralVarianceFunctional P w Ψ ∧
    multiChannelSpectralVarianceFunctional P w Ψ ≤
      (w_max * multiChannelProjectedEnergy P Ψ - multiChannelWeightedExpectation P w Ψ) *
        (multiChannelWeightedExpectation P w Ψ - w_min * multiChannelProjectedEnergy P Ψ) ∧
    multiChannelSpectralVarianceFunctional P w Ψ ≤
      ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P Ψ) ^ 2 := by
  intro Ψ
  have hlag := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w Ψ
  have hsh := multiChannelSpectralVarianceFunctional_shift_invariance P w c_shift Ψ
  have hbd := multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w w_min w_max hmin hmax Ψ
  exact ⟨hlag.1, hsh.2, hbd.1, hbd.2.1, hbd.2.2⟩

end MultiChannelCenteredSpectralVarianceAndLagrangeSpread

#print axioms multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
#print axioms multiChannelBhatiaDavis_mul_energy_add_spectralVariance_eq_rayleigh_deficit
#print axioms multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
#print axioms multiChannelSpectralVarianceFunctional_shift_invariance
#print axioms arbitrarySourceDegreeMPolyState_multiChannel_spectralVariance_package
#print axioms arbitrary_source_multiChannel_centered_projector_variance_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
