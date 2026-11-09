/- Three-Channel and Finite `Q`-Channel Spectral-Weighted Projector Second Moments,
Bhatia-Davis / Popoviciu Spectral Dispersion Functionals, `((w_max - w_min) / 2)^2`
Variance-Envelope Bounds, and Arbitrary-Source Degree-`M` Polynomial State Instantiations. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality

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
  (threeChannelWeightedExpectation multiChannelWeightedExpectation
   threeChannelWeightedExpectation_rayleigh_ritz_bounds
   multiChannelWeightedExpectation_rayleigh_ritz_bounds)

section WeightedProjectorBhatiaDavisCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma hilbertEnergy_nonneg (x : E) : 0 ≤ hilbertEnergy x := by
  unfold hilbertEnergy
  exact @inner_self_nonneg ℂ E _ _ _ x

private lemma scalar_bhatia_davis_factor_bounds
    {w w_min w_max : ℝ} (hmin : w_min ≤ w) (hmax : w ≤ w_max) :
    0 ≤ (w_max - w) * (w - w_min) ∧
    (w_max - w) * (w - w_min) ≤ ((w_max - w_min) / 2) ^ 2 := by
  have h1 : 0 ≤ w_max - w := sub_nonneg.mpr hmax
  have h2 : 0 ≤ w - w_min := sub_nonneg.mpr hmin
  have hsq : 0 ≤ (w - (w_max + w_min) / 2) ^ 2 := sq_nonneg (w - (w_max + w_min) / 2)
  have hid :
      ((w_max - w_min) / 2) ^ 2 - (w_max - w) * (w - w_min) =
        (w - (w_max + w_min) / 2) ^ 2 := by ring
  exact ⟨mul_nonneg h1 h2, by linarith⟩

/-- Three-channel spectral-weighted second moment
`w₁^2 * hilbertEnergy (P₁ x) + w₂^2 * hilbertEnergy (P₂ x) + w_res^2 * hilbertEnergy (residualTwoProjector P₁ P₂ x)`. -/
def threeChannelWeightedSecondMoment
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res : ℝ) (x : E) : ℝ :=
  threeChannelWeightedExpectation P₁ P₂ (w₁ ^ 2) (w₂ ^ 2) (w_res ^ 2) x

/-- Three-channel Bhatia-Davis spectral dispersion functional
`(w_max + w_min) * threeChannelWeightedExpectation - threeChannelWeightedSecondMoment - w_min * w_max * hilbertEnergy x`. -/
def threeChannelBhatiaDavisFunctional
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res w_min w_max : ℝ) (x : E) : ℝ :=
  (w_max + w_min) * threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x -
    threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x -
    w_min * w_max * hilbertEnergy x

/-- Finite `Q`-channel spectral-weighted second moment
`∑ q : Fin Q, (w q)^2 * hilbertEnergy (P q x)`. -/
def multiChannelWeightedSecondMoment
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (x : E) : ℝ :=
  multiChannelWeightedExpectation P (fun q => (w q) ^ 2) x

/-- Finite `Q`-channel Bhatia-Davis spectral dispersion functional
`(w_max + w_min) * multiChannelWeightedExpectation - multiChannelWeightedSecondMoment - w_min * w_max * (∑ q, hilbertEnergy (P q x))`. -/
def multiChannelBhatiaDavisFunctional
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ) (x : E) : ℝ :=
  (w_max + w_min) * multiChannelWeightedExpectation P w x -
    multiChannelWeightedSecondMoment P w x -
    w_min * w_max * (∑ q : Fin Q, hilbertEnergy (P q x))

/-- Exact factored representation of `threeChannelBhatiaDavisFunctional` when
`AreMutuallyOrthogonalProjections P₁ P₂`, and unconditional nonnegativity of
`threeChannelWeightedSecondMoment`. -/
theorem threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ) (x : E) :
    0 ≤ threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x =
      (w_max - w₁) * (w₁ - w_min) * hilbertEnergy (P₁ x) +
      (w_max - w₂) * (w₂ - w_min) * hilbertEnergy (P₂ x) +
      (w_max - w_res) * (w_res - w_min) * hilbertEnergy (residualTwoProjector P₁ P₂ x) := by
  have he1 : 0 ≤ hilbertEnergy (P₁ x) := hilbertEnergy_nonneg (P₁ x)
  have he2 : 0 ≤ hilbertEnergy (P₂ x) := hilbertEnergy_nonneg (P₂ x)
  have her : 0 ≤ hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_nonneg (residualTwoProjector P₁ P₂ x)
  have hnn : 0 ≤ threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x := by
    unfold threeChannelWeightedSecondMoment threeChannelWeightedExpectation
    positivity
  have hparseval := (twoProjector_three_channel_parseval_decomposition hP x).2
  have hfac :
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x =
        (w_max - w₁) * (w₁ - w_min) * hilbertEnergy (P₁ x) +
        (w_max - w₂) * (w₂ - w_min) * hilbertEnergy (P₂ x) +
        (w_max - w_res) * (w_res - w_min) * hilbertEnergy (residualTwoProjector P₁ P₂ x) := by
    unfold threeChannelBhatiaDavisFunctional threeChannelWeightedSecondMoment
      threeChannelWeightedExpectation
    rw [hparseval]
    ring
  exact ⟨hnn, hfac⟩

/-- Exact three-channel Bhatia-Davis / Popoviciu spectral dispersion inequality:
when `AreMutuallyOrthogonalProjections P₁ P₂` and `w_min ≤ w₁, w₂, w_res ≤ w_max`,
`0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤ ((w_max - w_min) / 2)^2 * hilbertEnergy x`. -/
theorem threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ∧
    threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
      ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x := by
  have he1 : 0 ≤ hilbertEnergy (P₁ x) := hilbertEnergy_nonneg (P₁ x)
  have he2 : 0 ≤ hilbertEnergy (P₂ x) := hilbertEnergy_nonneg (P₂ x)
  have her : 0 ≤ hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_nonneg (residualTwoProjector P₁ P₂ x)
  have hf1 := scalar_bhatia_davis_factor_bounds hmin₁ hmax₁
  have hf2 := scalar_bhatia_davis_factor_bounds hmin₂ hmax₂
  have hfr := scalar_bhatia_davis_factor_bounds hmin_r hmax_r
  have hfac := (threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP w₁ w₂ w_res w_min w_max x).2
  have hparseval := (twoProjector_three_channel_parseval_decomposition hP x).2
  rw [hfac, hparseval]
  have hlo1 := mul_nonneg hf1.1 he1
  have hlo2 := mul_nonneg hf2.1 he2
  have hlor := mul_nonneg hfr.1 her
  have hhi1 := mul_le_mul_of_nonneg_right hf1.2 he1
  have hhi2 := mul_le_mul_of_nonneg_right hf2.2 he2
  have hhir := mul_le_mul_of_nonneg_right hfr.2 her
  refine ⟨by linarith, by linarith⟩

/-- Exact factored representation of `multiChannelBhatiaDavisFunctional P w w_min w_max x`
and unconditional nonnegativity of `multiChannelWeightedSecondMoment P w x`. -/
theorem multiChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ) (x : E) :
    0 ≤ multiChannelWeightedSecondMoment P w x ∧
    multiChannelBhatiaDavisFunctional P w w_min w_max x =
      ∑ q : Fin Q, (w_max - w q) * (w q - w_min) * hilbertEnergy (P q x) := by
  refine ⟨?_, ?_⟩
  · unfold multiChannelWeightedSecondMoment multiChannelWeightedExpectation
    refine Finset.sum_nonneg (fun q _ => ?_)
    exact mul_nonneg (sq_nonneg (w q)) (hilbertEnergy_nonneg (P q x))
  · unfold multiChannelBhatiaDavisFunctional multiChannelWeightedSecondMoment
      multiChannelWeightedExpectation
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring

/-- Exact finite `Q`-channel Bhatia-Davis / Popoviciu spectral dispersion inequality:
when `w_min ≤ w q ≤ w_max` for all `q : Fin Q`,
`0 ≤ multiChannelBhatiaDavisFunctional P w w_min w_max x ≤ ((w_max - w_min) / 2)^2 * (∑ q, hilbertEnergy (P q x))`. -/
theorem multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E) :
    0 ≤ multiChannelBhatiaDavisFunctional P w w_min w_max x ∧
    multiChannelBhatiaDavisFunctional P w w_min w_max x ≤
      ((w_max - w_min) / 2) ^ 2 * (∑ q : Fin Q, hilbertEnergy (P q x)) := by
  have hfac := (multiChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    P w w_min w_max x).2
  rw [hfac, Finset.mul_sum]
  refine ⟨Finset.sum_nonneg (fun q _ => ?_), Finset.sum_le_sum (fun q _ => ?_)⟩
  · exact mul_nonneg (scalar_bhatia_davis_factor_bounds (hmin q) (hmax q)).1
      (hilbertEnergy_nonneg (P q x))
  · exact mul_le_mul_of_nonneg_right
      (scalar_bhatia_davis_factor_bounds (hmin q) (hmax q)).2
      (hilbertEnergy_nonneg (P q x))

/-- Three-channel Bhatia-Davis / Popoviciu dispersion bounds and response decomposition
for `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_threeChannel_bhatia_davis_package
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w b c PK
    threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max Ψ =
      (w_max - w₁) * (w₁ - w_min) *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₁ M w b c PK) +
      (w_max - w₂) * (w₂ - w_min) *
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₂ M w b c PK) +
      (w_max - w_res) * (w_res - w_min) *
        hilbertEnergy
          (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK) ∧
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max Ψ ∧
    threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max Ψ ≤
      ((w_max - w_min) / 2) ^ 2 * hilbertEnergy Ψ := by
  intro Ψ
  have hfac := (threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP w₁ w₂ w_res w_min w_max Ψ).2
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  exact ⟨hfac, hbd.1, hbd.2⟩

/-- Master Synthesis of Three-Channel and `Q`-Channel Spectral-Weighted Second Moments
and Bhatia-Davis / Popoviciu Dispersion Inequalities on Arbitrary-Source Degree-`M`
Polynomial States. -/
theorem arbitrary_source_weighted_projector_bhatia_davis_master_synthesis
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    {Q : ℕ} (Pq : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ)
    (w₁ w₂ w_res l_min l_max w_min w_max : ℝ)
    (hmin₁ : l_min ≤ w₁) (hmin₂ : l_min ≤ w₂) (hmin_r : l_min ≤ w_res)
    (hmax₁ : w₁ ≤ l_max) (hmax₂ : w₂ ≤ l_max) (hmax_r : w_res ≤ l_max)
    (hw_min : ∀ q, w_min ≤ w q) (hw_max : ∀ q, w q ≤ w_max)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
      (identicalPackets ψ)
    (0 ≤ threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res Ψ ∧
     0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res l_min l_max Ψ ∧
     threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res l_min l_max Ψ ≤
       ((l_max - l_min) / 2) ^ 2 * hilbertEnergy Ψ) ∧
    (0 ≤ multiChannelWeightedSecondMoment Pq w Ψ ∧
     0 ≤ multiChannelBhatiaDavisFunctional Pq w w_min w_max Ψ ∧
     multiChannelBhatiaDavisFunctional Pq w w_min w_max Ψ ≤
       ((w_max - w_min) / 2) ^ 2 * (∑ q : Fin Q, hilbertEnergy (Pq q Ψ))) := by
  intro Ψ
  have h2_3 := (threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP w₁ w₂ w_res l_min l_max Ψ).1
  have hbd3 := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res l_min l_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  have h2_Q := (multiChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    Pq w w_min w_max Ψ).1
  have hbdQ := multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    Pq w w_min w_max hw_min hw_max Ψ
  exact ⟨⟨h2_3, hbd3.1, hbd3.2⟩, ⟨h2_Q, hbdQ.1, hbdQ.2⟩⟩

end WeightedProjectorBhatiaDavisCalculus

#print axioms threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
#print axioms threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
#print axioms multiChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
#print axioms multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
#print axioms arbitrarySourceDegreeMPolyState_threeChannel_bhatia_davis_package
#print axioms arbitrary_source_weighted_projector_bhatia_davis_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
