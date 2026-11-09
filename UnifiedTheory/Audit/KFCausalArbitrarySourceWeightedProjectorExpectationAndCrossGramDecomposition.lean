/- Three-Channel (`w₁ P₁ + w₂ P₂ + w_res (I - P₁ - P₂)`) and Finite `Q`-Channel
(`∑_{q < Q} w_q P_q`) Spectral-Weighted Projector Expectations, Rayleigh-Ritz
Sandwich Bounds, and Arbitrary-Source Degree-`M` Polynomial State Weighted Energy
Decompositions. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition

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
   twoProjector_three_channel_parseval_decomposition
   arbitrarySourceDegreeMPolyState_three_channel_parseval_decomposition
   arbitrarySourceDegreeMPolyState_antipodal_deg_one_three_channel_package)

section WeightedProjectorExpectationCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private lemma hilbertEnergy_nonneg (x : E) : 0 ≤ hilbertEnergy x := by
  unfold hilbertEnergy
  exact @inner_self_nonneg ℂ E _ _ _ x

/-- Three-channel spectral-weighted projector expectation
`w₁ * hilbertEnergy (P₁ x) + w₂ * hilbertEnergy (P₂ x) + w_res * hilbertEnergy (residualTwoProjector P₁ P₂ x)`. -/
def threeChannelWeightedExpectation
    (P₁ P₂ : E →L[ℂ] E) (w₁ w₂ w_res : ℝ) (x : E) : ℝ :=
  w₁ * hilbertEnergy (P₁ x) +
  w₂ * hilbertEnergy (P₂ x) +
  w_res * hilbertEnergy (residualTwoProjector P₁ P₂ x)

/-- Finite `Q`-channel spectral-weighted projector expectation
`∑ q : Fin Q, w q * hilbertEnergy (P q x)`. -/
def multiChannelWeightedExpectation
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (x : E) : ℝ :=
  ∑ q : Fin Q, w q * hilbertEnergy (P q x)

/-- Nonnegativity of `threeChannelWeightedExpectation` for nonnegative spectral weights
`0 ≤ w₁, 0 ≤ w₂, 0 ≤ w_res`, and exact scalar Parseval identity at equal weights
`w₁ = w₂ = w_res = c` when `AreMutuallyOrthogonalProjections P₁ P₂`. -/
theorem threeChannelWeightedExpectation_nonneg_and_const_eq
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res c : ℝ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (hr : 0 ≤ w_res) (x : E) :
    0 ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelWeightedExpectation P₁ P₂ c c c x = c * hilbertEnergy x := by
  have he1 : 0 ≤ hilbertEnergy (P₁ x) := hilbertEnergy_nonneg (P₁ x)
  have he2 : 0 ≤ hilbertEnergy (P₂ x) := hilbertEnergy_nonneg (P₂ x)
  have her : 0 ≤ hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_nonneg (residualTwoProjector P₁ P₂ x)
  have hnn : 0 ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x := by
    unfold threeChannelWeightedExpectation
    positivity
  have hparseval := (twoProjector_three_channel_parseval_decomposition hP x).2
  have hconst : threeChannelWeightedExpectation P₁ P₂ c c c x = c * hilbertEnergy x := by
    unfold threeChannelWeightedExpectation
    rw [hparseval]
    ring
  exact ⟨hnn, hconst⟩

/-- Exact Rayleigh-Ritz sandwich bounds for `threeChannelWeightedExpectation`:
when `AreMutuallyOrthogonalProjections P₁ P₂` and `w_min ≤ w₁, w₂, w_res ≤ w_max`,
`w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x`. -/
theorem threeChannelWeightedExpectation_rayleigh_ritz_bounds
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
    threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x := by
  have he1 : 0 ≤ hilbertEnergy (P₁ x) := hilbertEnergy_nonneg (P₁ x)
  have he2 : 0 ≤ hilbertEnergy (P₂ x) := hilbertEnergy_nonneg (P₂ x)
  have her : 0 ≤ hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_nonneg (residualTwoProjector P₁ P₂ x)
  have hparseval := (twoProjector_three_channel_parseval_decomposition hP x).2
  unfold threeChannelWeightedExpectation
  rw [hparseval]
  have hlo1 := mul_le_mul_of_nonneg_right hmin₁ he1
  have hlo2 := mul_le_mul_of_nonneg_right hmin₂ he2
  have hlor := mul_le_mul_of_nonneg_right hmin_r her
  have hhi1 := mul_le_mul_of_nonneg_right hmax₁ he1
  have hhi2 := mul_le_mul_of_nonneg_right hmax₂ he2
  have hhir := mul_le_mul_of_nonneg_right hmax_r her
  refine ⟨by linarith, by linarith⟩

/-- Weight linearity (additivity and scalar homogeneity) and nonnegativity of
`multiChannelWeightedExpectation P w x`. -/
theorem multiChannelWeightedExpectation_linear_and_nonneg
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ : Fin Q → ℝ) (a : ℝ)
    (hw₁ : ∀ q, 0 ≤ w₁ q) (x : E) :
    multiChannelWeightedExpectation P (fun q => w₁ q + w₂ q) x =
      multiChannelWeightedExpectation P w₁ x + multiChannelWeightedExpectation P w₂ x ∧
    multiChannelWeightedExpectation P (fun q => a * w₁ q) x =
      a * multiChannelWeightedExpectation P w₁ x ∧
    0 ≤ multiChannelWeightedExpectation P w₁ x := by
  refine ⟨?_, ?_, ?_⟩
  · unfold multiChannelWeightedExpectation
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  · unfold multiChannelWeightedExpectation
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  · unfold multiChannelWeightedExpectation
    refine Finset.sum_nonneg (fun q _ => ?_)
    exact mul_nonneg (hw₁ q) (hilbertEnergy_nonneg (P q x))

/-- Rayleigh-Ritz sandwich bounds for `multiChannelWeightedExpectation P w x`:
when `w_min ≤ w q ≤ w_max` for all `q : Fin Q`,
`w_min * (∑ q, hilbertEnergy (P q x)) ≤ multiChannelWeightedExpectation P w x ≤ w_max * (∑ q, hilbertEnergy (P q x))`. -/
theorem multiChannelWeightedExpectation_rayleigh_ritz_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E) :
    w_min * (∑ q : Fin Q, hilbertEnergy (P q x)) ≤
      multiChannelWeightedExpectation P w x ∧
    multiChannelWeightedExpectation P w x ≤
      w_max * (∑ q : Fin Q, hilbertEnergy (P q x)) := by
  unfold multiChannelWeightedExpectation
  rw [Finset.mul_sum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum (fun q _ => ?_), Finset.sum_le_sum (fun q _ => ?_)⟩
  · exact mul_le_mul_of_nonneg_right (hmin q) (hilbertEnergy_nonneg (P q x))
  · exact mul_le_mul_of_nonneg_right (hmax q) (hilbertEnergy_nonneg (P q x))

/-- Three-channel spectral-weighted expectation and Rayleigh-Ritz bounds for
`arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_threeChannel_weighted_rayleigh_ritz
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w b c PK
    threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ =
      w₁ * hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₁ M w b c PK) +
      w₂ * hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₂ M w b c PK) +
      w_res * hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK) ∧
    w_min * hilbertEnergy Ψ ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ ∧
    threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ ≤ w_max * hilbertEnergy Ψ := by
  intro Ψ
  have hrr := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  exact ⟨rfl, hrr.1, hrr.2⟩

/-- Master Synthesis of Three-Channel and `Q`-Channel Spectral-Weighted Projector
Expectations and Rayleigh-Ritz Bounds on Arbitrary-Source Degree-`M` Polynomial States. -/
theorem arbitrary_source_weighted_projector_expectation_master_synthesis
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    {Q : ℕ} (Pq : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ)
    (w₁ w₂ w_res l_min l_max w_min w_max : ℝ)
    (hmin₁ : l_min ≤ w₁) (hmin₂ : l_min ≤ w₂) (hmin_r : l_min ≤ w_res)
    (hmax₁ : w₁ ≤ l_max) (hmax₂ : w₂ ≤ l_max) (hmax_r : w_res ≤ l_max)
    (hw_min : ∀ q, w_min ≤ w q) (hw_max : ∀ q, w q ≤ w_max)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
      (identicalPackets ψ)
    (threeChannelWeightedExpectation P₁ P₂ 1 1 1 Ψ = hilbertEnergy Ψ ∧
     l_min * hilbertEnergy Ψ ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ ∧
     threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res Ψ ≤ l_max * hilbertEnergy Ψ) ∧
    (w_min * (∑ q : Fin Q, hilbertEnergy (Pq q Ψ)) ≤
       multiChannelWeightedExpectation Pq w Ψ ∧
     multiChannelWeightedExpectation Pq w Ψ ≤
       w_max * (∑ q : Fin Q, hilbertEnergy (Pq q Ψ))) := by
  intro Ψ
  have hconst := (threeChannelWeightedExpectation_nonneg_and_const_eq
    hP 1 1 1 1 zero_le_one zero_le_one zero_le_one Ψ).2
  rw [one_mul] at hconst
  have hrr3 := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res l_min l_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r Ψ
  have hrrQ := multiChannelWeightedExpectation_rayleigh_ritz_bounds
    Pq w w_min w_max hw_min hw_max Ψ
  exact ⟨⟨hconst, hrr3.1, hrr3.2⟩, hrrQ⟩

end WeightedProjectorExpectationCalculus

#print axioms threeChannelWeightedExpectation_nonneg_and_const_eq
#print axioms threeChannelWeightedExpectation_rayleigh_ritz_bounds
#print axioms multiChannelWeightedExpectation_linear_and_nonneg
#print axioms multiChannelWeightedExpectation_rayleigh_ritz_bounds
#print axioms arbitrarySourceDegreeMPolyState_threeChannel_weighted_rayleigh_ritz
#print axioms arbitrary_source_weighted_projector_expectation_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
