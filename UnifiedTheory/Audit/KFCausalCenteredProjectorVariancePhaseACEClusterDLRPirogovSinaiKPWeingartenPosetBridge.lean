/- Bridge of the Normalized Three-Channel Spectral Variance Functional, Exact Lagrange Pairwise
Channel-Spread Identity, and Bhatia-Davis / Popoviciu Variance Envelope Bounds with the 20 LayerB
Multi-Link Hilbert, Matrix-Element Matching, Volterra Link Search, Cluster Expansion, Interacting
Wilson Measure, DLR Character Expansion, Pirogov-Sinai Contours, Glimm-Jaffe Kotecký-Preiss
Strategy, Higher Weingartens, KP3–KP7, Row-Permutation Symmetry, Off-Diagonal Weingarten, Poset
Growth, Projective Measurement DPI, and Propagation Rule Modules
(`Phase_A1_MultiLinkHilbert`..`PropagationRule`). -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching
import UnifiedTheory.LayerB.Phase_A6_VolterraLinkSearch
import UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_E3_DLR_CharacterExpansion
import UnifiedTheory.LayerB.Phase_E3_DLR_PirogovSinai
import UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
import UnifiedTheory.LayerB.Phase_E3_HigherWeingartens
import UnifiedTheory.LayerB.Phase_E3_KP3_KP4
import UnifiedTheory.LayerB.Phase_E3_KP5
import UnifiedTheory.LayerB.Phase_E3_KP6
import UnifiedTheory.LayerB.Phase_E3_KP6_StrongCouplingAttempt
import UnifiedTheory.LayerB.Phase_E3_KP6_Unconditional_FreeCase
import UnifiedTheory.LayerB.Phase_E3_KP7
import UnifiedTheory.LayerB.Phase_E3_RowPermutationSymmetry_Proof
import UnifiedTheory.LayerB.Phase_E3_Weingarten_OffDiagonal_Proof
import UnifiedTheory.LayerB.PosetGrowthIsQuantum
import UnifiedTheory.LayerB.ProjectiveMeasurementDPI
import UnifiedTheory.LayerB.PropagationRule

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalCenteredProjectorVariancePhaseACEClusterDLRPirogovSinaiKPWeingartenPosetBridge

open scoped InnerProduct BigOperators ComplexOrder
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition (hilbertEnergy)
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
  (AreMutuallyOrthogonalProjections)
open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
  (threeChannelWeightedExpectation)
open KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
  (threeChannelSpectralVarianceFunctional
   threeChannelLagrangePairwiseSpread
   threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
   threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
   threeChannelSpectralVarianceFunctional_shift_invariance)

/-- Exact Lagrange pairwise channel-spread identity and nonnegativity for
`threeChannelSpectralVarianceFunctional` paired with multi-link $L^2$ embedding isometry
(`Phase_A1_MultiLinkHilbert`), chamber-to-$\iota_6$ injectivity and $\mathbb{Z}_2$-even parity
(`Phase_A4_MatrixElementMatching`), and $J_4$ target trace `14 / 15`
(`Phase_A6_VolterraLinkSearch`). -/
theorem centeredProjectorVariance_lagrangeSpread_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E)
    (L_link : ℕ) (i_link : Fin L_link)
    (f_lp : MeasureTheory.Lp ℝ 2 LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      ‖LayerB.Phase_A1_MultiLinkHilbert.embedAtLink L_link i_link f_lp‖ = ‖f_lp‖ ∧
      Function.Injective LayerB.Phase_A4_MatrixElementMatching.chamberToIota6 ∧
      LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨0, by decide⟩ ⟨0, by decide⟩ +
        LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨1, by decide⟩ ⟨1, by decide⟩ +
        LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨2, by decide⟩ ⟨2, by decide⟩ = 14 / 15 := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  exact ⟨hlag.1, hlag.2.1,
    LayerB.Phase_A1_MultiLinkHilbert.embedAtLink_norm L_link i_link f_lp,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_A6_VolterraLinkSearch.J4target_trace_eq⟩

/-- Domination of `threeChannelSpectralVarianceFunctional` by Bhatia-Davis and Popoviciu
variance-squared bounds paired with polymer size positivity (`Phase_C1_ClusterExpansion`),
trivial character coefficient at $\beta = 0$ (`Phase_E3_DLR_CharacterExpansion`), Pirogov-Sinai
contour size positivity (`Phase_E3_DLR_PirogovSinai`), and zero-activity Kotecký-Preiss condition
(`Phase_E3_GJConvergenceStrategy`). -/
theorem centeredProjectorVariance_popoviciu_with_clusterExpansion_dlrCharacter_pirogovSinai_and_gjKP
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E)
    {L_lat : LayerB.Phase_C1_ClusterExpansion.LatticeSide}
    (P_poly : LayerB.Phase_C1_ClusterExpansion.Polymer L_lat)
    (γ_cnt : LayerB.Phase_E3_DLR_PirogovSinai.WilsonContour L_lat)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (h_zero : ∀ γ : sys.Poly, sys.activity γ = 0) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
      (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) ∧
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
        ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 ∧
      1 ≤ LayerB.Phase_C1_ClusterExpansion.polymerSize P_poly ∧
      LayerB.Phase_E3_DLR_CharacterExpansion.cCoef 0
        LayerB.Phase_A3_CasimirSpectrum.SO10Irrep.trivial = 1 ∧
      1 ≤ LayerB.Phase_E3_DLR_PirogovSinai.contourSize γ_cnt ∧
      LayerB.Phase_E3_GJConvergenceStrategy.KoteckyPreissCondition sys
        (fun _ => 0) (fun _ => 0) := by
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.2.1, hbd.2.2,
    LayerB.Phase_C1_ClusterExpansion.polymerSize_pos P_poly,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_DLR_PirogovSinai.contourSize_pos γ_cnt,
    LayerB.Phase_E3_GJConvergenceStrategy.KP_holds_at_zero_activity sys h_zero⟩

/-- Shift invariance of `threeChannelSpectralVarianceFunctional` paired with cubic $SO(10)$ Haar
integral vanishing (`Phase_E3_HigherWeingartens`), KP3–KP5 weighted activity sum nonnegativity
(`Phase_E3_KP3_KP4`, `Phase_E3_KP5`), KP6 action-to-projective consistency (`Phase_E3_KP6`), and
4D coordination number positivity (`Phase_E3_KP7`). -/
theorem centeredProjectorVariance_shift_with_higherWeingartens_kp3456_and_kp7Coord4D
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res c_sh : ℝ) (x : E)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (a_kp b_kp : sys.Poly → ℝ) (Λ_kp : Finset sys.Poly)
    (β_w : ℝ) (S_act : LayerB.Phase_E2_InteractingWilsonMeasure.WilsonActionAssignment) :
    threeChannelSpectralVarianceFunctional P₁ P₂ (w₁ + c_sh) (w₂ + c_sh) (w_res + c_sh) x =
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      (∫ U : LayerB.R2b_SO10HaarConcreteConstruction.G_SO10,
        LayerB.Phase_E3_HigherWeingartens.traceCube U
          ∂LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10 = 0) ∧
      0 ≤ LayerB.Phase_E3_KP5.activitySum sys a_kp b_kp Λ_kp ∧
      0 ≤ LayerB.Phase_E3_KP5.activityDensity sys a_kp b_kp Λ_kp ∧
      (LayerB.Phase_E3_KP6.WilsonActionConsistency β_w S_act ↔
        LayerB.Phase_E2_InteractingWilsonMeasure.InteractingWilsonProjectiveConsistency β_w S_act) ∧
      0 < LayerB.Phase_E3_KP7.coord4D := by
  have hsh := threeChannelSpectralVarianceFunctional_shift_invariance
    hP w₁ w₂ w_res c_sh x
  exact ⟨hsh.2,
    LayerB.Phase_E3_HigherWeingartens.trace_cubed_integral_zero,
    LayerB.Phase_E3_KP5.activitySum_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP5.KP5_density_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP6.wilsonActionConsistency_iff_projectiveConsistency β_w S_act,
    LayerB.Phase_E3_KP7.coord4D_pos⟩

/-- Spectral variance Lagrange identity paired with unconditional $SO(10)$ row-permutation symmetry
(`Phase_E3_RowPermutationSymmetry_Proof`), unconditional off-diagonal Weingarten vanishing
(`Phase_E3_Weingarten_OffDiagonal_Proof`), poset growth rotation norm invariance
(`PosetGrowthIsQuantum`), projective-measurement Umegaki DPI (`ProjectiveMeasurementDPI`), and
multiplicative path amplitude (`PropagationRule`). -/
theorem centeredProjectorVariance_with_rowPermSymmetry_offDiagWeingarten_posetGrowth_projectiveDPI_and_propRule
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res Q P_pos θ k_amp s₁ s₂ : ℝ) (x : E)
    {n_dpi : ℕ} (ρ σ : LayerB.RobertsonSchrodinger.ComplexDensityMatrix n_dpi)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      LayerB.Phase_E3_Weingarten_Diagonal.RowPermutationSymmetrySO10 ∧
      LayerB.Phase_E3_Weingarten_Diagonal.OffDiagonalDiagSquaredCorrelation 0 ∧
      (LayerB.PosetGrowthIsQuantum.rotateQ Q P_pos θ) ^ 2 +
        (LayerB.PosetGrowthIsQuantum.rotateP Q P_pos θ) ^ 2 = Q ^ 2 + P_pos ^ 2 ∧
      LayerB.ClassicalRelativeEntropy.klDivergence
        (LayerB.ProjectiveMeasurementDPI.outcomesInSigmaBasis ρ σ hσ_pos hρ_pos)
        (LayerB.ProjectiveMeasurementDPI.outcomesInSigmaBasis σ σ hσ_pos hσ_pos) ≤
        LayerB.UmegakiRelativeEntropy.umegakiRelativeEntropy ρ σ ∧
      LayerB.PropagationRule.expAmplitude k_amp (s₁ + s₂) =
        LayerB.PropagationRule.expAmplitude k_amp s₁ *
          LayerB.PropagationRule.expAmplitude k_amp s₂ := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  exact ⟨hlag.1,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.PosetGrowthIsQuantum.rotation_preserves_norm Q P_pos θ,
    LayerB.ProjectiveMeasurementDPI.umegaki_dpi_projective_sigma_basis ρ σ hρ_pos hσ_pos,
    LayerB.PropagationRule.exp_multiplicative k_amp s₁ s₂⟩

/-- Master synthesis of the normalized three-channel spectral variance functional, Lagrange
channel-spread identity, and Bhatia-Davis / Popoviciu bounds with all 20
Phase-A/C/E/Weingarten/Poset/ProjectiveDPI/PropagationRule modules. -/
theorem centeredProjectorVariance_phaseACE_cluster_dlr_pirogovSinai_kp_weingarten_poset_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max Q P_pos θ k_amp s₁ s₂ : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
        ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 ∧
      Function.Injective LayerB.Phase_A4_MatrixElementMatching.chamberToIota6 ∧
      LayerB.Phase_E3_DLR_CharacterExpansion.cCoef 0
        LayerB.Phase_A3_CasimirSpectrum.SO10Irrep.trivial = 1 ∧
      0 < LayerB.Phase_E3_KP7.coord4D ∧
      LayerB.Phase_E3_Weingarten_Diagonal.RowPermutationSymmetrySO10 ∧
      LayerB.Phase_E3_Weingarten_Diagonal.OffDiagonalDiagSquaredCorrelation 0 ∧
      (LayerB.PosetGrowthIsQuantum.rotateQ Q P_pos θ) ^ 2 +
        (LayerB.PosetGrowthIsQuantum.rotateP Q P_pos θ) ^ 2 = Q ^ 2 + P_pos ^ 2 ∧
      LayerB.PropagationRule.expAmplitude k_amp (s₁ + s₂) =
        LayerB.PropagationRule.expAmplitude k_amp s₁ *
          LayerB.PropagationRule.expAmplitude k_amp s₂ := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hlag.1, hbd.1, hbd.2.2,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_KP7.coord4D_pos,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.PosetGrowthIsQuantum.rotation_preserves_norm Q P_pos θ,
    LayerB.PropagationRule.exp_multiplicative k_amp s₁ s₂⟩

#print axioms centeredProjectorVariance_lagrangeSpread_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
#print axioms centeredProjectorVariance_popoviciu_with_clusterExpansion_dlrCharacter_pirogovSinai_and_gjKP
#print axioms centeredProjectorVariance_shift_with_higherWeingartens_kp3456_and_kp7Coord4D
#print axioms centeredProjectorVariance_with_rowPermSymmetry_offDiagWeingarten_posetGrowth_projectiveDPI_and_propRule
#print axioms centeredProjectorVariance_phaseACE_cluster_dlr_pirogovSinai_kp_weingarten_poset_bridge_master

end KFCausalCenteredProjectorVariancePhaseACEClusterDLRPirogovSinaiKPWeingartenPosetBridge
end Audit
end UnifiedTheory
