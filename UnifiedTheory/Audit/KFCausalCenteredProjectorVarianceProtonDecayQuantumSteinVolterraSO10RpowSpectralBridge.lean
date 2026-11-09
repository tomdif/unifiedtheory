/- Bridge of the Normalized Three-Channel Spectral Variance Functional, Exact Lagrange Pairwise
Channel-Spread Identity, and Bhatia-Davis / Popoviciu Variance Envelope Bounds with the 22 LayerB
Proton Decay, Quantum Defects, Quantum Entanglement, Quantum Mechanics Theorem, Quantum Stein,
R1 Chamber-Bath / Character Orthogonality / Volterra $SO(10)$ Embeddings, R2 $SO(10)$ Haar Integral,
Richer Matter, Fractional Power Integrand / Operator Concavity, $SO(10)$ Embedding Test, Separable
CHSH, Signed Source, Source Focusing, and Spectral Density / Functional Calculus Modules
(`ProtonDecayPrediction`..`SpectralFunctionalCalculusTrace`). -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
import UnifiedTheory.LayerB.ProtonDecayPrediction
import UnifiedTheory.LayerB.QuantumDefects
import UnifiedTheory.LayerB.QuantumEntanglement
import UnifiedTheory.LayerB.QuantumMechanicsIsATheorem
import UnifiedTheory.LayerB.QuantumStein
import UnifiedTheory.LayerB.R1_ChamberBathCommutes_FullYM
import UnifiedTheory.LayerB.R1_CharacterOrthogonality
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim4Chamber
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim6Full
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_DimExtension
import UnifiedTheory.LayerB.R2_SO10HaarIntegral
import UnifiedTheory.LayerB.RicherMatter
import UnifiedTheory.LayerB.RpowIntegrandPerT
import UnifiedTheory.LayerB.RpowOperatorConcavity
import UnifiedTheory.LayerB.SO10EmbeddingTest
import UnifiedTheory.LayerB.SeparableCHSH
import UnifiedTheory.LayerB.SignedSource
import UnifiedTheory.LayerB.SourceFocusing
import UnifiedTheory.LayerB.SpectralDensityMatrix
import UnifiedTheory.LayerB.SpectralFunctionalCalculus
import UnifiedTheory.LayerB.SpectralFunctionalCalculusTrace

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalCenteredProjectorVarianceProtonDecayQuantumSteinVolterraSO10RpowSpectralBridge

open scoped InnerProduct BigOperators Matrix ComplexOrder
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
`threeChannelSpectralVarianceFunctional` paired with proton-decay discriminant `disc = 7`
(`ProtonDecayPrediction`), Born nonnegativity (`QuantumDefects`), quantum separability equivalence
(`QuantumEntanglement`), and binary hypothesis test complement Hermiticity (`QuantumStein`). -/
theorem centeredProjectorVariance_lagrangeSpread_with_protonDecay_quantumDefects_entanglement_and_quantumStein
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E) (z : ℂ)
    {n_ent n_st : ℕ}
    (ψ_ent : LayerB.QuantumEntanglement.TwoParticleState n_ent)
    (T_st : LayerB.QuantumStein.BinaryHypothesisTest n_st) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      LayerB.ProtonDecayPrediction.disc = 7 ∧
      0 ≤ LayerB.obs z ∧
      (LayerB.QuantumEntanglement.IsQuantumSeparable ψ_ent ↔
        LayerB.Entanglement.IsSeparable ψ_ent) ∧
      (1 - T_st.accept).IsHermitian := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  exact ⟨hlag.1, hlag.2.1,
    LayerB.ProtonDecayPrediction.disc_eq_seven,
    LayerB.born_nonneg z,
    LayerB.QuantumEntanglement.isQuantumSeparable_iff_isSeparable ψ_ent,
    LayerB.QuantumStein.BinaryHypothesisTest.complement_isHerm T_st⟩

/-- Domination of `threeChannelSpectralVarianceFunctional` by Bhatia-Davis and Popoviciu
variance-squared bounds paired with R1 chamber-bath label vanishing (`R1_ChamberBathCommutes_FullYM`),
$\mathbb{Z}_2$ central-character sign product (`R1_CharacterOrthogonality`), Volterra $SO(10)$ $L^2$
orthogonality (`R1_VolterraSO10Embedding`), and dim-4/dim-6 central-character parity
(`R1_VolterraSO10Embedding_Dim4Chamber`, `R1_VolterraSO10Embedding_Dim6Full`,
`R1_VolterraSO10Embedding_DimExtension`). -/
theorem centeredProjectorVariance_popoviciu_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) (i_ch : Fin 3) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
      (w_max * hilbertEnergy x - threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x) *
        (threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x - w_min * hilbertEnergy x) ∧
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
        ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 ∧
      LayerB.R1_ChamberBathCommutes_FullYM.chamberLabel
        (LayerB.Build3_ExplicitFeshbach.chamberIdx i_ch) = 0 ∧
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .even *
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .odd = -1 ∧
      (inner ℝ LayerB.R1_VolterraSO10Embedding.oneLp
        LayerB.R1_VolterraSO10Embedding.traceLp : ℝ) = 0 ∧
      LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.even
        LayerB.R1_VolterraSO10Embedding_Dim4Chamber.f4 ∧
      LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.odd
        LayerB.R1_VolterraSO10Embedding_Dim6Full.h1 ∧
      LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.even
        LayerB.R1_VolterraSO10Embedding_DimExtension.f3 := by
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.2.1, hbd.2.2,
    LayerB.R1_ChamberBathCommutes_FullYM.chamberLabel_chamber_eq i_ch,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner,
    LayerB.R1_VolterraSO10Embedding_Dim4Chamber.f4_carries_even,
    LayerB.R1_VolterraSO10Embedding_Dim6Full.h1_carries_odd,
    LayerB.R1_VolterraSO10Embedding_DimExtension.f3_carries_even⟩

/-- Shift invariance of `threeChannelSpectralVarianceFunctional` paired with Wilson-Haar interface
normalization (`R2_SO10HaarIntegral`), shifted PSD positive-definiteness (`RpowOperatorConcavity`),
$SO(10)$ embedding $N_W = 2, N_c = 3$ (`SO10EmbeddingTest`), and singlet CHSH violation
`chshValue^2 > 4` (`SeparableCHSH`). -/
theorem centeredProjectorVariance_shift_with_r2Haar_rpowConcavity_so10Test_and_separableCHSH
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res c_sh : ℝ) (x : E)
    (I_haar : LayerB.R2_SO10HaarIntegral.WilsonHaarInterface)
    {n_mat : ℕ} (A_psd : Matrix (Fin n_mat) (Fin n_mat) ℂ) (hA : A_psd.PosSemidef)
    {t_pos : ℝ} (ht : 0 < t_pos) :
    threeChannelSpectralVarianceFunctional P₁ P₂ (w₁ + c_sh) (w₂ + c_sh) (w_res + c_sh) x =
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      (∫ _x, (1 : ℝ) ∂I_haar.μ = 1) ∧
      (((t_pos : ℂ) • (1 : Matrix (Fin n_mat) (Fin n_mat) ℂ)) + A_psd).PosDef ∧
      LayerB.SO10EmbeddingTest.N_W = 2 ∧
      LayerB.SO10EmbeddingTest.N_c = 3 ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 := by
  have hsh := threeChannelSpectralVarianceFunctional_shift_invariance
    hP w₁ w₂ w_res c_sh x
  exact ⟨hsh.2,
    LayerB.R2_SO10HaarIntegral.interface_normalization I_haar,
    LayerB.RpowOperatorConcavity.posDef_add_smul_one_of_PSD A_psd hA ht,
    LayerB.SO10EmbeddingTest.N_W_eq,
    LayerB.SO10EmbeddingTest.N_c_eq,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four⟩

/-- Spectral variance Lagrange identity paired with signed-source additivity (`SignedSource`),
positive-source focusing (`SourceFocusing`), spectral von Neumann entropy nonnegativity
(`SpectralDensityMatrix`), spectral CFC Hermiticity (`SpectralFunctionalCalculus`), and unitary
conjugation trace invariance (`SpectralFunctionalCalculusTrace`). -/
theorem centeredProjectorVariance_with_signedSource_sourceFocusing_spectralDensity_and_spectralFCTrace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E)
    {m_src n_sp : ℕ}
    (h₁ h₂ : LayerB.MetricDefects.Perturbation (m_src + 2))
    (F_foc : LayerB.SourceFocusing.FocusingHypothesis m_src)
    (hp : 0 < LayerB.SignedSource.Q h₁)
    (S_sp : LayerB.Spectral.SpectralDensityMatrix n_sp)
    (f_fc : ℝ → ℝ) (ρ_sp : LayerB.RobertsonSchrodinger.ComplexDensityMatrix n_sp)
    (U_sp : Matrix.unitaryGroup (Fin n_sp) ℂ) (M_sp : Matrix (Fin n_sp) (Fin n_sp) ℂ) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      LayerB.SignedSource.Q (h₁ + h₂) =
        LayerB.SignedSource.Q h₁ + LayerB.SignedSource.Q h₂ ∧
      0 < LayerB.SourceFocusing.focusing F_foc h₁ ∧
      0 ≤ LayerB.Spectral.vonNeumannEntropySpectral S_sp ∧
      (LayerB.SpectralFC.cfcρ f_fc ρ_sp).IsHermitian ∧
      Matrix.trace
        ((U_sp : Matrix (Fin n_sp) (Fin n_sp) ℂ) * M_sp *
          star (U_sp : Matrix (Fin n_sp) (Fin n_sp) ℂ)) =
        Matrix.trace M_sp := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  exact ⟨hlag.1,
    LayerB.SignedSource.Q_add h₁ h₂,
    LayerB.SourceFocusing.positive_source_focuses F_foc h₁ hp,
    LayerB.Spectral.spectral_entropy_nonneg S_sp,
    LayerB.SpectralFC.cfcρ_isHermitian f_fc ρ_sp,
    LayerB.SpectralFCTrace.trace_conj_unitary U_sp M_sp⟩

/-- Master synthesis of the normalized three-channel spectral variance functional, Lagrange
channel-spread identity, and Bhatia-Davis / Popoviciu bounds with all 22
ProtonDecay/QuantumStein/VolterraSO10/Rpow/SpectralFC modules. -/
theorem centeredProjectorVariance_protonDecay_quantumStein_volterraSO10_rpow_spectral_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) {n_sp : ℕ} (S_sp : LayerB.Spectral.SpectralDensityMatrix n_sp) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
        ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 ∧
      LayerB.ProtonDecayPrediction.disc = 7 ∧
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .even *
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .odd = -1 ∧
      (inner ℝ LayerB.R1_VolterraSO10Embedding.oneLp
        LayerB.R1_VolterraSO10Embedding.traceLp : ℝ) = 0 ∧
      LayerB.SO10EmbeddingTest.N_W = 2 ∧
      LayerB.SO10EmbeddingTest.N_c = 3 ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      0 ≤ LayerB.Spectral.vonNeumannEntropySpectral S_sp := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hlag.1, hbd.1, hbd.2.2,
    LayerB.ProtonDecayPrediction.disc_eq_seven,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner,
    LayerB.SO10EmbeddingTest.N_W_eq,
    LayerB.SO10EmbeddingTest.N_c_eq,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerB.Spectral.spectral_entropy_nonneg S_sp⟩

#print axioms centeredProjectorVariance_lagrangeSpread_with_protonDecay_quantumDefects_entanglement_and_quantumStein
#print axioms centeredProjectorVariance_popoviciu_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
#print axioms centeredProjectorVariance_shift_with_r2Haar_rpowConcavity_so10Test_and_separableCHSH
#print axioms centeredProjectorVariance_with_signedSource_sourceFocusing_spectralDensity_and_spectralFCTrace
#print axioms centeredProjectorVariance_protonDecay_quantumStein_volterraSO10_rpow_spectral_bridge_master

end KFCausalCenteredProjectorVarianceProtonDecayQuantumSteinVolterraSO10RpowSpectralBridge
end Audit
end UnifiedTheory
