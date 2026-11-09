/- Bridge of the Finite `Q`-Channel $2 \times 2$ Spectral Covariance Gram Determinant, Multiplicative
Cauchy-Schwarz Inequality `Cov_Q(w₁, w₂, x)^2 ≤ Var_Q(w₁, x) * Var_Q(w₂, x)`, $\mathrm{GL}_2(\mathbb{R})$
Determinant Scaling, and Multiplicative Popoviciu Bounds with the LayerB/LayerC Bell CHSH, Separable
CHSH, Tsirelson Bound, Bipartite Qubit No-Signalling, Bit-Commitment Impossibility, Information
Causality, LHV vs. Relational Reality, Fine's No-Go Theorem, Phase Faithfulness, Singlet
No-Global-Section, and SM Partial Forcing Modules. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
import UnifiedTheory.LayerB.BellTheorem
import UnifiedTheory.LayerB.SeparableCHSH
import UnifiedTheory.LayerC.BipartiteFullPostulatesQubit
import UnifiedTheory.LayerC.BipartiteQubitCHSH
import UnifiedTheory.LayerC.BipartiteUnitaryQM
import UnifiedTheory.LayerC.BitCommitmentImpossibility
import UnifiedTheory.LayerC.InformationCausality
import UnifiedTheory.LayerC.LHVvsRR
import UnifiedTheory.LayerC.NoGoAnatomy
import UnifiedTheory.LayerC.PhaseFaithfulnessAllN
import UnifiedTheory.LayerC.PhaseQuotientUnitaryQM
import UnifiedTheory.LayerC.SMBornRuleReconciliation
import UnifiedTheory.LayerC.SMPartialForcing
import UnifiedTheory.LayerC.SingletNoGlobalSection
import UnifiedTheory.LayerC.TsirelsonProblem
import UnifiedTheory.LayerC.UnitaryQMLocalRealistic

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalMultiChannelGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

open scoped InnerProduct BigOperators Matrix
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional)
open KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant
   multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
   multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
   multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds)

/-- Nonnegativity of `multiChannelSpectralCovarianceGramDeterminant` and multiplicative
Cauchy-Schwarz inequality `Cov_Q(w₁, w₂, x)^2 ≤ Var_Q(w₁, x) * Var_Q(w₂, x)` paired with singlet
CHSH violation `chshValue^2 > 4` (`SeparableCHSH`), Tsirelson bound `tsirelsonBound^2 = 8`
(`TsirelsonProblem`), singlet CHSH value `2 * \sqrt{2}` (`SingletNoGlobalSection`), and Pauli
$\sigma_x, \sigma_z$ Hermiticity (`BipartiteQubitCHSH`). -/
theorem multiChannelGramDeterminant_cauchySchwarz_with_bellCHSH_tsirelson_and_singletNoGlobalSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ) (x : E) :
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian ∧
      LayerC.BipartiteQubitCHSH.σz.IsHermitian := by
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ x
  exact ⟨hcs.2.1, hcs.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.BipartiteQubitCHSH.σx_isHermitian,
    LayerC.BipartiteQubitCHSH.σz_isHermitian⟩

/-- Sharp multiplicative Popoviciu variance-product and covariance-squared bounds paired with
classical random-access code bound `successCount S 0 + successCount S 1 ≤ 6`
(`InformationCausality`), LHV CHSH bound `|m.CHSH| ≤ 2` (`LHVvsRR`), and Fine's theorem
(`NoGoAnatomy`). -/
theorem multiChannelGramDeterminant_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E)
    (S_rac : LayerC.InformationCausality.ClassicalRACStrategy)
    (m_lhv : LayerC.LHVvsRR.LHVModel)
    {C_ng O_ng : ℕ} (E_emp : LayerC.NoGoAnatomy.EmpiricalModel C_ng O_ng) :
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P x) ^ 4 ∧
      LayerC.InformationCausality.successCount S_rac 0 +
        LayerC.InformationCausality.successCount S_rac 1 ≤ 6 ∧
      |m_lhv.CHSH| ≤ 2 ∧
      (LayerC.NoGoAnatomy.HasGlobalSection E_emp ↔
        LayerC.NoGoAnatomy.HasNonContextualHV E_emp) := by
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ x
  exact ⟨hpop.1, hpop.2.2.2,
    LayerC.InformationCausality.successCount_sum_le_six S_rac,
    LayerC.LHVvsRR.LHVModel.CHSH_le_two m_lhv,
    LayerC.NoGoAnatomy.fine_theorem E_emp⟩

/-- Exact $\mathrm{GL}_2(\mathbb{R})$ determinant scaling and bilateral shift invariance of
`multiChannelSpectralCovarianceGramDeterminant` paired with bipartite separation and invertible
dynamics (`BipartiteFullPostulatesQubit`, `BipartiteUnitaryQM`), and Alice-action Bob-reduced state
invariance in quantum bit commitment (`BitCommitmentImpossibility`). -/
theorem multiChannelGramDeterminant_gl2Scaling_with_bipartiteNoSignalling_and_bitCommitment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ)
    (a b c d c₁_sh c₂_sh : ℝ) (x : E)
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : LayerC.LocalRealisticAxioms.BipartiteNoSignallingAnalyticCore n_A n_B)
    {n_bc : ℕ} (U_bc ψ_bc : Matrix (Fin n_bc) (Fin n_bc) ℝ) (hU : U_bcᵀ * U_bc = 1) :
    multiChannelSpectralCovarianceGramDeterminant P
      (fun q => a * w₁ q + b * w₂ q) (fun q => c * w₁ q + d * w₂ q) x =
      (a * d - b * c) ^ 2 * multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      multiChannelSpectralCovarianceGramDeterminant P
        (fun q => w₁ q + c₁_sh) (fun q => w₂ q + c₂_sh) x =
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics ∧
      (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc)ᵀ *
        (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc) = ψ_bcᵀ * ψ_bc := by
  have hgl := multiChannelSpectralCovarianceGramDeterminant_gl2_scaling_and_shift_invariance
    P w₁ w₂ a b c d c₁_sh c₂_sh x
  exact ⟨hgl.1, hgl.2.2,
    LayerC.LocalRealisticAxioms.bipartite_separationPostulate n_A n_B hCore,
    LayerC.LocalRealisticAxioms.bipartite_invertibleDynamics n_A n_B hCore,
    LayerC.BitCommitmentImpossibility.aliceAction_preserves_bobReduced U_bc ψ_bc hU⟩

/-- Completing-the-square variance identity for `multiChannelSpectralCovarianceGramDeterminant`
paired with general-$n$ phase faithfulness (`PhaseFaithfulnessAllN`), phase-quotient and unitary QM
invertible dynamics (`PhaseQuotientUnitaryQM`, `UnitaryQMLocalRealistic`), KP raw density
Hermiticity (`SMBornRuleReconciliation`), and single-generation dimension
$N_W^{d_{\mathrm{eff}}} = 16$ (`SMPartialForcing`). -/
theorem multiChannelGramDeterminant_completingSquare_with_phaseFaithfulness_smBorn_and_smPartialForcing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ) (Q_kp P_kp : ℝ) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    multiChannelSpectralVarianceFunctional P
      (fun q => multiChannelSpectralVarianceFunctional P w₂ x * w₁ q -
        multiChannelSpectralCovarianceFunctional P w₁ w₂ x * w₂ q) x =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      (LayerC.LocalRealisticAxioms.phaseQuotientUnitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.LocalRealisticAxioms.unitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.SMBornRuleReconciliation.kpDensityRaw Q_kp P_kp).IsHermitian ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ x
  exact ⟨hcs.1,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.LocalRealisticAxioms.phaseQuotient_invertibleDynamics n_qm,
    LayerC.LocalRealisticAxioms.unitaryQuantum_invertibleDynamics n_qm,
    LayerC.SMBornRuleReconciliation.kpDensityRaw_isHermitian Q_kp P_kp,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Master synthesis of the finite `Q`-channel $2 \times 2$ spectral covariance Gram determinant,
multiplicative Cauchy-Schwarz inequality, and multiplicative Popoviciu bounds with the Bell CHSH,
Tsirelson, Phase Faithfulness, Singlet No-Global-Section, and SM Partial Forcing modules. -/
theorem multiChannelGramDeterminant_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P x) ^ 4 ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian := by
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ x
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ x
  exact ⟨hcs.2.1, hcs.2.2, hpop.2.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen,
    LayerC.BipartiteQubitCHSH.σx_isHermitian⟩

#print axioms multiChannelGramDeterminant_cauchySchwarz_with_bellCHSH_tsirelson_and_singletNoGlobalSection
#print axioms multiChannelGramDeterminant_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
#print axioms multiChannelGramDeterminant_gl2Scaling_with_bipartiteNoSignalling_and_bitCommitment
#print axioms multiChannelGramDeterminant_completingSquare_with_phaseFaithfulness_smBorn_and_smPartialForcing
#print axioms multiChannelGramDeterminant_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master

end KFCausalMultiChannelGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
end Audit
end UnifiedTheory
