/- Bridge of the Finite `Q`-Channel Normalized Spectral Variance Functional, Exact `Q × Q`
Double-Sum Lagrange Pairwise Spread Identity, and `Q`-Channel Bhatia-Davis / Popoviciu
Variance-Squared Envelope Bounds with the LayerB/LayerC Bell CHSH, Separable CHSH, Tsirelson Bound,
Bipartite Qubit No-Signalling, Bit-Commitment Impossibility, Information Causality, LHV vs.
Relational Reality, Fine's No-Go Theorem, Phase Faithfulness, Singlet No-Global-Section, and SM
Partial Forcing Modules. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
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
namespace KFCausalMultiChannelProjectorVarianceBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

open scoped InnerProduct BigOperators Matrix
open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
  (multiChannelWeightedExpectation)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelLagrangeDoubleSpread
   multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg
   multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
   multiChannelSpectralVarianceFunctional_shift_invariance)

/-- Exact `Q × Q` Lagrange double-sum pairwise channel-spread identity and nonnegativity for
`multiChannelSpectralVarianceFunctional` paired with singlet CHSH violation `chshValue^2 > 4`
(`SeparableCHSH`), Tsirelson bound `tsirelsonBound^2 = 8` (`TsirelsonProblem`), singlet CHSH value
`2 * \sqrt{2}` (`SingletNoGlobalSection`), and Pauli $\sigma_x, \sigma_z$ Hermiticity
(`BipartiteQubitCHSH`). -/
theorem multiChannelProjectorVariance_lagrangeDoubleSpread_with_bellCHSH_tsirelson_and_singletNoGlobalSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w : Fin Q_ch → ℝ) (x : E) :
    multiChannelLagrangeDoubleSpread P w x =
      2 * multiChannelSpectralVarianceFunctional P w x ∧
      0 ≤ multiChannelSpectralVarianceFunctional P w x ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian ∧
      LayerC.BipartiteQubitCHSH.σz.IsHermitian := by
  have hlag := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w x
  exact ⟨hlag.1, hlag.2.1,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.BipartiteQubitCHSH.σx_isHermitian,
    LayerC.BipartiteQubitCHSH.σz_isHermitian⟩

/-- Domination of `multiChannelSpectralVarianceFunctional` by Bhatia-Davis and Popoviciu
variance-squared bounds paired with classical random-access code bound
`successCount S 0 + successCount S 1 ≤ 6` (`InformationCausality`), LHV CHSH bound `|m.CHSH| ≤ 2`
(`LHVvsRR`), and Fine's theorem (`NoGoAnatomy`). -/
theorem multiChannelProjectorVariance_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w : Fin Q_ch → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    (S_rac : LayerC.InformationCausality.ClassicalRACStrategy)
    (m_lhv : LayerC.LHVvsRR.LHVModel)
    {C_ng O_ng : ℕ} (E_emp : LayerC.NoGoAnatomy.EmpiricalModel C_ng O_ng) :
    multiChannelSpectralVarianceFunctional P w x ≤
      (w_max * multiChannelProjectedEnergy P x - multiChannelWeightedExpectation P w x) *
        (multiChannelWeightedExpectation P w x - w_min * multiChannelProjectedEnergy P x) ∧
      multiChannelSpectralVarianceFunctional P w x ≤
        ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2 ∧
      LayerC.InformationCausality.successCount S_rac 0 +
        LayerC.InformationCausality.successCount S_rac 1 ≤ 6 ∧
      |m_lhv.CHSH| ≤ 2 ∧
      (LayerC.NoGoAnatomy.HasGlobalSection E_emp ↔
        LayerC.NoGoAnatomy.HasNonContextualHV E_emp) := by
  have hbd := multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w w_min w_max hmin hmax x
  exact ⟨hbd.2.1, hbd.2.2,
    LayerC.InformationCausality.successCount_sum_le_six S_rac,
    LayerC.LHVvsRR.LHVModel.CHSH_le_two m_lhv,
    LayerC.NoGoAnatomy.fine_theorem E_emp⟩

/-- Shift invariance of `multiChannelSpectralVarianceFunctional` paired with bipartite separation
and invertible dynamics (`BipartiteFullPostulatesQubit`, `BipartiteUnitaryQM`), and Alice-action
Bob-reduced state invariance in quantum bit commitment (`BitCommitmentImpossibility`). -/
theorem multiChannelProjectorVariance_shift_with_bipartiteNoSignalling_and_bitCommitment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w : Fin Q_ch → ℝ) (c_sh : ℝ) (x : E)
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : LayerC.LocalRealisticAxioms.BipartiteNoSignallingAnalyticCore n_A n_B)
    {n_bc : ℕ} (U_bc ψ_bc : Matrix (Fin n_bc) (Fin n_bc) ℝ) (hU : U_bcᵀ * U_bc = 1) :
    multiChannelSpectralVarianceFunctional P (fun q => w q + c_sh) x =
      multiChannelSpectralVarianceFunctional P w x ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics ∧
      (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc)ᵀ *
        (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc) = ψ_bcᵀ * ψ_bc := by
  have hsh := multiChannelSpectralVarianceFunctional_shift_invariance P w c_sh x
  exact ⟨hsh.2,
    LayerC.LocalRealisticAxioms.bipartite_separationPostulate n_A n_B hCore,
    LayerC.LocalRealisticAxioms.bipartite_invertibleDynamics n_A n_B hCore,
    LayerC.BitCommitmentImpossibility.aliceAction_preserves_bobReduced U_bc ψ_bc hU⟩

/-- `Q`-channel spectral variance Lagrange double-sum spread identity paired with general-$n$ phase
faithfulness (`PhaseFaithfulnessAllN`), phase-quotient and unitary QM invertible dynamics
(`PhaseQuotientUnitaryQM`, `UnitaryQMLocalRealistic`), KP raw density Hermiticity
(`SMBornRuleReconciliation`), and single-generation dimension $N_W^{d_{\mathrm{eff}}} = 16$
(`SMPartialForcing`). -/
theorem multiChannelProjectorVariance_with_phaseFaithfulness_smBorn_and_smPartialForcing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w : Fin Q_ch → ℝ) (Q_kp P_kp : ℝ) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    multiChannelLagrangeDoubleSpread P w x =
      2 * multiChannelSpectralVarianceFunctional P w x ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      (LayerC.LocalRealisticAxioms.phaseQuotientUnitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.LocalRealisticAxioms.unitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.SMBornRuleReconciliation.kpDensityRaw Q_kp P_kp).IsHermitian ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  have hlag := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w x
  exact ⟨hlag.1,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.LocalRealisticAxioms.phaseQuotient_invertibleDynamics n_qm,
    LayerC.LocalRealisticAxioms.unitaryQuantum_invertibleDynamics n_qm,
    LayerC.SMBornRuleReconciliation.kpDensityRaw_isHermitian Q_kp P_kp,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Master synthesis of the finite `Q`-channel normalized spectral variance functional, `Q × Q`
Lagrange double-sum spread identity, and Bhatia-Davis / Popoviciu variance-squared bounds with the
Bell CHSH, Tsirelson, Phase Faithfulness, Singlet No-Global-Section, and SM Partial Forcing
modules. -/
theorem multiChannelProjectorVariance_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w : Fin Q_ch → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    multiChannelLagrangeDoubleSpread P w x =
      2 * multiChannelSpectralVarianceFunctional P w x ∧
      0 ≤ multiChannelSpectralVarianceFunctional P w x ∧
      multiChannelSpectralVarianceFunctional P w x ≤
        ((w_max - w_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 2 ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian := by
  have hlag := multiChannelSpectralVarianceFunctional_eq_lagrangeDoubleSpread_and_nonneg P w x
  have hbd := multiChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    P w w_min w_max hmin hmax x
  exact ⟨hlag.1, hbd.1, hbd.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen,
    LayerC.BipartiteQubitCHSH.σx_isHermitian⟩

#print axioms multiChannelProjectorVariance_lagrangeDoubleSpread_with_bellCHSH_tsirelson_and_singletNoGlobalSection
#print axioms multiChannelProjectorVariance_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
#print axioms multiChannelProjectorVariance_shift_with_bipartiteNoSignalling_and_bitCommitment
#print axioms multiChannelProjectorVariance_with_phaseFaithfulness_smBorn_and_smPartialForcing
#print axioms multiChannelProjectorVariance_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master

end KFCausalMultiChannelProjectorVarianceBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
end Audit
end UnifiedTheory
