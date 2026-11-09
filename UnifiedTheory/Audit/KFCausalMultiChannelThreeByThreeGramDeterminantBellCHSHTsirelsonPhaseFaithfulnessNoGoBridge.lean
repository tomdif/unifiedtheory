/- Bridge of the Finite `Q`-Channel Three-Profile $3 \times 3$ Sylvester-Jacobi Spectral Covariance
Gram Determinant `Det3_Q(w₁, w₂, w₃, x)`, Hadamard's $3 \times 3$ Determinant Inequality, Sylvester
Identity, Trilateral Shift Invariance, and $3 \times 3$ Popoviciu Bounds with the LayerB/LayerC Bell
CHSH, Separable CHSH, Tsirelson Bound, Bipartite Qubit No-Signalling, Bit-Commitment Impossibility,
Information Causality, LHV vs. Relational Reality, Fine's No-Go Theorem, Phase Faithfulness, Singlet
No-Global-Section, and SM Partial Forcing Modules. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
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
namespace KFCausalMultiChannelThreeByThreeGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

open scoped InnerProduct BigOperators Matrix
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional
   multiChannelSpectralVarianceFunctional_shift_invariance)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional
   multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance)
open KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant)
open KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelSpectralPartialCovariance
   multiChannelThreeByThreeSpectralGramDeterminant
   multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
   multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
   multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds)

/-- Nonnegativity of `multiChannelThreeByThreeSpectralGramDeterminant` and Hadamard's $3 \times 3$
determinant inequality `Det3_Q(w₁, w₂, w₃, x) ≤ Var_Q(w₁, x) * Var_Q(w₂, x) * Var_Q(w₃, x)` paired
with singlet CHSH violation `chshValue^2 > 4` (`SeparableCHSH`), Tsirelson bound
`tsirelsonBound^2 = 8` (`TsirelsonProblem`), singlet CHSH value `2 * \sqrt{2}`
(`SingletNoGlobalSection`), and Pauli $\sigma_x, \sigma_z$ Hermiticity (`BipartiteQubitCHSH`). -/
theorem multiChannelThreeByThreeGramDeterminant_hadamard_with_bellCHSH_tsirelson_and_singletNoGlobalSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ) (x : E) :
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralVarianceFunctional P w₃ x ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian ∧
      LayerC.BipartiteQubitCHSH.σz.IsHermitian := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  exact ⟨hhad.1, hhad.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.BipartiteQubitCHSH.σx_isHermitian,
    LayerC.BipartiteQubitCHSH.σz_isHermitian⟩

/-- Sharp $3 \times 3$ Hadamard-Popoviciu variance-product and Gram determinant bounds paired with
classical random-access code bound `successCount S 0 + successCount S 1 ≤ 6`
(`InformationCausality`), LHV CHSH bound `|m.CHSH| ≤ 2` (`LHVvsRR`), and Fine's theorem
(`NoGoAnatomy`). -/
theorem multiChannelThreeByThreeGramDeterminant_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E)
    (S_rac : LayerC.InformationCausality.ClassicalRACStrategy)
    (m_lhv : LayerC.LHVvsRR.LHVModel)
    {C_ng O_ng : ℕ} (E_emp : LayerC.NoGoAnatomy.EmpiricalModel C_ng O_ng) :
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralVarianceFunctional P w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 ∧
      LayerC.InformationCausality.successCount S_rac 0 +
        LayerC.InformationCausality.successCount S_rac 1 ≤ 6 ∧
      |m_lhv.CHSH| ≤ 2 ∧
      (LayerC.NoGoAnatomy.HasGlobalSection E_emp ↔
        LayerC.NoGoAnatomy.HasNonContextualHV E_emp) := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  exact ⟨hhad.2.2, hpop.2.2,
    LayerC.InformationCausality.successCount_sum_le_six S_rac,
    LayerC.LHVvsRR.LHVModel.CHSH_le_two m_lhv,
    LayerC.NoGoAnatomy.fine_theorem E_emp⟩

/-- Trilateral shift invariance and Laplace-Sylvester block upper bound of
`multiChannelThreeByThreeSpectralGramDeterminant` paired with bipartite separation and invertible
dynamics (`BipartiteFullPostulatesQubit`, `BipartiteUnitaryQM`), and Alice-action Bob-reduced state
invariance in quantum bit commitment (`BitCommitmentImpossibility`). -/
theorem multiChannelThreeByThreeGramDeterminant_shiftInvariance_with_bipartiteNoSignalling_and_bitCommitment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (c₁_sh c₂_sh c₃_sh : ℝ) (x : E)
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : LayerC.LocalRealisticAxioms.BipartiteNoSignallingAnalyticCore n_A n_B)
    {n_bc : ℕ} (U_bc ψ_bc : Matrix (Fin n_bc) (Fin n_bc) ℝ) (hU : U_bcᵀ * U_bc = 1) :
    multiChannelThreeByThreeSpectralGramDeterminant P
      (fun q => w₁ q + c₁_sh) (fun q => w₂ q + c₂_sh) (fun q => w₃ q + c₃_sh) x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralCovarianceGramDeterminant P w₂ w₃ x ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics ∧
      (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc)ᵀ *
        (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc) = ψ_bcᵀ * ψ_bc := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hsh :
      multiChannelThreeByThreeSpectralGramDeterminant P
        (fun q => w₁ q + c₁_sh) (fun q => w₂ q + c₂_sh) (fun q => w₃ q + c₃_sh) x =
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x := by
    unfold multiChannelThreeByThreeSpectralGramDeterminant
    rw [(multiChannelSpectralVarianceFunctional_shift_invariance P w₁ c₁_sh x).2,
      (multiChannelSpectralVarianceFunctional_shift_invariance P w₂ c₂_sh x).2,
      (multiChannelSpectralVarianceFunctional_shift_invariance P w₃ c₃_sh x).2,
      (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance P w₁ w₂ c₁_sh c₂_sh x).2,
      (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance P w₂ w₃ c₂_sh c₃_sh x).2,
      (multiChannelSpectralCovarianceFunctional_bilateral_shift_invariance P w₁ w₃ c₁_sh c₃_sh x).2]
  exact ⟨hsh, hhad.2.1,
    LayerC.LocalRealisticAxioms.bipartite_separationPostulate n_A n_B hCore,
    LayerC.LocalRealisticAxioms.bipartite_invertibleDynamics n_A n_B hCore,
    LayerC.BitCommitmentImpossibility.aliceAction_preserves_bobReduced U_bc ψ_bc hU⟩

/-- Sylvester's $3 \times 3$ determinant identity and partial covariance Cauchy-Schwarz inequality
paired with general-$n$ phase faithfulness (`PhaseFaithfulnessAllN`), phase-quotient and unitary QM
invertible dynamics (`PhaseQuotientUnitaryQM`, `UnitaryQMLocalRealistic`), KP raw density
Hermiticity (`SMBornRuleReconciliation`), and single-generation dimension
$N_W^{d_{\mathrm{eff}}} = 16$ (`SMPartialForcing`). -/
theorem multiChannelThreeByThreeGramDeterminant_sylvester_with_phaseFaithfulness_smBorn_and_smPartialForcing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ) (Q_kp P_kp : ℝ) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
      multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 ≤
        multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
          multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      (LayerC.LocalRealisticAxioms.phaseQuotientUnitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.LocalRealisticAxioms.unitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
      (LayerC.SMBornRuleReconciliation.kpDensityRaw Q_kp P_kp).IsHermitian ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  have hsylv := multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    P w₁ w₂ w₃ x
  exact ⟨hsylv.1, hsylv.2.2,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.LocalRealisticAxioms.phaseQuotient_invertibleDynamics n_qm,
    LayerC.LocalRealisticAxioms.unitaryQuantum_invertibleDynamics n_qm,
    LayerC.SMBornRuleReconciliation.kpDensityRaw_isHermitian Q_kp P_kp,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Master synthesis of the finite `Q`-channel $3 \times 3$ Sylvester-Jacobi spectral covariance
Gram determinant, Hadamard's $3 \times 3$ determinant inequality, and $3 \times 3$ Popoviciu bounds
with the Bell CHSH, Tsirelson, Phase Faithfulness, Singlet No-Global-Section, and SM Partial Forcing
modules. -/
theorem multiChannelThreeByThreeGramDeterminant_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralVarianceFunctional P w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  exact ⟨hhad.1, hhad.2.2, hpop.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen,
    LayerC.BipartiteQubitCHSH.σx_isHermitian⟩

#print axioms multiChannelThreeByThreeGramDeterminant_hadamard_with_bellCHSH_tsirelson_and_singletNoGlobalSection
#print axioms multiChannelThreeByThreeGramDeterminant_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
#print axioms multiChannelThreeByThreeGramDeterminant_shiftInvariance_with_bipartiteNoSignalling_and_bitCommitment
#print axioms multiChannelThreeByThreeGramDeterminant_sylvester_with_phaseFaithfulness_smBorn_and_smPartialForcing
#print axioms multiChannelThreeByThreeGramDeterminant_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master

end KFCausalMultiChannelThreeByThreeGramDeterminantBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
end Audit
end UnifiedTheory
