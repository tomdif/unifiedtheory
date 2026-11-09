/- Bridge of the Six-Vector Orthogonality Certificate ($M^T M = I_3$ and $(\det M)^2 = 1$
Quantum-Channel $3 \times 3$ Gram Determinant Conservation), Unimodular Scalar-Zero Lattice Generation,
Short Projective-Root Householder Reflection Involution, and Octahedral-to-Legendre Elliptic
$j$-Invariant Identity with the LayerB/LayerC Bell CHSH, Separable CHSH, Tsirelson Bound,
Bipartite Qubit No-Signalling, Bit-Commitment Impossibility, Information Causality, LHV vs.
Relational Reality, Fine's No-Go Theorem, Phase Faithfulness, Singlet No-Global-Section, and SM
Partial Forcing Modules. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant
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
namespace KFCausalMultiChannelSixVectorOrthogonalityShortRootReflectionBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

open scoped InnerProduct BigOperators Matrix
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional)
open KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant)
open KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelSpectralPartialCovariance
   multiChannelThreeByThreeSpectralGramDeterminant
   multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz)
open KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction
  (multiChannelTernaryLinearCombination
   gl3Determinant
   multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
   multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
   multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds)
open KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant
  (ternaryMatrixImageNorm
   reflectiveNorm71 reflect71X reflect71Y reflect71Z
   octahedralJ legendreJ
   six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
   octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic)

/-- Six-Vector Orthogonality Certificate ($(\det M)^2 = 1$ and quantum-channel $3 \times 3$ Gram
determinant conservation) and Ramanujan Six-Direction covariance reconstruction paired with singlet
CHSH violation `chshValue^2 > 4` (`SeparableCHSH`), Tsirelson bound `tsirelsonBound^2 = 8`
(`TsirelsonProblem`), singlet CHSH value `2 * \sqrt{2}` (`SingletNoGlobalSection`), and Pauli
$\sigma_x, \sigma_z$ Hermiticity (`BipartiteQubitCHSH`). -/
theorem multiChannelSixVectorOrthogonality_and_ramanujanSixDirection_with_bellCHSH_tsirelson_and_singletNoGlobalSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    (x : E) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    let D₁ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) x
    let D₂ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) x
    let D₃ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) x
    let D₄ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) x
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₂ x = D₁ - D₂ - D₃ + D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₁ w₃ x = D₁ - D₂ + D₃ - D₄ ∧
    8 * multiChannelSpectralCovarianceFunctional P w₂ w₃ x = D₁ + D₂ - D₃ - D₄ ∧
    LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
    LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
    LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
    LayerC.BipartiteQubitCHSH.σx.IsHermitian ∧
    LayerC.BipartiteQubitCHSH.σz.IsHermitian := by
  intro u₁ u₂ u₃ D₁ D₂ D₃ D₄
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hram := multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    P w₁ w₂ w₃ x
  exact ⟨horth.2.2.1, horth.2.2.2, hram.1, hram.2.1, hram.2.2.1,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.BipartiteQubitCHSH.σx_isHermitian,
    LayerC.BipartiteQubitCHSH.σz_isHermitian⟩

/-- Short projective-root `p = 71` reflection involution and $\mathrm{GL}_3(\mathbb{R})$-scaled
Hadamard & $3 \times 3$ Popoviciu bounds paired with classical random-access code bound
`successCount S 0 + successCount S 1 ≤ 6` (`InformationCausality`) — matching the 6 vectors of the
Ramanujan orthogonality certificate — LHV CHSH bound `|m.CHSH| ≤ 2` (`LHVvsRR`), and Fine's theorem
(`NoGoAnatomy`). -/
theorem multiChannelShortRootReflection_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max)
    (x_int y_int z_int : ℤ) (x : E)
    (S_rac : LayerC.InformationCausality.ClassicalRACStrategy)
    (m_lhv : LayerC.LHVvsRR.LHVModel)
    {C_ng O_ng : ℕ} (E_emp : LayerC.NoGoAnatomy.EmpiricalModel C_ng O_ng) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    let detA := gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
    reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
      (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
    reflect71X (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
      (reflect71Z x_int y_int z_int) = x_int ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x ≤
      detA ^ 2 *
        (multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x *
          multiChannelSpectralVarianceFunctional P w₃ x) ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x ≤
      detA ^ 2 *
        (((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6) ∧
    LayerC.InformationCausality.successCount S_rac 0 +
      LayerC.InformationCausality.successCount S_rac 1 ≤ 6 ∧
    |m_lhv.CHSH| ≤ 2 ∧
    (LayerC.NoGoAnatomy.HasGlobalSection E_emp ↔
      LayerC.NoGoAnatomy.HasNonContextualHV E_emp) := by
  intro u₁ u₂ u₃ detA
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃
    w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  refine ⟨?_, ?_, hpop.2.1, hpop.2.2,
    LayerC.InformationCausality.successCount_sum_le_six S_rac,
    LayerC.LHVvsRR.LHVModel.CHSH_le_two m_lhv,
    LayerC.NoGoAnatomy.fine_theorem E_emp⟩
  · unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z; ring
  · unfold reflect71X reflect71Y reflect71Z; ring

/-- Octahedral-to-Legendre elliptic $j$-invariant identity and $\mathrm{SL}_3(\mathbb{R})$ 3D shear
invariance paired with bipartite separation and invertible dynamics (`BipartiteFullPostulatesQubit`,
`BipartiteUnitaryQM`), and Alice-action Bob-reduced state invariance in quantum bit commitment
(`BitCommitmentImpossibility`). -/
theorem multiChannelOctahedralLegendreJ_and_shearInvariance_with_bipartiteNoSignalling_and_bitCommitment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (α β γ : ℝ) {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0) (x : E)
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : LayerC.LocalRealisticAxioms.BipartiteNoSignallingAnalyticCore n_A n_B)
    {n_bc : ℕ} (U_bc ψ_bc : Matrix (Fin n_bc) (Fin n_bc) ℝ) (hU : U_bcᵀ * U_bc = 1) :
    let D₁ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) x
    let D₂ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) x
    let D₃ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) x
    let D₄ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) x
    (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) ∧
    multiChannelThreeByThreeSpectralGramDeterminant P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 α β)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 1 γ)
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 0 0 1) x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    4 * (multiChannelSpectralVarianceFunctional P w₁ x +
      multiChannelSpectralVarianceFunctional P w₂ x +
      multiChannelSpectralVarianceFunctional P w₃ x) = D₁ + D₂ + D₃ + D₄ ∧
    (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate ∧
    (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).InvertibleDynamics ∧
    (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc)ᵀ *
      (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc) = ψ_bcᵀ * ψ_bc := by
  intro D₁ D₂ D₃ D₄
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  have hgl3 := multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    P w₁ w₂ w₃ 1 α β 0 1 γ 0 0 1 α β γ x
  have hram := multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    P w₁ w₂ w₃ x
  exact ⟨hj.1, hgl3.2.2, hram.2.2.2.1,
    LayerC.LocalRealisticAxioms.bipartite_separationPostulate n_A n_B hCore,
    LayerC.LocalRealisticAxioms.bipartite_invertibleDynamics n_A n_B hCore,
    LayerC.BitCommitmentImpossibility.aliceAction_preserves_bobReduced U_bc ψ_bc hU⟩

/-- Unimodular scalar-zero generator determinant `p^3`, Ramanujan Six-Direction diagonal variance
reconstruction, and Sylvester's $3 \times 3$ determinant identity paired with general-$n$ phase
faithfulness (`PhaseFaithfulnessAllN`), phase-quotient and unitary QM invertible dynamics
(`PhaseQuotientUnitaryQM`, `UnitaryQMLocalRealistic`), KP raw density Hermiticity
(`SMBornRuleReconciliation`), and single-generation dimension $N_W^{d_{\mathrm{eff}}} = 16$
(`SMPartialForcing`). -/
theorem multiChannelUnimodularGenerators_and_sylvester_with_phaseFaithfulness_smBorn_and_smPartialForcing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ) (p Q_kp P_kp : ℝ) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    let D₁ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 1) x
    let D₂ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ (-1) 1 1) x
    let D₃ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 (-1) 1) x
    let D₄ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 1 (-1)) x
    let D₅ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 2 1 1) x
    let D₆ := multiChannelSpectralVarianceFunctional P
      (multiChannelTernaryLinearCombination w₁ w₂ w₃ 1 2 1) x
    gl3Determinant p p p (2 * p) p p p (2 * p) p = p ^ 3 ∧
    6 * multiChannelSpectralVarianceFunctional P w₁ x = 2 * D₅ - 3 * D₁ + D₂ ∧
    6 * multiChannelSpectralVarianceFunctional P w₂ x = 2 * D₆ - 3 * D₁ + D₃ ∧
    12 * multiChannelSpectralVarianceFunctional P w₃ x =
      15 * D₁ + D₂ + D₃ + 3 * D₄ - 4 * D₅ - 4 * D₆ ∧
    multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x *
      multiChannelSpectralCovarianceGramDeterminant P w₃ w₂ x -
      (multiChannelSpectralPartialCovariance P w₁ w₃ w₂ x) ^ 2 =
      multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
    (LayerC.LocalRealisticAxioms.phaseQuotientUnitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
    (LayerC.LocalRealisticAxioms.unitaryQuantumNoSignalling n_qm).InvertibleDynamics ∧
    (LayerC.SMBornRuleReconciliation.kpDensityRaw Q_kp P_kp).IsHermitian ∧
    LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  intro D₁ D₂ D₃ D₄ D₅ D₆
  have hram := multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
    P w₁ w₂ w₃ x
  have hsylv := multiChannelThreeByThreeSpectralGramDeterminant_sylvester_identity_and_partial_cauchy_schwarz
    P w₁ w₂ w₃ x
  refine ⟨by unfold gl3Determinant; ring,
    hram.2.2.2.2.1, hram.2.2.2.2.2.1, hram.2.2.2.2.2.2, hsylv.1,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.LocalRealisticAxioms.phaseQuotient_invertibleDynamics n_qm,
    LayerC.LocalRealisticAxioms.unitaryQuantum_invertibleDynamics n_qm,
    LayerC.SMBornRuleReconciliation.kpDensityRaw_isHermitian Q_kp P_kp,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Master synthesis of the Six-Vector Orthogonality Certificate, Quantum-Channel $3 \times 3$
Gram Determinant Conservation, Short-Root Householder Reflection Involution, and
Octahedral-to-Legendre Elliptic $j$-Invariant Identity with the Bell CHSH, Tsirelson, Phase
Faithfulness, Singlet No-Global-Section, and SM Partial Forcing modules. -/
theorem multiChannelSixVectorOrthogonality_shortRootReflection_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    (x_int y_int z_int : ℤ)
    {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0) (x : E)
    (n_qm : ℕ) [NeZero n_qm] :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
    reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
      (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
    -256 * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) ∧
    LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
    LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
    LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
    LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
    LayerC.SMPartialForcing.N_W_pow_d_eff = 16 ∧
    LayerC.BipartiteQubitCHSH.σx.IsHermitian := by
  intro u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  refine ⟨horth.2.2.1, horth.2.2.2, ?_, hj.1,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen,
    LayerC.BipartiteQubitCHSH.σx_isHermitian⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

#print axioms multiChannelSixVectorOrthogonality_and_ramanujanSixDirection_with_bellCHSH_tsirelson_and_singletNoGlobalSection
#print axioms multiChannelShortRootReflection_popoviciu_with_informationCausality_lhvCHSH_and_fineTheorem
#print axioms multiChannelOctahedralLegendreJ_and_shearInvariance_with_bipartiteNoSignalling_and_bitCommitment
#print axioms multiChannelUnimodularGenerators_and_sylvester_with_phaseFaithfulness_smBorn_and_smPartialForcing
#print axioms multiChannelSixVectorOrthogonality_shortRootReflection_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master

end KFCausalMultiChannelSixVectorOrthogonalityShortRootReflectionBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
end Audit
end UnifiedTheory
