/- Bridge of the Euler Partition Generating Function Reciprocal Partial-Product Bounds
$1 + \sum_{k=0}^{N-1} q^{k+1} \le \prod_{k=0}^{N-1} (1 - q^{k+1})^{-1} \le \frac{1 - q}{1 - 2q}$
on $0 \le q < 1/2$, Exact Reciprocal Cancellation $P_N(q) Q_N(q) = 1$, Two-Channel
Rademacher-Kloosterman Subleading Hierarchy
$S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2 = \frac{c_2 - c_1}{c_1 c_2} S_{\mathrm{BH}} \ge 0$,
Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Bilateral Constant-Term Decomposition, Six-Vector
Orthogonality Certificate, Short Projective-Root `p = 71` Householder Reflection Isometry, and
Octahedral-to-Legendre Elliptic $j$-Invariant Identity with the Bell CHSH, Tsirelson Bound,
Information Causality, LHV vs RR, Fine's Theorem, Bit Commitment, Phase Faithfulness, and SM
Partial Forcing Modules. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy
import UnifiedTheory.Audit.KFCausalMultiChannelQPochhammerWeierstrassKloostermanRademacherGapBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalMultiChannelEulerPartitionReciprocalKloostermanHierarchyBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge

open scoped Matrix
open KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelThreeByThreeSpectralGramDeterminant)
open KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction
  (multiChannelTernaryLinearCombination
   gl3Determinant)
open KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant
  (ternaryMatrixImageNorm
   reflectiveNorm71 reflect71X reflect71Y reflect71Z
   octahedralJ legendreJ
   six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
   octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic)
open KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy
  (mtc0ClearedDifference
   mtc1ClearedDifference
   mtc0ThetaReducedResidual
   mtc1ThetaReducedResidual
   rademacherCardySaddleExponent
   rademacherCardyMinimalEntropy
   mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
   mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
   rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound)
open KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap
  (qPochhammerPartialProduct
   qGeometricPartialSum
   rademacherKloostermanChannelExponent)
open KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy
  (qPartitionGeneratingPartialProduct
   qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
   qPartitionGeneratingPartialProduct_lower_and_upper_bounds
   rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
   mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman
   multiChannel_eulerPartitionReciprocal_and_kloosterman_twoChannel_hierarchy_master_synthesis)
open KFCausalMultiChannelQPochhammerWeierstrassKloostermanRademacherGapBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
  (multiChannel_qPochhammer_weierstrass_kloostermanRademacher_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master)

/-- Euler partition generating function reciprocal bounds, `MTC₀` bilateral constant-term
factorization, and Six-Vector Orthogonality Certificate paired with Bell CHSH violation
$\mathrm{CHSH}^2 > 4$, Tsirelson bound $(2\sqrt{2})^2 = 8$, and singlet correlation
$\mathrm{CHSH} = 2\sqrt{2}$. -/
theorem eulerPartitionReciprocal_and_sixVectorOrthogonality_with_bell_chsh_and_tsirelson_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    {R_q : Type*} [CommRing R_q]
    (qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 : R_q)
    (hqfac0 : qfac = J2_5 * (P1_5 * P4_5))
    (hPhi1 : Phi1 - 1 = B0_lead + B0_tail)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (x : E) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N = 1 ∧
      1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 ∧
      (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
      multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 := by
  intro u₁ u₂ u₃
  have hq_lt1 : q < 1 := by linarith
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation q hq_nn hq_lt1 N
  have hB := qPartitionGeneratingPartialProduct_lower_and_upper_bounds q hq_nn hq_half N
  have hmtc0 := mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 hqfac0 hPhi1
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  exact ⟨hQ.2.1, hB.2.2.1, hB.2.2.2.1, hmtc0.1, horth.2.2.1, horth.2.2.2,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh⟩

/-- Two-channel Rademacher-Kloosterman subleading hierarchy, `MTC₁` bilateral constant-term
factorization, and short projective-root `p = 71` Householder reflection isometry paired with
Information Causality classical RAC bound `≤ 6`, LHV classical CHSH bound `≤ 2`, and Fine's
Joint-Distribution Theorem. -/
theorem kloostermanTwoChannel_hierarchy_and_shortRootReflection_with_informationCausality_lhv_and_finesTheorem
    {R_q : Type*} [CommRing R_q]
    (X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 : R_q)
    (hqfac1 : qfac = J1_5 * (P2_5 * P3_5))
    (hPhi2 : Phi2 - 1 = B1_lead + B1_tail)
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ)
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂)
    (x_int y_int z_int : ℤ)
    (S_rac : LayerC.InformationCausality.ClassicalRACStrategy)
    (m_lhv : LayerC.LHVvsRR.LHVModel)
    {C_ng O_ng : ℕ} (E_emp : LayerC.NoGoAnatomy.EmpiricalModel C_ng O_ng) :
    rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 ∧
      reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
        (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
      LayerC.InformationCausality.successCount S_rac 0 +
        LayerC.InformationCausality.successCount S_rac 1 ≤ 6 ∧
      |m_lhv.CHSH| ≤ 2 ∧
      (LayerC.NoGoAnatomy.HasGlobalSection E_emp ↔
        LayerC.NoGoAnatomy.HasNonContextualHV E_emp) := by
  have hK2 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₁ c₂ hc₁ hc₁₂
  have hmtc1 := mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 hqfac1 hPhi2
  refine ⟨hK2.1, hK2.2.1, hmtc1.1, ?_,
    LayerC.InformationCausality.successCount_sum_le_six S_rac,
    LayerC.LHVvsRR.LHVModel.CHSH_le_two m_lhv,
    LayerC.NoGoAnatomy.fine_theorem E_emp⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

/-- Euler partition generating function reciprocal bounds, two-channel Rademacher-Kloosterman
subleading hierarchy, and Rademacher-Cardy saddle-point quadratic completion paired with
octahedral-to-Legendre elliptic $j$-invariant identity, Mayers-Lo-Chau quantum bit-commitment no-go,
Phase Faithfulness analytic core, and SM partial forcing $N_W^{d_{\mathrm{eff}}} = 16$. -/
theorem eulerPartitionReciprocal_and_kloostermanTwoChannel_with_bitCommitment_phaseFaithfulness_and_smPartialForcing
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂)
    {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0)
    {n_bc : ℕ} (U_bc ψ_bc : Matrix (Fin n_bc) (Fin n_bc) ℝ) (hU : U_bcᵀ * U_bc = 1)
    (n_qm : ℕ) [NeZero n_qm] :
    1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) ∧
      (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc)ᵀ *
        (LayerC.BitCommitmentImpossibility.aliceAction U_bc ψ_bc) = ψ_bcᵀ * ψ_bc ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  have hB := qPartitionGeneratingPartialProduct_lower_and_upper_bounds q hq_nn hq_half N
  have hcardy := rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    C_eff Δ β hC hΔ hβ
  have hK2 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₁ c₂ hc₁ hc₁₂
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  exact ⟨hB.2.2.1, hB.2.2.2.1, hcardy.1, hK2.2.1, hj.1,
    LayerC.BitCommitmentImpossibility.aliceAction_preserves_bobReduced U_bc ψ_bc hU,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) reciprocal partition multiplier cancellation
and Euler partition generating function bounds paired with Bell CHSH violation, Tsirelson bound,
singlet CHSH saturation, Phase Faithfulness analytic core, and SM partial forcing. -/
theorem mockTheta_reciprocal_partition_cancellation_with_bell_tsirelson_phaseFaithfulness_and_smPartialForcing
    {R_q : Type*} [CommRing R_q]
    (X qfac qfac_N qinv_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 : R_q)
    (hqfac_split : qfac = qfac_N * qfac_tail)
    (hqinv : qinv_N * qfac_N = 1)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (n_qm : ℕ) [NeZero n_qm] :
    qinv_N * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_tail * (f0 + 2 * (Phi1 - 1)) - qinv_N * (J5_10 * J2_5) ∧
      qinv_N * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_tail * (X * f1 + 2 * (Phi2 - 1)) - qinv_N * (X * (J5_10 * J1_5)) ∧
      qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N = 1 ∧
      1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  have hrec := mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman
    X qfac qfac_N qinv_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 hqfac_split hqinv q hq_nn hq_half N
  exact ⟨hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1,
    LayerB.SeparableCHSH.singlet_chsh_sq_gt_four,
    LayerC.TsirelsonProblem.tsirelson_sq,
    LayerC.SingletNoGlobalSection.singletCorrelation_chsh,
    LayerC.LocalRealisticAxioms.phaseFaithfulnessAnalyticCore_general n_qm,
    LayerC.SMPartialForcing.N_W_pow_d_eff_eq_sixteen⟩

/-- Master synthesis uniting the Euler partition generating function reciprocal partial-product
bounds $1 + S_N(q) \le Q_N(q) \le \frac{1-q}{1-2q}$, exact reciprocal cancellation
$P_N(q) Q_N(q) = 1$, two-channel Rademacher-Kloosterman subleading hierarchy, Rademacher-Cardy
saddle-point quadratic completion, fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term decompositions, Six-Vector Orthogonality Certificate, short projective-root `p = 71`
Householder reflection isometry, and octahedral-to-Legendre elliptic $j$-invariant identity with
the Bell CHSH, Tsirelson, Singlet No-Global-Section, Phase Faithfulness, and SM Partial Forcing
modules. -/
theorem multiChannel_eulerPartitionReciprocal_kloostermanTwoChannel_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    {R_q : Type*} [CommRing R_q]
    (X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2
     B0_lead B0_tail B1_lead B1_tail : R_q)
    (hq5 : qfac = P0_5 * P1_5 * P2_5 * P3_5 * P4_5)
    (hJ2 : J2_5 = P0_5 * P2_5 * P3_5)
    (hJ1 : J1_5 = P0_5 * P1_5 * P4_5)
    (hPhi1 : Phi1 - 1 = B0_lead + B0_tail)
    (hPhi2 : Phi2 - 1 = B1_lead + B1_tail)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂)
    (x_int y_int z_int : ℤ)
    {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0)
    (x : E) (n_qm : ℕ) [NeZero n_qm] :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
      multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ x =
        multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 ∧
      mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 ∧
      qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N = 1 ∧
      1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
        (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) ∧
      LayerB.BellTheorem.chshValue ^ 2 > 4 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 ∧
      LayerC.SingletNoGlobalSection.singletCorrelation.CHSH = 2 * Real.sqrt 2 ∧
      LayerC.LocalRealisticAxioms.PhaseFaithfulnessAnalyticCore n_qm ∧
      LayerC.SMPartialForcing.N_W_pow_d_eff = 16 := by
  intro u₁ u₂ u₃
  have hq_lt1 : q < 1 := by linarith
  have h10 := multiChannel_eulerPartitionReciprocal_and_kloosterman_twoChannel_hierarchy_master_synthesis
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2
    B0_lead B0_tail B1_lead B1_tail hq5 hJ2 hJ1 hPhi1 hPhi2
    q hq_nn hq_half N C_eff Δ β hC hΔ hβ c₁ c₂ hc₁ hc₁₂
    x_int y_int z_int hi_c hj_c hk_c hiso_c x
  have h25 := multiChannel_qPochhammer_weierstrass_kloostermanRademacher_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2
    B0_lead B0_tail B1_lead B1_tail hq5 hJ2 hJ1 hPhi1 hPhi2
    q hq_nn hq_lt1 N C_eff Δ β hC hΔ hβ c₁ hc₁
    x_int y_int z_int hi_c hj_c hk_c hiso_c x n_qm
  exact ⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.1, h10.2.2.2.2.2.1,
    h10.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.2.1,
    h10.2.2.2.2.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.2.2.2,
    h25.2.2.2.2.2.2.2.2.2.2.2.2.1, h25.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h25.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h25.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h25.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

#print axioms eulerPartitionReciprocal_and_sixVectorOrthogonality_with_bell_chsh_and_tsirelson_bounds
#print axioms kloostermanTwoChannel_hierarchy_and_shortRootReflection_with_informationCausality_lhv_and_finesTheorem
#print axioms eulerPartitionReciprocal_and_kloostermanTwoChannel_with_bitCommitment_phaseFaithfulness_and_smPartialForcing
#print axioms mockTheta_reciprocal_partition_cancellation_with_bell_tsirelson_phaseFaithfulness_and_smPartialForcing
#print axioms multiChannel_eulerPartitionReciprocal_kloostermanTwoChannel_bell_chsh_tsirelson_phaseFaithfulness_noGo_bridge_master

end KFCausalMultiChannelEulerPartitionReciprocalKloostermanHierarchyBellCHSHTsirelsonPhaseFaithfulnessNoGoBridge
end Audit
end UnifiedTheory
