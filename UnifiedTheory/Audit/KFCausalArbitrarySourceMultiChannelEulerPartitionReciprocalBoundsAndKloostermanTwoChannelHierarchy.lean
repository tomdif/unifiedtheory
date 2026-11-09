/- Arbitrary-Source Multi-Channel Euler Partition Generating Function Reciprocal Partial-Product
Bounds $1 + \sum_{k=0}^{N-1} q^{k+1} \le 2 - \prod_{k=0}^{N-1} (1 - q^{k+1}) \le
\prod_{k=0}^{N-1} (1 - q^{k+1})^{-1} \le \frac{1 - q}{1 - 2q}$ on $0 \le q < 1/2$, Exact Reciprocal
Cancellation $P_N(q) Q_N(q) = 1$, Two-Channel Rademacher-Kloosterman Subleading Hierarchy
$S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2 = \frac{c_2 - c_1}{c_1 c_2} S_{\mathrm{BH}} \ge 0$ for
$2 \le c_1 \le c_2$, Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Reciprocal Partition
Cancellation, and Quantum-Channel $3 \times 3$ Gram Determinant Synthesis. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy

open scoped BigOperators
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
   mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
   rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound)
open KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap
  (qPochhammerPartialProduct
   qGeometricPartialSum
   rademacherKloostermanChannelExponent
   qPochhammerPartialProduct_succ_and_pos_and_le_one
   qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity
   rademacher_kloosterman_subleading_channel_exponential_suppression_gap)

/-- Finite Euler partition generating function partial product
$Q_N(q) = \prod_{k=0}^{N-1} (1 - q^{k+1})^{-1}$. -/
noncomputable def qPartitionGeneratingPartialProduct (q : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 - q ^ (k + 1))⁻¹

/-- **Euler Partition Generating Function Partial-Product Step Recurrence, Exact Reciprocal
Cancellation $P_N(q) Q_N(q) = 1$, Lower Bound $1 \le Q_N(q)$, and Monotonicity on $0 \le q < 1$**:
For every $0 \le q < 1$ and $N \in \mathbb{N}$:
1. $Q_{N+1}(q) = Q_N(q) (1 - q^{N+1})^{-1}$;
2. $P_N(q) Q_N(q) = 1$;
3. $Q_N(q) = (P_N(q))^{-1}$;
4. $1 \le Q_N(q)$;
5. $Q_N(q) \le Q_{N+1}(q)$. -/
theorem qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ) :
    qPartitionGeneratingPartialProduct q (N + 1) =
        qPartitionGeneratingPartialProduct q N * (1 - q ^ (N + 1))⁻¹ ∧
      qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N = 1 ∧
      qPartitionGeneratingPartialProduct q N = (qPochhammerPartialProduct q N)⁻¹ ∧
      1 ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ qPartitionGeneratingPartialProduct q (N + 1) := by
  have hrec : ∀ M : ℕ,
      qPartitionGeneratingPartialProduct q (M + 1) =
        qPartitionGeneratingPartialProduct q M * (1 - q ^ (M + 1))⁻¹ := by
    intro M
    unfold qPartitionGeneratingPartialProduct
    exact Finset.prod_range_succ (fun k => (1 - q ^ (k + 1))⁻¹) M
  have hprod_one : ∀ M : ℕ,
      qPochhammerPartialProduct q M * qPartitionGeneratingPartialProduct q M = 1 := by
    intro M
    unfold qPochhammerPartialProduct qPartitionGeneratingPartialProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    have hpow_lt : q ^ (k + 1) < 1 := pow_lt_one₀ hq_nn hq_lt (Nat.succ_ne_zero k)
    have hfac_ne : 1 - q ^ (k + 1) ≠ 0 := ne_of_gt (sub_pos.mpr hpow_lt)
    exact mul_inv_cancel₀ hfac_ne
  have hP := qPochhammerPartialProduct_succ_and_pos_and_le_one q hq_nn hq_lt N
  have hP_ne : qPochhammerPartialProduct q N ≠ 0 := ne_of_gt hP.2.1
  have heq_inv : qPartitionGeneratingPartialProduct q N = (qPochhammerPartialProduct q N)⁻¹ := by
    calc
      qPartitionGeneratingPartialProduct q N
        = (qPochhammerPartialProduct q N)⁻¹ *
            (qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N) := by
          rw [← mul_assoc, inv_mul_cancel₀ hP_ne, one_mul]
      _ = (qPochhammerPartialProduct q N)⁻¹ := by
          rw [hprod_one N, mul_one]
  have hQ_pos : 0 < qPartitionGeneratingPartialProduct q N := by
    rw [heq_inv]
    exact inv_pos.mpr hP.2.1
  have h1_le_Q : 1 ≤ qPartitionGeneratingPartialProduct q N := by
    have hmul := mul_le_mul_of_nonneg_right hP.2.2.1 (le_of_lt hQ_pos)
    linarith [hprod_one N]
  have hmono :
      qPartitionGeneratingPartialProduct q N ≤ qPartitionGeneratingPartialProduct q (N + 1) := by
    rw [hrec N]
    have hpow_nn : 0 ≤ q ^ (N + 1) := pow_nonneg hq_nn (N + 1)
    have hpow_lt : q ^ (N + 1) < 1 := pow_lt_one₀ hq_nn hq_lt (Nat.succ_ne_zero N)
    have hfac_pos : 0 < 1 - q ^ (N + 1) := sub_pos.mpr hpow_lt
    have hfac_ne : 1 - q ^ (N + 1) ≠ 0 := ne_of_gt hfac_pos
    have hfac_le_one : 1 - q ^ (N + 1) ≤ 1 := by linarith
    have hinv_pos : 0 < (1 - q ^ (N + 1))⁻¹ := inv_pos.mpr hfac_pos
    have h1_le_inv : 1 ≤ (1 - q ^ (N + 1))⁻¹ := by
      have hm := mul_le_mul_of_nonneg_right hfac_le_one (le_of_lt hinv_pos)
      have hc : (1 - q ^ (N + 1)) * (1 - q ^ (N + 1))⁻¹ = 1 := mul_inv_cancel₀ hfac_ne
      linarith
    have hmQ := mul_le_mul_of_nonneg_left h1_le_inv (le_of_lt hQ_pos)
    linarith
  exact ⟨hrec N, hprod_one N, heq_inv, h1_le_Q, hmono⟩

/-- **Analytic Two-Sided Bounds for the Euler Partition Generating Function Partial Product $Q_N(q)$
on $0 \le q < 1/2$**:
For every $0 \le q < 1/2$ and $N \in \mathbb{N}$:
1. $2 - P_N(q) \le 1 + \sum_{k=0}^{N-1} q^{k+1}$;
2. $2 - P_N(q) \le Q_N(q)$;
3. $1 + \sum_{k=0}^{N-1} q^{k+1} \le Q_N(q)$;
4. $Q_N(q) \le \frac{1 - q}{1 - 2q}$;
5. $Q_N(q) - 1 \le \frac{q}{1 - 2q}$. -/
theorem qPartitionGeneratingPartialProduct_lower_and_upper_bounds
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ) :
    2 - qPochhammerPartialProduct q N ≤ 1 + qGeometricPartialSum q N ∧
      2 - qPochhammerPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N ∧
      1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      qPartitionGeneratingPartialProduct q N - 1 ≤ q / (1 - 2 * q) := by
  have hq_lt1 : q < 1 := by linarith
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation q hq_nn hq_lt1 N
  have hW := qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity
    q hq_nn hq_lt1 N
  have h1pS : 2 - qPochhammerPartialProduct q N ≤ 1 + qGeometricPartialSum q N := by
    linarith [hW.1]
  have hQ_nn : 0 ≤ qPartitionGeneratingPartialProduct q N := by linarith [hQ.2.2.2.1]
  have hsq :
      (2 - qPochhammerPartialProduct q N) * qPochhammerPartialProduct q N ≤
        qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N := by
    rw [hQ.2.1]
    have hnonneg : 0 ≤ (1 - qPochhammerPartialProduct q N) ^ 2 := sq_nonneg _
    nlinarith
  have h2mP : 2 - qPochhammerPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N := by
    have hmul := mul_le_mul_of_nonneg_right hsq hQ_nn
    have h1 :
        (2 - qPochhammerPartialProduct q N) * qPochhammerPartialProduct q N *
            qPartitionGeneratingPartialProduct q N =
          2 - qPochhammerPartialProduct q N := by
      rw [mul_assoc, hQ.2.1, mul_one]
    have h2 :
        (qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N) *
            qPartitionGeneratingPartialProduct q N =
          qPartitionGeneratingPartialProduct q N := by
      rw [hQ.2.1, one_mul]
    linarith
  have hlow_all : ∀ M : ℕ,
      1 + qGeometricPartialSum q M ≤ qPartitionGeneratingPartialProduct q M := by
    intro M
    induction M with
    | zero =>
      unfold qGeometricPartialSum qPartitionGeneratingPartialProduct
      simp
    | succ M ih =>
      have hS_succ : qGeometricPartialSum q (M + 1) = qGeometricPartialSum q M + q ^ (M + 1) := by
        unfold qGeometricPartialSum
        exact Finset.sum_range_succ (fun k => q ^ (k + 1)) M
      have hQ_succ := (qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
        q hq_nn hq_lt1 M).1
      have hS_nn : 0 ≤ qGeometricPartialSum q M := by
        unfold qGeometricPartialSum
        exact Finset.sum_nonneg (fun k _ => pow_nonneg hq_nn (k + 1))
      have hpow_nn : 0 ≤ q ^ (M + 1) := pow_nonneg hq_nn (M + 1)
      have hpow_lt : q ^ (M + 1) < 1 := pow_lt_one₀ hq_nn hq_lt1 (Nat.succ_ne_zero M)
      have hfac_pos : 0 < 1 - q ^ (M + 1) := sub_pos.mpr hpow_lt
      have hfac_ne : 1 - q ^ (M + 1) ≠ 0 := ne_of_gt hfac_pos
      have hinv_nn : 0 ≤ (1 - q ^ (M + 1))⁻¹ := le_of_lt (inv_pos.mpr hfac_pos)
      have h1pq_le_inv : 1 + q ^ (M + 1) ≤ (1 - q ^ (M + 1))⁻¹ := by
        have hsq_nn : 0 ≤ (q ^ (M + 1)) ^ 2 := sq_nonneg _
        have hprod_le : (1 + q ^ (M + 1)) * (1 - q ^ (M + 1)) ≤ 1 := by nlinarith
        have hmul_inv := mul_le_mul_of_nonneg_right hprod_le hinv_nn
        have h1 : (1 + q ^ (M + 1)) * (1 - q ^ (M + 1)) * (1 - q ^ (M + 1))⁻¹ = 1 + q ^ (M + 1) := by
          rw [mul_assoc, mul_inv_cancel₀ hfac_ne, mul_one]
        linarith
      have hprod_step :
          1 + qGeometricPartialSum q (M + 1) ≤
            (1 + qGeometricPartialSum q M) * (1 + q ^ (M + 1)) := by
        rw [hS_succ]
        have hmul_nn : 0 ≤ qGeometricPartialSum q M * q ^ (M + 1) := mul_nonneg hS_nn hpow_nn
        linarith
      have hmul_ih :
          (1 + qGeometricPartialSum q M) * (1 + q ^ (M + 1)) ≤
            qPartitionGeneratingPartialProduct q M * (1 - q ^ (M + 1))⁻¹ :=
        mul_le_mul ih h1pq_le_inv (by linarith) (by linarith)
      rw [hQ_succ]
      exact hprod_step.trans hmul_ih
  have hlow : 1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N := hlow_all N
  have h1mq_pos : 0 < 1 - q := by linarith
  have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq_pos
  have h1m2q_pos : 0 < 1 - 2 * q := by linarith
  have h1m2q_ne : 1 - 2 * q ≠ 0 := ne_of_gt h1m2q_pos
  have hmul_W := mul_le_mul_of_nonneg_right hW.2.2.2.2 hQ_nn
  rw [hQ.2.1] at hmul_W
  have hup : qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) := by
    rw [le_div_iff₀ h1m2q_pos]
    have hmul2 := mul_le_mul_of_nonneg_right hmul_W (le_of_lt h1mq_pos)
    have hsimp :
        (1 - 2 * q) / (1 - q) * qPartitionGeneratingPartialProduct q N * (1 - q) =
          qPartitionGeneratingPartialProduct q N * (1 - 2 * q) := by
      field_simp [h1mq_ne]
    linarith
  have hsub : qPartitionGeneratingPartialProduct q N - 1 ≤ q / (1 - 2 * q) := by
    have halg : (1 - q) / (1 - 2 * q) - 1 = q / (1 - 2 * q) := by
      rw [div_sub_one h1m2q_ne]
      ring
    linarith
  exact ⟨h1pS, h2mP, hlow, hup, hsub⟩

/-- **Two-Channel Rademacher-Kloosterman Subleading Hierarchy and Relative Suppression Gap**:
For all $C_{\mathrm{eff}} \ge 0$, $\Delta \ge 0$, and Kloosterman moduli $2 \le c_1 \le c_2$:
1. $S_{\mathrm{BH}}/c_2 \le S_{\mathrm{BH}}/c_1$;
2. $S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2 = \frac{c_2 - c_1}{c_1 c_2} S_{\mathrm{BH}}$;
3. $(S_{\mathrm{BH}} - S_{\mathrm{BH}}/c_2) - (S_{\mathrm{BH}} - S_{\mathrm{BH}}/c_1) =
   \frac{c_2 - c_1}{c_1 c_2} S_{\mathrm{BH}}$;
4. $S_{\mathrm{BH}} - S_{\mathrm{BH}}/c_1 \le S_{\mathrm{BH}} - S_{\mathrm{BH}}/c_2$;
5. $0 \le S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2$. -/
theorem rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ)
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) :
    rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      (rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) -
        (rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₁) =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₁ ≤
        rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ ∧
      0 ≤ rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ := by
  have _ := mul_nonneg hC hΔ
  have hS_nn : 0 ≤ rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherCardyMinimalEntropy
    positivity
  have hc₁_real : (2 : ℝ) ≤ (c₁ : ℝ) := by exact_mod_cast hc₁
  have hc₁₂_real : (c₁ : ℝ) ≤ (c₂ : ℝ) := by exact_mod_cast hc₁₂
  have hc₁_pos : (0 : ℝ) < (c₁ : ℝ) := by linarith
  have hc₂_pos : (0 : ℝ) < (c₂ : ℝ) := by linarith
  have hc₁_ne : (c₁ : ℝ) ≠ 0 := ne_of_gt hc₁_pos
  have hc₂_ne : (c₂ : ℝ) ≠ 0 := ne_of_gt hc₂_pos
  have hmono :
      rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ := by
    unfold rademacherKloostermanChannelExponent
    exact div_le_div_of_nonneg_left hS_nn hc₁_pos hc₁₂_real
  have hdiff :
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherKloostermanChannelExponent
    field_simp [hc₁_ne, hc₂_ne]
  have hgap_diff :
      (rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) -
        (rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₁) =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ := by
    linarith [hdiff]
  have hgap_mono :
      rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₁ ≤
        rademacherCardyMinimalEntropy C_eff Δ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ := by
    linarith [hmono]
  have hdiff_nn :
      0 ≤ rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ := by
    linarith [hmono]
  exact ⟨hmono, hdiff, hgap_diff, hgap_mono, hdiff_nn⟩

/-- **Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Reciprocal Partition Cancellation and
Two-Sided Euler Generating Function Bounds**:
Under `qfac = qfac_N * qfac_tail` and `qinv_N * qfac_N = 1`, multiplying `mtc0ClearedDifference`
and `mtc1ClearedDifference` by `qinv_N` cancels the finite `(q; q)_N` factor, while the real
partition generating partial product `qPartitionGeneratingPartialProduct q N` satisfies
$P_N(q) Q_N(q) = 1$ and $1 + S_N(q) \le Q_N(q) \le \frac{1 - q}{1 - 2q}$ on $0 \le q < 1/2$. -/
theorem mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman
    {R_q : Type*} [CommRing R_q]
    (X qfac qfac_N qinv_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 : R_q)
    (hqfac_split : qfac = qfac_N * qfac_tail)
    (hqinv : qinv_N * qfac_N = 1)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ) :
    qinv_N * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_tail * (f0 + 2 * (Phi1 - 1)) - qinv_N * (J5_10 * J2_5) ∧
      qinv_N * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_tail * (X * f1 + 2 * (Phi2 - 1)) - qinv_N * (X * (J5_10 * J1_5)) ∧
      qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N = 1 ∧
      1 + qGeometricPartialSum q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N ≤ (1 - q) / (1 - 2 * q) ∧
      qPartitionGeneratingPartialProduct q N - 1 ≤ q / (1 - 2 * q) := by
  have h0 :
      qinv_N * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_tail * (f0 + 2 * (Phi1 - 1)) - qinv_N * (J5_10 * J2_5) := by
    unfold mtc0ClearedDifference
    linear_combination (qfac_tail * (f0 + 2 * (Phi1 - 1))) * hqinv +
      (qinv_N * (f0 + 2 * (Phi1 - 1))) * hqfac_split
  have h1 :
      qinv_N * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_tail * (X * f1 + 2 * (Phi2 - 1)) - qinv_N * (X * (J5_10 * J1_5)) := by
    unfold mtc1ClearedDifference
    linear_combination (qfac_tail * (X * f1 + 2 * (Phi2 - 1))) * hqinv +
      (qinv_N * (X * f1 + 2 * (Phi2 - 1))) * hqfac_split
  have hq_lt1 : q < 1 := by linarith
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation q hq_nn hq_lt1 N
  have hB := qPartitionGeneratingPartialProduct_lower_and_upper_bounds q hq_nn hq_half N
  exact ⟨h0, h1, hQ.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2⟩

/-- Quantum-channel Six-Vector Orthogonality Certificate ($(\det M)^2 = 1$ and $3 \times 3$ Gram
determinant conservation) paired with fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term factorizations, Euler partition generating function reciprocal bounds, and the
two-channel Rademacher-Kloosterman subleading hierarchy. -/
theorem multiChannel_sixVectorOrthogonality_with_eulerPartitionReciprocal_and_kloostermanTwoChannelHierarchy
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
    (X qfac f0 f1 Phi1 Phi2 B0_lead B0_tail B1_lead B1_tail J5_10 J2_5 J1_5 P1_5 P4_5 P2_5 P3_5 : R_q)
    (hqfac0 : qfac = J2_5 * (P1_5 * P4_5))
    (hPhi1 : Phi1 - 1 = B0_lead + B0_tail)
    (hqfac1 : qfac = J1_5 * (P2_5 * P3_5))
    (hPhi2 : Phi2 - 1 = B1_lead + B1_tail)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ)
    (c₁ c₂ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂)
    (x : E) :
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
      rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂ =
        (((c₂ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₂ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ := by
  intro u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hmtc0 := mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 hqfac0 hPhi1
  have hmtc1 := mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 hqfac1 hPhi2
  have hq_lt1 : q < 1 := by linarith
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation q hq_nn hq_lt1 N
  have hB := qPartitionGeneratingPartialProduct_lower_and_upper_bounds q hq_nn hq_half N
  have hK2 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₁ c₂ hc₁ hc₁₂
  exact ⟨horth.2.2.1, horth.2.2.2, hmtc0.1, hmtc1.1, hQ.2.1, hB.2.2.1, hB.2.2.2.1,
    hK2.1, hK2.2.1⟩

/-- Master synthesis uniting the Euler partition generating function reciprocal partial-product
bounds $1 + S_N(q) \le Q_N(q) \le \frac{1-q}{1-2q}$, exact reciprocal cancellation
$P_N(q) Q_N(q) = 1$, two-channel Rademacher-Kloosterman subleading hierarchy
$S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2 = \frac{c_2 - c_1}{c_1 c_2} S_{\mathrm{BH}} \ge 0$,
Rademacher-Cardy saddle-point quadratic completion, fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`)
bilateral constant-term factorizations, five-fold Euler residue-partition splitting, short
projective-root `p = 71` Householder reflection isometry, octahedral-to-Legendre elliptic
$j$-invariant identity, and quantum-channel $3 \times 3$ Gram determinant conservation. -/
theorem multiChannel_eulerPartitionReciprocal_and_kloosterman_twoChannel_hierarchy_master_synthesis
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
    (x : E) :
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
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro u₁ u₂ u₃
  have h5split := mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2 hq5 hJ2 hJ1
  have hmain := multiChannel_sixVectorOrthogonality_with_eulerPartitionReciprocal_and_kloostermanTwoChannelHierarchy
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac f0 f1 Phi1 Phi2 B0_lead B0_tail B1_lead B1_tail J5_10 J2_5 J1_5 P1_5 P4_5 P2_5 P3_5
    h5split.1 hPhi1 h5split.2.1 hPhi2 q hq_nn hq_half N C_eff Δ hC hΔ c₁ c₂ hc₁ hc₁₂ x
  have hcardy := rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    C_eff Δ β hC hΔ hβ
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
    hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2.1, hcardy.1, hmain.2.2.2.2.2.2.2.1,
    hmain.2.2.2.2.2.2.2.2, ?_, hj.1⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

#print axioms qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
#print axioms qPartitionGeneratingPartialProduct_lower_and_upper_bounds
#print axioms rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
#print axioms mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman
#print axioms multiChannel_sixVectorOrthogonality_with_eulerPartitionReciprocal_and_kloostermanTwoChannelHierarchy
#print axioms multiChannel_eulerPartitionReciprocal_and_kloosterman_twoChannel_hierarchy_master_synthesis

end KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy
end Audit
end UnifiedTheory
