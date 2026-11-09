/- Arbitrary-Source Multi-Channel Euler Distinct-Parts (Fermionic) Partition Partial Product
$D_N(q) = \prod_{k=0}^{N-1} (1 + q^{k+1})$, Exact Bosonic-Fermionic Partial-Product Identities
$P_N(q) D_N(q) = P_N(q^2)$ and $D_N(q) = P_N(q^2) Q_N(q)$, Pauli Exclusion / Distinct-vs-Unrestricted
Partition Sandwich Bounds $1 + \sum_{k=0}^{N-1} q^{k+1} \le D_N(q) \le Q_N(q) \le \frac{1 - q}{1 - 2q}$
and Bosonic-Fermionic Excess $Q_N(q) - D_N(q) = (1 - P_N(q^2)) Q_N(q) \ge 0$ on $0 \le q < 1/2$,
Three-Channel Rademacher-Kloosterman Subleading Telescoping Cocycle
$(S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2) + (S_{\mathrm{BH}}/c_2 - S_{\mathrm{BH}}/c_3) =
S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_3 = \frac{c_3 - c_1}{c_1 c_3} S_{\mathrm{BH}} \ge 0$ for
$2 \le c_1 \le c_2 \le c_3$, Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Fermionic Partition
Multiplier Identities, and Quantum-Channel $3 \times 3$ Gram Determinant Synthesis. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalArbitrarySourceMultiChannelEulerDistinctPartitionBosonicFermionicIdentityAndKloostermanThreeChannelCocycle

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
   qPochhammerPartialProduct_succ_and_pos_and_le_one)
open KFCausalArbitrarySourceMultiChannelEulerPartitionReciprocalBoundsAndKloostermanTwoChannelHierarchy
  (qPartitionGeneratingPartialProduct
   qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
   qPartitionGeneratingPartialProduct_lower_and_upper_bounds
   rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
   mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman)

/-- Finite Euler distinct-parts (fermionic) partition partial product
$D_N(q) = \prod_{k=0}^{N-1} (1 + q^{k+1})$. -/
noncomputable def eulerDistinctPartitionPartialProduct (q : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 + q ^ (k + 1))

/-- **Euler Distinct-Parts (Fermionic) Partition Partial-Product Step Recurrence, Exact
Bosonic-Fermionic Partial-Product Identities $P_N(q) D_N(q) = P_N(q^2)$ and
$D_N(q) = P_N(q^2) Q_N(q)$, Lower Bound $1 \le D_N(q)$, and Monotonicity on $0 \le q < 1$**:
For every $0 \le q < 1$ and $N \in \mathbb{N}$:
1. $D_{N+1}(q) = D_N(q) (1 + q^{N+1})$;
2. $P_N(q) D_N(q) = P_N(q^2)$;
3. $D_N(q) = P_N(q^2) Q_N(q)$;
4. $1 \le D_N(q)$;
5. $D_N(q) \le D_{N+1}(q)$. -/
theorem eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ) :
    eulerDistinctPartitionPartialProduct q (N + 1) =
        eulerDistinctPartitionPartialProduct q N * (1 + q ^ (N + 1)) ∧
      qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N ∧
      eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N * qPartitionGeneratingPartialProduct q N ∧
      1 ≤ eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ eulerDistinctPartitionPartialProduct q (N + 1) := by
  have hrec : ∀ M : ℕ,
      eulerDistinctPartitionPartialProduct q (M + 1) =
        eulerDistinctPartitionPartialProduct q M * (1 + q ^ (M + 1)) := by
    intro M
    unfold eulerDistinctPartitionPartialProduct
    exact Finset.prod_range_succ (fun k => 1 + q ^ (k + 1)) M
  have hprod_sq :
      qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N := by
    unfold qPochhammerPartialProduct eulerDistinctPartitionPartialProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    rw [pow_right_comm q 2 (k + 1)]
    ring
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation q hq_nn hq_lt N
  have hD_eq :
      eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N * qPartitionGeneratingPartialProduct q N := by
    calc
      eulerDistinctPartitionPartialProduct q N
        = eulerDistinctPartitionPartialProduct q N *
            (qPochhammerPartialProduct q N * qPartitionGeneratingPartialProduct q N) := by
          rw [hQ.2.1, mul_one]
      _ = (qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N) *
            qPartitionGeneratingPartialProduct q N := by ring
      _ = qPochhammerPartialProduct (q ^ 2) N * qPartitionGeneratingPartialProduct q N := by
          rw [hprod_sq]
  have h1_le_all : ∀ M : ℕ, 1 ≤ eulerDistinctPartitionPartialProduct q M := by
    intro M
    induction M with
    | zero =>
      unfold eulerDistinctPartitionPartialProduct
      simp
    | succ M ih =>
      rw [hrec M]
      have hpow_nn : 0 ≤ q ^ (M + 1) := pow_nonneg hq_nn (M + 1)
      nlinarith
  have h1_le : 1 ≤ eulerDistinctPartitionPartialProduct q N := h1_le_all N
  have hmono :
      eulerDistinctPartitionPartialProduct q N ≤
        eulerDistinctPartitionPartialProduct q (N + 1) := by
    rw [hrec N]
    have hpow_nn : 0 ≤ q ^ (N + 1) := pow_nonneg hq_nn (N + 1)
    nlinarith
  exact ⟨hrec N, hprod_sq, hD_eq, h1_le, hmono⟩

/-- **Pauli Exclusion / Distinct-vs-Unrestricted Partition Sandwich Bounds and Exact
Bosonic-Fermionic Excess Identity on $0 \le q < 1/2$**:
For every $0 \le q < 1/2$ and $N \in \mathbb{N}$:
1. $1 + \sum_{k=0}^{N-1} q^{k+1} \le D_N(q)$;
2. $D_N(q) \le Q_N(q)$;
3. $Q_N(q) - D_N(q) = (1 - P_N(q^2)) Q_N(q)$;
4. $0 \le Q_N(q) - D_N(q)$;
5. $D_N(q) \le \frac{1 - q}{1 - 2q}$. -/
theorem eulerDistinctPartitionPartialProduct_pauli_sandwich_and_bosonic_excess_bounds
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ) :
    1 + qGeometricPartialSum q N ≤ eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N ∧
      qPartitionGeneratingPartialProduct q N - eulerDistinctPartitionPartialProduct q N =
        (1 - qPochhammerPartialProduct (q ^ 2) N) * qPartitionGeneratingPartialProduct q N ∧
      0 ≤ qPartitionGeneratingPartialProduct q N - eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ (1 - q) / (1 - 2 * q) := by
  have hq_lt1 : q < 1 := by linarith
  have hq2_nn : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2_lt1 : q ^ 2 < 1 := by nlinarith
  have hD := eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
    q hq_nn hq_lt1 N
  have hQ := qPartitionGeneratingPartialProduct_succ_and_reciprocal_cancellation
    q hq_nn hq_lt1 N
  have hP2 := qPochhammerPartialProduct_succ_and_pos_and_le_one (q ^ 2) hq2_nn hq2_lt1 N
  have hB := qPartitionGeneratingPartialProduct_lower_and_upper_bounds q hq_nn hq_half N
  have hlow_all : ∀ M : ℕ,
      1 + qGeometricPartialSum q M ≤ eulerDistinctPartitionPartialProduct q M := by
    intro M
    induction M with
    | zero =>
      unfold qGeometricPartialSum eulerDistinctPartitionPartialProduct
      simp
    | succ M ih =>
      have hS_succ : qGeometricPartialSum q (M + 1) = qGeometricPartialSum q M + q ^ (M + 1) := by
        unfold qGeometricPartialSum
        exact Finset.sum_range_succ (fun k => q ^ (k + 1)) M
      have hD_succ := (eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
        q hq_nn hq_lt1 M).1
      have hS_nn : 0 ≤ qGeometricPartialSum q M := by
        unfold qGeometricPartialSum
        exact Finset.sum_nonneg (fun k _ => pow_nonneg hq_nn (k + 1))
      have hpow_nn : 0 ≤ q ^ (M + 1) := pow_nonneg hq_nn (M + 1)
      have hprod_step :
          1 + qGeometricPartialSum q (M + 1) ≤
            (1 + qGeometricPartialSum q M) * (1 + q ^ (M + 1)) := by
        rw [hS_succ]
        have hmul_nn : 0 ≤ qGeometricPartialSum q M * q ^ (M + 1) := mul_nonneg hS_nn hpow_nn
        linarith
      have hmul_ih :
          (1 + qGeometricPartialSum q M) * (1 + q ^ (M + 1)) ≤
            eulerDistinctPartitionPartialProduct q M * (1 + q ^ (M + 1)) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      rw [hD_succ]
      exact hprod_step.trans hmul_ih
  have hlow : 1 + qGeometricPartialSum q N ≤ eulerDistinctPartitionPartialProduct q N :=
    hlow_all N
  have hQ_nn : 0 ≤ qPartitionGeneratingPartialProduct q N := by linarith [hQ.2.2.2.1]
  have hexcess :
      qPartitionGeneratingPartialProduct q N - eulerDistinctPartitionPartialProduct q N =
        (1 - qPochhammerPartialProduct (q ^ 2) N) * qPartitionGeneratingPartialProduct q N := by
    rw [hD.2.2.1]
    ring
  have hexcess_nn :
      0 ≤ qPartitionGeneratingPartialProduct q N - eulerDistinctPartitionPartialProduct q N := by
    rw [hexcess]
    exact mul_nonneg (by linarith [hP2.2.2.1]) hQ_nn
  have hD_le_Q : eulerDistinctPartitionPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N := by
    linarith
  have hD_up : eulerDistinctPartitionPartialProduct q N ≤ (1 - q) / (1 - 2 * q) :=
    hD_le_Q.trans hB.2.2.2.1
  exact ⟨hlow, hD_le_Q, hexcess, hexcess_nn, hD_up⟩

/-- **Three-Channel Rademacher-Kloosterman Subleading Telescoping Cocycle and Ordered Hierarchy**:
For all $C_{\mathrm{eff}} \ge 0$, $\Delta \ge 0$, and Kloosterman moduli $2 \le c_1 \le c_2 \le c_3$:
1. $S_{\mathrm{BH}}/c_3 \le S_{\mathrm{BH}}/c_2$ and $S_{\mathrm{BH}}/c_2 \le S_{\mathrm{BH}}/c_1$;
2. $(S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2) + (S_{\mathrm{BH}}/c_2 - S_{\mathrm{BH}}/c_3) =
   S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_3$;
3. $S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_3 = \frac{c_3 - c_1}{c_1 c_3} S_{\mathrm{BH}}$;
4. $0 \le S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_2$ and $0 \le S_{\mathrm{BH}}/c_2 - S_{\mathrm{BH}}/c_3$
   and $0 \le S_{\mathrm{BH}}/c_1 - S_{\mathrm{BH}}/c_3$. -/
theorem rademacher_kloosterman_three_channel_cocycle_and_ordered_hierarchy
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ)
    (c₁ c₂ c₃ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂₃ : c₂ ≤ c₃) :
    rademacherKloostermanChannelExponent C_eff Δ c₃ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₂ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₂ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      (rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) +
        (rademacherKloostermanChannelExponent C_eff Δ c₂ -
          rademacherKloostermanChannelExponent C_eff Δ c₃) =
        rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₃ ∧
      rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₃ =
        (((c₃ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₃ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      0 ≤ rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₃ := by
  have hc₂ : 2 ≤ c₂ := le_trans hc₁ hc₁₂
  have hc₁₃ : c₁ ≤ c₃ := le_trans hc₁₂ hc₂₃
  have h12 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₁ c₂ hc₁ hc₁₂
  have h23 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₂ c₃ hc₂ hc₂₃
  have h13 := rademacher_kloosterman_two_channel_hierarchy_and_relative_suppression
    C_eff Δ hC hΔ c₁ c₃ hc₁ hc₁₃
  refine ⟨h23.1, h12.1, ?_, h13.2.1, h13.2.2.2.2⟩
  ring

/-- **Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Fermionic Partition Multiplier Identity and
Three-Channel Kloosterman Cocycle**:
Combines the reciprocal partition cancellation of `mtc0ClearedDifference` and `mtc1ClearedDifference`
with the Euler bosonic-fermionic partial-product identities $P_N(q) D_N(q) = P_N(q^2)$ and
$D_N(q) = P_N(q^2) Q_N(q)$, the Pauli exclusion sandwich bounds $1 + S_N(q) \le D_N(q) \le Q_N(q)$,
and the three-channel Rademacher-Kloosterman subleading cocycle. -/
theorem mockTheta_distinct_partition_multiplier_identity_and_three_channel_kloosterman
    {R_q : Type*} [CommRing R_q]
    (X qfac qfac_N qinv_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 : R_q)
    (hqfac_split : qfac = qfac_N * qfac_tail)
    (hqinv : qinv_N * qfac_N = 1)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_half : q < 1 / 2) (N : ℕ)
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ)
    (c₁ c₂ c₃ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂₃ : c₂ ≤ c₃) :
    qinv_N * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_tail * (f0 + 2 * (Phi1 - 1)) - qinv_N * (J5_10 * J2_5) ∧
      qinv_N * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_tail * (X * f1 + 2 * (Phi2 - 1)) - qinv_N * (X * (J5_10 * J1_5)) ∧
      qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N ∧
      eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N * qPartitionGeneratingPartialProduct q N ∧
      1 + qGeometricPartialSum q N ≤ eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N ∧
      (rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) +
        (rademacherKloostermanChannelExponent C_eff Δ c₂ -
          rademacherKloostermanChannelExponent C_eff Δ c₃) =
        (((c₃ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₃ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ := by
  have hq_lt1 : q < 1 := by linarith
  have hrec := mockTheta_reciprocal_partition_multiplier_cancellation_and_two_channel_kloosterman
    X qfac qfac_N qinv_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 hqfac_split hqinv q hq_nn hq_half N
  have hD := eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
    q hq_nn hq_lt1 N
  have hS := eulerDistinctPartitionPartialProduct_pauli_sandwich_and_bosonic_excess_bounds
    q hq_nn hq_half N
  have hK3 := rademacher_kloosterman_three_channel_cocycle_and_ordered_hierarchy
    C_eff Δ hC hΔ c₁ c₂ c₃ hc₁ hc₁₂ hc₂₃
  exact ⟨hrec.1, hrec.2.1, hD.2.1, hD.2.2.1, hS.1, hS.2.1, hK3.2.2.1.trans hK3.2.2.2.1⟩

/-- Quantum-channel Six-Vector Orthogonality Certificate ($(\det M)^2 = 1$ and $3 \times 3$ Gram
determinant conservation) paired with fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term factorizations, Euler bosonic-fermionic distinct-partition identities and Pauli
sandwich bounds, and the three-channel Rademacher-Kloosterman subleading cocycle. -/
theorem multiChannel_sixVectorOrthogonality_with_eulerDistinctPartition_and_kloostermanThreeChannelCocycle
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
    (c₁ c₂ c₃ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂₃ : c₂ ≤ c₃)
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
      qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N ∧
      1 + qGeometricPartialSum q N ≤ eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N ∧
      rademacherKloostermanChannelExponent C_eff Δ c₃ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      (rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) +
        (rademacherKloostermanChannelExponent C_eff Δ c₂ -
          rademacherKloostermanChannelExponent C_eff Δ c₃) =
        (((c₃ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₃ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ := by
  intro u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hmtc0 := mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 hqfac0 hPhi1
  have hmtc1 := mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 hqfac1 hPhi2
  have hq_lt1 : q < 1 := by linarith
  have hD := eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
    q hq_nn hq_lt1 N
  have hS := eulerDistinctPartitionPartialProduct_pauli_sandwich_and_bosonic_excess_bounds
    q hq_nn hq_half N
  have hK3 := rademacher_kloosterman_three_channel_cocycle_and_ordered_hierarchy
    C_eff Δ hC hΔ c₁ c₂ c₃ hc₁ hc₁₂ hc₂₃
  exact ⟨horth.2.2.1, horth.2.2.2, hmtc0.1, hmtc1.1, hD.2.1, hS.1, hS.2.1,
    hK3.1.trans hK3.2.1, hK3.2.2.1.trans hK3.2.2.2.1⟩

/-- Master synthesis uniting the Euler distinct-parts (fermionic) partition partial product
$D_N(q) = \prod_{k=0}^{N-1} (1 + q^{k+1})$, exact bosonic-fermionic partial-product identities
$P_N(q) D_N(q) = P_N(q^2)$ and $D_N(q) = P_N(q^2) Q_N(q)$, Pauli exclusion sandwich bounds
$1 + S_N(q) \le D_N(q) \le Q_N(q) \le \frac{1-q}{1-2q}$, three-channel Rademacher-Kloosterman
subleading telescoping cocycle, Rademacher-Cardy saddle-point quadratic completion, fifth-order
Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral constant-term factorizations, short projective-root
`p = 71` Householder reflection isometry, octahedral-to-Legendre elliptic $j$-invariant identity,
and quantum-channel $3 \times 3$ Gram determinant conservation. -/
theorem multiChannel_eulerDistinctPartition_and_kloosterman_threeChannel_cocycle_master_synthesis
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
    (c₁ c₂ c₃ : ℕ) (hc₁ : 2 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂₃ : c₂ ≤ c₃)
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
      qPochhammerPartialProduct q N * eulerDistinctPartitionPartialProduct q N =
        qPochhammerPartialProduct (q ^ 2) N ∧
      1 + qGeometricPartialSum q N ≤ eulerDistinctPartitionPartialProduct q N ∧
      eulerDistinctPartitionPartialProduct q N ≤ qPartitionGeneratingPartialProduct q N ∧
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherKloostermanChannelExponent C_eff Δ c₃ ≤
        rademacherKloostermanChannelExponent C_eff Δ c₁ ∧
      (rademacherKloostermanChannelExponent C_eff Δ c₁ -
          rademacherKloostermanChannelExponent C_eff Δ c₂) +
        (rademacherKloostermanChannelExponent C_eff Δ c₂ -
          rademacherKloostermanChannelExponent C_eff Δ c₃) =
        (((c₃ : ℝ) - (c₁ : ℝ)) / ((c₁ : ℝ) * (c₃ : ℝ))) *
          rademacherCardyMinimalEntropy C_eff Δ ∧
      reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
        (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro u₁ u₂ u₃
  have h5split := mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2 hq5 hJ2 hJ1
  have hmain := multiChannel_sixVectorOrthogonality_with_eulerDistinctPartition_and_kloostermanThreeChannelCocycle
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac f0 f1 Phi1 Phi2 B0_lead B0_tail B1_lead B1_tail J5_10 J2_5 J1_5 P1_5 P4_5 P2_5 P3_5
    h5split.1 hPhi1 h5split.2.1 hPhi2 q hq_nn hq_half N C_eff Δ hC hΔ c₁ c₂ c₃ hc₁ hc₁₂ hc₂₃ x
  have hcardy := rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    C_eff Δ β hC hΔ hβ
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
    hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2.1, hcardy.1, hmain.2.2.2.2.2.2.2.1,
    hmain.2.2.2.2.2.2.2.2, ?_, hj.1⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

#print axioms eulerDistinctPartitionPartialProduct_succ_and_bosonic_fermionic_identity
#print axioms eulerDistinctPartitionPartialProduct_pauli_sandwich_and_bosonic_excess_bounds
#print axioms rademacher_kloosterman_three_channel_cocycle_and_ordered_hierarchy
#print axioms mockTheta_distinct_partition_multiplier_identity_and_three_channel_kloosterman
#print axioms multiChannel_sixVectorOrthogonality_with_eulerDistinctPartition_and_kloostermanThreeChannelCocycle
#print axioms multiChannel_eulerDistinctPartition_and_kloosterman_threeChannel_cocycle_master_synthesis

end KFCausalArbitrarySourceMultiChannelEulerDistinctPartitionBosonicFermionicIdentityAndKloostermanThreeChannelCocycle
end Audit
end UnifiedTheory
