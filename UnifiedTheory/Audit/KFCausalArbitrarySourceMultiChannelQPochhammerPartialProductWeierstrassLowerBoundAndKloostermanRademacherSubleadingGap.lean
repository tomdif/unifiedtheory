/- Arbitrary-Source Multi-Channel $q$-Pochhammer Partial-Product Weierstrass Lower Bound
$1 - \sum_{k=0}^{N-1} q^{k+1} \le \prod_{k=0}^{N-1} (1 - q^{k+1}) \le 1$, Exact Geometric Series
Telescoping & Uniform Tail Bound, Rademacher-Kloosterman Subleading $c \ge 2$ Channel Exponential
Suppression Gap $S_{\mathrm{BH}} - S_{\mathrm{BH}}/c = \frac{c-1}{c} S_{\mathrm{BH}} \ge \frac{1}{2} S_{\mathrm{BH}}$,
Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Truncation Factorization, and Quantum-Channel
$3 \times 3$ Gram Determinant Synthesis. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap

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

/-- Finite $q$-Pochhammer partial product
$P_N(q) = (q; q)_N = \prod_{k=0}^{N-1} (1 - q^{k+1})$. -/
def qPochhammerPartialProduct (q : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (1 - q ^ (k + 1))

/-- Finite geometric series partial sum
$S_N(q) = \sum_{k=0}^{N-1} q^{k+1}$. -/
def qGeometricPartialSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, q ^ (k + 1)

/-- Subleading Rademacher-Kloosterman $c$-th channel Bessel exponent
$S_{\mathrm{BH}} / c = \frac{2\pi\sqrt{2 C_{\mathrm{eff}} \Delta}}{c}$ for Kloosterman modulus $c \in \mathbb{N}$. -/
noncomputable def rademacherKloostermanChannelExponent (C_eff Δ : ℝ) (c : ℕ) : ℝ :=
  rademacherCardyMinimalEntropy C_eff Δ / (c : ℝ)

/-- **Finite $q$-Pochhammer Partial-Product Step Recurrence, Strict Positivity, Contraction, and
Monotone Antitonicity on $0 \le q < 1$**:
For every $0 \le q < 1$ and $N \in \mathbb{N}$:
1. $P_{N+1}(q) = P_N(q) (1 - q^{N+1})$;
2. $0 < P_N(q)$ and $P_N(q) \le 1$;
3. $P_{N+1}(q) \le P_N(q)$ with exact step drop $P_N(q) - P_{N+1}(q) = P_N(q) q^{N+1} \ge 0$. -/
theorem qPochhammerPartialProduct_succ_and_pos_and_le_one
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ) :
    qPochhammerPartialProduct q (N + 1) =
        qPochhammerPartialProduct q N * (1 - q ^ (N + 1)) ∧
      0 < qPochhammerPartialProduct q N ∧
      qPochhammerPartialProduct q N ≤ 1 ∧
      qPochhammerPartialProduct q (N + 1) ≤ qPochhammerPartialProduct q N ∧
      qPochhammerPartialProduct q N - qPochhammerPartialProduct q (N + 1) =
        qPochhammerPartialProduct q N * q ^ (N + 1) := by
  have hrec : ∀ M : ℕ,
      qPochhammerPartialProduct q (M + 1) =
        qPochhammerPartialProduct q M * (1 - q ^ (M + 1)) := by
    intro M
    unfold qPochhammerPartialProduct
    exact Finset.prod_range_succ (fun k => 1 - q ^ (k + 1)) M
  have hpos_le : ∀ M : ℕ,
      0 < qPochhammerPartialProduct q M ∧ qPochhammerPartialProduct q M ≤ 1 := by
    intro M
    induction M with
    | zero =>
      unfold qPochhammerPartialProduct
      simp
    | succ M ih =>
      rw [hrec M]
      have hpow_nn : 0 ≤ q ^ (M + 1) := pow_nonneg hq_nn (M + 1)
      have hpow_lt : q ^ (M + 1) < 1 := pow_lt_one₀ hq_nn hq_lt (Nat.succ_ne_zero M)
      have hfac_pos : 0 < 1 - q ^ (M + 1) := sub_pos.mpr hpow_lt
      have hfac_le : 1 - q ^ (M + 1) ≤ 1 := by linarith
      refine ⟨mul_pos ih.1 hfac_pos, ?_⟩
      exact (mul_le_of_le_one_right (le_of_lt ih.1) hfac_le).trans ih.2
  have hN := hpos_le N
  have hdrop :
      qPochhammerPartialProduct q N - qPochhammerPartialProduct q (N + 1) =
        qPochhammerPartialProduct q N * q ^ (N + 1) := by
    rw [hrec N]
    ring
  have hmono : qPochhammerPartialProduct q (N + 1) ≤ qPochhammerPartialProduct q N := by
    have hprod_nn : 0 ≤ qPochhammerPartialProduct q N * q ^ (N + 1) :=
      mul_nonneg (le_of_lt hN.1) (pow_nonneg hq_nn (N + 1))
    linarith [hdrop]
  exact ⟨hrec N, hN.1, hN.2, hmono, hdrop⟩

/-- **Weierstrass Product Inequality and Geometric Series Telescoping Lower Bound for $P_N(q)$**:
For every $0 \le q < 1$ and $N \in \mathbb{N}$:
1. Weierstrass lower bound: $1 - \sum_{k=0}^{N-1} q^{k+1} \le \prod_{k=0}^{N-1} (1 - q^{k+1})$;
2. Geometric series telescoping: $(1 - q) \sum_{k=0}^{N-1} q^{k+1} = q (1 - q^N)$;
3. Uniform geometric sum bound: $\sum_{k=0}^{N-1} q^{k+1} \le \frac{q}{1 - q}$;
4. Uniform Euler lower bound: $\frac{1 - 2q}{1 - q} = 1 - \frac{q}{1 - q} \le \prod_{k=0}^{N-1} (1 - q^{k+1})$. -/
theorem qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ) :
    1 - qGeometricPartialSum q N ≤ qPochhammerPartialProduct q N ∧
      (1 - q) * qGeometricPartialSum q N = q * (1 - q ^ N) ∧
      qGeometricPartialSum q N ≤ q / (1 - q) ∧
      1 - q / (1 - q) = (1 - 2 * q) / (1 - q) ∧
      (1 - 2 * q) / (1 - q) ≤ qPochhammerPartialProduct q N := by
  have hsum_nn : ∀ M : ℕ, 0 ≤ qGeometricPartialSum q M := by
    intro M
    unfold qGeometricPartialSum
    exact Finset.sum_nonneg (fun k _ => pow_nonneg hq_nn (k + 1))
  have hweier : ∀ M : ℕ, 1 - qGeometricPartialSum q M ≤ qPochhammerPartialProduct q M := by
    intro M
    induction M with
    | zero =>
      unfold qGeometricPartialSum qPochhammerPartialProduct
      simp
    | succ M ih =>
      have hrec_P : qPochhammerPartialProduct q (M + 1) =
          qPochhammerPartialProduct q M * (1 - q ^ (M + 1)) := by
        unfold qPochhammerPartialProduct
        exact Finset.prod_range_succ (fun k => 1 - q ^ (k + 1)) M
      have hrec_S : qGeometricPartialSum q (M + 1) =
          qGeometricPartialSum q M + q ^ (M + 1) := by
        unfold qGeometricPartialSum
        exact Finset.sum_range_succ (fun k => q ^ (k + 1)) M
      have hpow_lt : q ^ (M + 1) < 1 := pow_lt_one₀ hq_nn hq_lt (Nat.succ_ne_zero M)
      have hfac_nn : 0 ≤ 1 - q ^ (M + 1) := le_of_lt (sub_pos.mpr hpow_lt)
      have hmul := mul_le_mul_of_nonneg_right ih hfac_nn
      have hcross_nn : 0 ≤ qGeometricPartialSum q M * q ^ (M + 1) :=
        mul_nonneg (hsum_nn M) (pow_nonneg hq_nn (M + 1))
      rw [hrec_P, hrec_S]
      have hid :
          (1 - qGeometricPartialSum q M) * (1 - q ^ (M + 1)) =
            1 - (qGeometricPartialSum q M + q ^ (M + 1)) +
              qGeometricPartialSum q M * q ^ (M + 1) := by ring
      linarith
  have htele : ∀ M : ℕ, (1 - q) * qGeometricPartialSum q M = q * (1 - q ^ M) := by
    intro M
    induction M with
    | zero =>
      unfold qGeometricPartialSum
      simp
    | succ M ih =>
      have hrec_S : qGeometricPartialSum q (M + 1) =
          qGeometricPartialSum q M + q ^ (M + 1) := by
        unfold qGeometricPartialSum
        exact Finset.sum_range_succ (fun k => q ^ (k + 1)) M
      rw [hrec_S, mul_add, ih, pow_succ]
      ring
  have h1mq_pos : 0 < 1 - q := sub_pos.mpr hq_lt
  have h1mq_ne : 1 - q ≠ 0 := ne_of_gt h1mq_pos
  have hgeom_le : qGeometricPartialSum q N ≤ q / (1 - q) := by
    rw [le_div_iff₀ h1mq_pos, mul_comm, htele N]
    have hqpow_nn : 0 ≤ q * q ^ N := mul_nonneg hq_nn (pow_nonneg hq_nn N)
    linarith
  have halg : 1 - q / (1 - q) = (1 - 2 * q) / (1 - q) := by
    field_simp [h1mq_ne]
    ring
  have hunif : (1 - 2 * q) / (1 - q) ≤ qPochhammerPartialProduct q N := by
    have h1 : 1 - q / (1 - q) ≤ 1 - qGeometricPartialSum q N := by linarith [hgeom_le]
    rw [← halg]
    exact h1.trans (hweier N)
  exact ⟨hweier N, htele N, hgeom_le, halg, hunif⟩

/-- **Rademacher-Kloosterman Subleading $c \ge 2$ Channel Exponential Suppression Gap**:
For all $C_{\mathrm{eff}} \ge 0$, $\Delta \ge 0$, and every subleading Kloosterman modulus $c \ge 2$:
1. The leading $c = 1$ Rademacher exponent equals $S_{\mathrm{BH}} = 2\pi\sqrt{2 C_{\mathrm{eff}} \Delta}$;
2. Every subleading $c \ge 2$ channel exponent satisfies $S_{\mathrm{BH}}/c \le S_{\mathrm{BH}}/2$;
3. The exponential suppression gap between the leading $c = 1$ saddle and the $c$-th Kloosterman
   channel is $S_{\mathrm{BH}} - S_{\mathrm{BH}}/c = \frac{c-1}{c} S_{\mathrm{BH}} \ge \frac{1}{2} S_{\mathrm{BH}} \ge 0$. -/
theorem rademacher_kloosterman_subleading_channel_exponential_suppression_gap
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (c : ℕ) (hc : 2 ≤ c) :
    rademacherKloostermanChannelExponent C_eff Δ 1 = rademacherCardyMinimalEntropy C_eff Δ ∧
      rademacherKloostermanChannelExponent C_eff Δ c ≤ rademacherCardyMinimalEntropy C_eff Δ / 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c =
        (((c : ℝ) - 1) / (c : ℝ)) * rademacherCardyMinimalEntropy C_eff Δ ∧
      rademacherCardyMinimalEntropy C_eff Δ / 2 ≤
        rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c ∧
      0 ≤ rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c := by
  have _ := mul_nonneg hC hΔ
  have hS_nn : 0 ≤ rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherCardyMinimalEntropy
    positivity
  have hc1 : rademacherKloostermanChannelExponent C_eff Δ 1 =
      rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherKloostermanChannelExponent
    simp
  have hc_real : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hc_pos : (0 : ℝ) < (c : ℝ) := by linarith
  have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
  have hsub_le :
      rademacherKloostermanChannelExponent C_eff Δ c ≤
        rademacherCardyMinimalEntropy C_eff Δ / 2 := by
    unfold rademacherKloostermanChannelExponent
    exact div_le_div_of_nonneg_left hS_nn (by norm_num : (0 : ℝ) < 2) hc_real
  have hgap_eq :
      rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c =
        (((c : ℝ) - 1) / (c : ℝ)) * rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherKloostermanChannelExponent
    field_simp [hc_ne]
  have hgap_half :
      rademacherCardyMinimalEntropy C_eff Δ / 2 ≤
        rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c := by
    linarith [hsub_le]
  have hgap_nn :
      0 ≤ rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c := by
    linarith [hS_nn, hgap_half]
  exact ⟨hc1, hsub_le, hgap_eq, hgap_half, hgap_nn⟩

/-- **Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Finite-Truncation $q$-Pochhammer Factor
Decomposition and Weierstrass Lower Bound**:
Under the finite/tail factorization `qfac = qfac_N * qfac_tail` of `(q; q)∞ = (q; q)_N (q^{N+1}; q)∞`,
both cleared-denominator differences `mtc0ClearedDifference` and `mtc1ClearedDifference` factor
through the finite partial product `qfac_N`, while the real partial product `qPochhammerPartialProduct q N`
satisfies $0 < P_N(q) \le 1$ and the Weierstrass lower bound $1 - S_N(q) \le P_N(q)$. -/
theorem mockTheta_finite_truncation_remainder_decomposition_and_weierstrass_divisor_bound
    {R_q : Type*} [CommRing R_q]
    (X qfac qfac_N qfac_tail f0 f1 Phi1 Phi2 J5_10 J2_5 J1_5 : R_q)
    (hqfac_split : qfac = qfac_N * qfac_tail)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ) :
    mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_N * (qfac_tail * (f0 + 2 * (Phi1 - 1))) - J5_10 * J2_5 ∧
      mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_N * (qfac_tail * (X * f1 + 2 * (Phi2 - 1))) - X * (J5_10 * J1_5) ∧
      0 < qPochhammerPartialProduct q N ∧
      qPochhammerPartialProduct q N ≤ 1 ∧
      1 - qGeometricPartialSum q N ≤ qPochhammerPartialProduct q N ∧
      (1 - 2 * q) / (1 - q) ≤ qPochhammerPartialProduct q N := by
  have h0 :
      mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        qfac_N * (qfac_tail * (f0 + 2 * (Phi1 - 1))) - J5_10 * J2_5 := by
    unfold mtc0ClearedDifference
    rw [hqfac_split]
    ring
  have h1 :
      mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac_N * (qfac_tail * (X * f1 + 2 * (Phi2 - 1))) - X * (J5_10 * J1_5) := by
    unfold mtc1ClearedDifference
    rw [hqfac_split]
    ring
  have hP := qPochhammerPartialProduct_succ_and_pos_and_le_one q hq_nn hq_lt N
  have hW := qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity q hq_nn hq_lt N
  exact ⟨h0, h1, hP.2.1, hP.2.2.1, hW.1, hW.2.2.2.2⟩

/-- Quantum-channel Six-Vector Orthogonality Certificate ($(\det M)^2 = 1$ and $3 \times 3$ Gram
determinant conservation) paired with fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term factorizations, the $q$-Pochhammer Weierstrass lower bound, and the Rademacher-Kloosterman
subleading $c \ge 2$ exponential suppression gap. -/
theorem multiChannel_sixVectorOrthogonality_with_qPochhammerWeierstrass_and_kloostermanRademacherGap
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
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ)
    (C_eff Δ : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (c : ℕ) (hc : 2 ≤ c)
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
      0 < qPochhammerPartialProduct q N ∧
      1 - qGeometricPartialSum q N ≤ qPochhammerPartialProduct q N ∧
      rademacherKloostermanChannelExponent C_eff Δ c ≤ rademacherCardyMinimalEntropy C_eff Δ / 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ / 2 ≤
        rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c := by
  intro u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hmtc0 := mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 hqfac0 hPhi1
  have hmtc1 := mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 hqfac1 hPhi2
  have hP := qPochhammerPartialProduct_succ_and_pos_and_le_one q hq_nn hq_lt N
  have hW := qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity q hq_nn hq_lt N
  have hK := rademacher_kloosterman_subleading_channel_exponential_suppression_gap C_eff Δ hC hΔ c hc
  exact ⟨horth.2.2.1, horth.2.2.2, hmtc0.1, hmtc1.1, hP.2.1, hW.1, hK.2.1, hK.2.2.2.1⟩

/-- Master synthesis uniting the $q$-Pochhammer partial-product Weierstrass lower bound, geometric
series telescoping, Rademacher-Kloosterman subleading $c \ge 2$ exponential suppression gap,
Rademacher-Cardy saddle-point quadratic completion, fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`)
bilateral constant-term factorizations, five-fold Euler residue-partition splitting, short
projective-root `p = 71` Householder reflection isometry, octahedral-to-Legendre elliptic
$j$-invariant identity, and quantum-channel $3 \times 3$ Gram determinant conservation. -/
theorem multiChannel_qPochhammer_weierstrass_and_kloosterman_rademacher_gap_master_synthesis
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
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1) (N : ℕ)
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β) (c : ℕ) (hc : 2 ≤ c)
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
      0 < qPochhammerPartialProduct q N ∧
      1 - qGeometricPartialSum q N ≤ qPochhammerPartialProduct q N ∧
      (1 - 2 * q) / (1 - q) ≤ qPochhammerPartialProduct q N ∧
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherKloostermanChannelExponent C_eff Δ c ≤ rademacherCardyMinimalEntropy C_eff Δ / 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ / 2 ≤
        rademacherCardyMinimalEntropy C_eff Δ - rademacherKloostermanChannelExponent C_eff Δ c ∧
      reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
        (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro u₁ u₂ u₃
  have h5split := mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2 hq5 hJ2 hJ1
  have hmain := multiChannel_sixVectorOrthogonality_with_qPochhammerWeierstrass_and_kloostermanRademacherGap
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac f0 f1 Phi1 Phi2 B0_lead B0_tail B1_lead B1_tail J5_10 J2_5 J1_5 P1_5 P4_5 P2_5 P3_5
    h5split.1 hPhi1 h5split.2.1 hPhi2 q hq_nn hq_lt N C_eff Δ hC hΔ c hc x
  have hW := qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity q hq_nn hq_lt N
  have hcardy := rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    C_eff Δ β hC hΔ hβ
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
    hmain.2.2.2.2.2.1, hW.2.2.2.2, hcardy.1, hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2, ?_, hj.1⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

#print axioms qPochhammerPartialProduct_succ_and_pos_and_le_one
#print axioms qPochhammerPartialProduct_weierstrass_lower_bound_and_geometric_sum_identity
#print axioms rademacher_kloosterman_subleading_channel_exponential_suppression_gap
#print axioms mockTheta_finite_truncation_remainder_decomposition_and_weierstrass_divisor_bound
#print axioms multiChannel_sixVectorOrthogonality_with_qPochhammerWeierstrass_and_kloostermanRademacherGap
#print axioms multiChannel_qPochhammer_weierstrass_and_kloosterman_rademacher_gap_master_synthesis

end KFCausalArbitrarySourceMultiChannelQPochhammerPartialProductWeierstrassLowerBoundAndKloostermanRademacherSubleadingGap
end Audit
end UnifiedTheory
