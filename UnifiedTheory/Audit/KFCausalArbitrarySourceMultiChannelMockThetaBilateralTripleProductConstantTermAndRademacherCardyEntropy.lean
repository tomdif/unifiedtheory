/- Arbitrary-Source Multi-Channel Fifth-Order Mock Theta Conjecture (`MTC₀`/`MTC₁`) Bilateral
Triple-Product Constant-Term Decomposition, Five-Fold Euler Residue-Partition Factorization
(`qfacInf_split₀` & `qfacInf_split₁`), Joint Two-Conjecture Eliminant Identity, Rademacher-Cardy /
Hardy-Ramanujan Saddle-Point Black-Hole Microstate Entropy Bound
$2 \pi^2 C_{\mathrm{eff}} / \beta + \beta \Delta \ge 2 \pi \sqrt{2 C_{\mathrm{eff}} \Delta}$, and
Quantum-Channel $3 \times 3$ Gram Determinant Synthesis. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy

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

/-- Cleared-denominator difference `(q)∞ f₀(q) + 2 (q)∞ (Φ₁(q) - 1) - J_{5,10} J_{2,5}` for the
first fifth-order Mock Theta Conjecture (`MTC₀`). -/
def mtc0ClearedDifference {R : Type*} [CommRing R] (qfac f0 Phi1 J5_10 J2_5 : R) : R :=
  qfac * f0 + 2 * qfac * (Phi1 - 1) - J5_10 * J2_5

/-- Cleared-denominator difference `q (q)∞ f₁(q) + 2 (q)∞ (Φ₂(q) - 1) - q J_{5,10} J_{1,5}` for the
second fifth-order Mock Theta Conjecture (`MTC₁`). -/
def mtc1ClearedDifference {R : Type*} [CommRing R] (X qfac f1 Phi2 J5_10 J1_5 : R) : R :=
  X * qfac * f1 + 2 * qfac * (Phi2 - 1) - X * (J5_10 * J1_5)

/-- `J_{2,5}`-reduced bilateral constant-term residual
`(P_{1,5} P_{4,5})(f₀ + 2(B_{0,\mathrm{lead}} + B_{0,\mathrm{tail}})) - J_{5,10}` for `MTC₀`. -/
def mtc0ThetaReducedResidual {R : Type*} [CommRing R]
    (P1_5 P4_5 f0 B0_lead B0_tail J5_10 : R) : R :=
  (P1_5 * P4_5) * (f0 + 2 * (B0_lead + B0_tail)) - J5_10

/-- `J_{1,5}`-reduced bilateral constant-term residual
`(P_{2,5} P_{3,5})(q f₁ + 2(B_{1,\mathrm{lead}} + B_{1,\mathrm{tail}})) - q J_{5,10}` for `MTC₁`. -/
def mtc1ThetaReducedResidual {R : Type*} [CommRing R]
    (P2_5 P3_5 X f1 B1_lead B1_tail J5_10 : R) : R :=
  (P2_5 * P3_5) * (X * f1 + 2 * (B1_lead + B1_tail)) - X * J5_10

/-- Rademacher-Cardy / Hardy-Ramanujan modular-inversion saddle-point exponent
`2 π² C_eff / β + β Δ` governing the asymptotic growth of mock-modular and modular partition
degeneracies. -/
noncomputable def rademacherCardySaddleExponent (C_eff Δ β : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * C_eff / β + β * Δ

/-- Rademacher-Cardy / Hardy-Ramanujan minimal saddle-point entropy
`2 π √(2 C_eff Δ)` attained at the modular saddle point `2 π² C_eff / β = β Δ`. -/
noncomputable def rademacherCardyMinimalEntropy (C_eff Δ : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (2 * C_eff * Δ)

/-- **First Fifth-Order Mock Theta Conjecture (`MTC₀`) Bilateral Constant-Term & Residue-Partition
Factorization**:
Under the residue-partition splitting `qfac = J2_5 * (P1_5 * P4_5)` (`qfacInf_split₀`) and the
bilateral constant-term decomposition `Phi1 - 1 = B0_lead + B0_tail` of the rank-generating series
`Φ₁(q) - 1 = [z⁰](1 + z)(z q; q)∞(z⁻¹ q; q)∞ / ((z q; q⁵)∞(z⁻¹ q⁴; q⁵)∞) - 1`, the cleared
`MTC₀` difference factors as `J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10`. -/
theorem mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    {R : Type*} [CommRing R]
    (qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 : R)
    (hqfac0 : qfac = J2_5 * (P1_5 * P4_5))
    (hPhi1 : Phi1 - 1 = B0_lead + B0_tail) :
    mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 ∧
      (mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 = 0 →
        qfac * f0 + 2 * qfac * (Phi1 - 1) = J5_10 * J2_5) ∧
      (qfac * f0 + 2 * qfac * (Phi1 - 1) = J5_10 * J2_5 →
        J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 = 0) := by
  have hfac :
      mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 =
        J2_5 * mtc0ThetaReducedResidual P1_5 P4_5 f0 B0_lead B0_tail J5_10 := by
    unfold mtc0ClearedDifference mtc0ThetaReducedResidual
    rw [hqfac0, hPhi1]
    ring
  refine ⟨hfac, ?_, ?_⟩
  · intro hres
    have h0 : mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 = 0 := by
      rw [hfac, hres, mul_zero]
    unfold mtc0ClearedDifference at h0
    exact sub_eq_zero.mp h0
  · intro hmtc0
    rw [← hfac]
    unfold mtc0ClearedDifference
    exact sub_eq_zero.mpr hmtc0

/-- **Second Fifth-Order Mock Theta Conjecture (`MTC₁`) Bilateral Constant-Term & Residue-Partition
Factorization**:
Under the residue-partition splitting `qfac = J1_5 * (P2_5 * P3_5)` (`qfacInf_split₁`) and the
bilateral constant-term decomposition `Phi2 - 1 = B1_lead + B1_tail` of the rank-generating series
`Φ₂(q) - 1 = [z⁰](1 + z)(z q; q)∞(z⁻¹ q; q)∞ / ((z q²; q⁵)∞(z⁻¹ q³; q⁵)∞) - 1`, the cleared
`MTC₁` difference factors as `J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10`. -/
theorem mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    {R : Type*} [CommRing R]
    (X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 : R)
    (hqfac1 : qfac = J1_5 * (P2_5 * P3_5))
    (hPhi2 : Phi2 - 1 = B1_lead + B1_tail) :
    mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 ∧
      (mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 = 0 →
        X * qfac * f1 + 2 * qfac * (Phi2 - 1) = X * (J5_10 * J1_5)) ∧
      (X * qfac * f1 + 2 * qfac * (Phi2 - 1) = X * (J5_10 * J1_5) →
        J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 = 0) := by
  have hfac :
      mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        J1_5 * mtc1ThetaReducedResidual P2_5 P3_5 X f1 B1_lead B1_tail J5_10 := by
    unfold mtc1ClearedDifference mtc1ThetaReducedResidual
    rw [hqfac1, hPhi2]
    ring
  refine ⟨hfac, ?_, ?_⟩
  · intro hres
    have h0 : mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 = 0 := by
      rw [hfac, hres, mul_zero]
    unfold mtc1ClearedDifference at h0
    exact sub_eq_zero.mp h0
  · intro hmtc1
    rw [← hfac]
    unfold mtc1ClearedDifference
    exact sub_eq_zero.mpr hmtc1

/-- **Five-Fold Euler Residue-Partition Splitting (`qfacInf_split₀` & `qfacInf_split₁`) and Joint
Two-Conjecture Eliminant Identity**:
When `(q; q)∞ = P_{0,5} P_{1,5} P_{2,5} P_{3,5} P_{4,5}` with `J_{2,5} = P_{0,5} P_{2,5} P_{3,5}`
and `J_{1,5} = P_{0,5} P_{1,5} P_{4,5}`, both `qfac = J_{2,5} (P_{1,5} P_{4,5})` and
`qfac = J_{1,5} (P_{2,5} P_{3,5})` hold simultaneously, and the linear combination
`(X * J1_5) * mtc0ClearedDifference - J2_5 * mtc1ClearedDifference` eliminates `J_{5,10}` identically. -/
theorem mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
    {R : Type*} [CommRing R]
    (X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2 : R)
    (hq5 : qfac = P0_5 * P1_5 * P2_5 * P3_5 * P4_5)
    (hJ2 : J2_5 = P0_5 * P2_5 * P3_5)
    (hJ1 : J1_5 = P0_5 * P1_5 * P4_5) :
    qfac = J2_5 * (P1_5 * P4_5) ∧
      qfac = J1_5 * (P2_5 * P3_5) ∧
      (X * J1_5) * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 -
          J2_5 * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac * ((X * J1_5) * (f0 + 2 * (Phi1 - 1)) - J2_5 * (X * f1 + 2 * (Phi2 - 1))) ∧
      (qfac * f0 + 2 * qfac * (Phi1 - 1) = J5_10 * J2_5 →
        X * qfac * f1 + 2 * qfac * (Phi2 - 1) = X * (J5_10 * J1_5) →
        qfac * ((X * J1_5) * (f0 + 2 * (Phi1 - 1)) - J2_5 * (X * f1 + 2 * (Phi2 - 1))) = 0) := by
  have hsplit0 : qfac = J2_5 * (P1_5 * P4_5) := by
    rw [hq5, hJ2]
    ring
  have hsplit1 : qfac = J1_5 * (P2_5 * P3_5) := by
    rw [hq5, hJ1]
    ring
  have helim :
      (X * J1_5) * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 -
          J2_5 * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac * ((X * J1_5) * (f0 + 2 * (Phi1 - 1)) - J2_5 * (X * f1 + 2 * (Phi2 - 1))) := by
    unfold mtc0ClearedDifference mtc1ClearedDifference
    ring
  refine ⟨hsplit0, hsplit1, helim, ?_⟩
  intro hmtc0 hmtc1
  rw [← helim]
  unfold mtc0ClearedDifference mtc1ClearedDifference
  rw [sub_eq_zero.mpr hmtc0, sub_eq_zero.mpr hmtc1]
  ring

/-- **Rademacher-Cardy / Hardy-Ramanujan Saddle-Point Completion of the Square and Minimal
Black-Hole Microstate Entropy Bound**:
For all `C_eff ≥ 0`, `Δ ≥ 0`, and inverse temperature `β > 0`,
`rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
  (√(2 π² C_eff / β) - √(β Δ))² ≥ 0`,
so `2 π √(2 C_eff Δ) ≤ 2 π² C_eff / β + β Δ`, with equality at the modular saddle point
`2 π² C_eff / β = β Δ`. -/
theorem rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β) :
    rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ ≤ rademacherCardySaddleExponent C_eff Δ β ∧
      0 ≤ rademacherCardyMinimalEntropy C_eff Δ ∧
      (2 * Real.pi ^ 2 * C_eff / β = β * Δ →
        rademacherCardySaddleExponent C_eff Δ β = rademacherCardyMinimalEntropy C_eff Δ) := by
  have hA : 0 ≤ 2 * Real.pi ^ 2 * C_eff / β := by positivity
  have hB : 0 ≤ β * Δ := by positivity
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hAB : (2 * Real.pi ^ 2 * C_eff / β) * (β * Δ) = Real.pi ^ 2 * (2 * C_eff * Δ) := by
    field_simp [hβ_ne]
  have hsqrt_prod :
      Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) * Real.sqrt (β * Δ) =
        Real.pi * Real.sqrt (2 * C_eff * Δ) := by
    rw [← Real.sqrt_mul hA (β * Δ), hAB, Real.sqrt_mul (sq_nonneg Real.pi),
      Real.sqrt_sq (le_of_lt Real.pi_pos)]
  have hsq :
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 := by
    calc rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ
        = (2 * Real.pi ^ 2 * C_eff / β) + (β * Δ) -
            2 * (Real.pi * Real.sqrt (2 * C_eff * Δ)) := by
          unfold rademacherCardySaddleExponent rademacherCardyMinimalEntropy
          ring
      _ = (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β)) ^ 2 + (Real.sqrt (β * Δ)) ^ 2 -
            2 * (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) * Real.sqrt (β * Δ)) := by
          rw [Real.sq_sqrt hA, Real.sq_sqrt hB, hsqrt_prod]
      _ = (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 := by ring
  have hmin_le : rademacherCardyMinimalEntropy C_eff Δ ≤ rademacherCardySaddleExponent C_eff Δ β := by
    have hnonneg : 0 ≤ (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 :=
      sq_nonneg _
    linarith [hsq]
  have hmin_nonneg : 0 ≤ rademacherCardyMinimalEntropy C_eff Δ := by
    unfold rademacherCardyMinimalEntropy
    positivity
  refine ⟨hsq, hmin_le, hmin_nonneg, ?_⟩
  intro hsad
  have hdiff_zero :
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ = 0 := by
    rw [hsq, hsad, sub_self, sq]
    ring
  linarith

/-- Quantum-channel Six-Vector Orthogonality Certificate ($(\det M)^2 = 1$ and $3 \times 3$ Gram
determinant conservation) paired with fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term factorizations and the Rademacher-Cardy saddle-point black-hole entropy bound. -/
theorem multiChannel_sixVectorOrthogonality_with_mockThetaBilateralSplit_and_rademacherCardyEntropy
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
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
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
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ ≤ rademacherCardySaddleExponent C_eff Δ β := by
  intro u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 x
  have hmtc0 := mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
    qfac f0 Phi1 B0_lead B0_tail J5_10 J2_5 P1_5 P4_5 hqfac0 hPhi1
  have hmtc1 := mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
    X qfac f1 Phi2 B1_lead B1_tail J5_10 J1_5 P2_5 P3_5 hqfac1 hPhi2
  have hcardy := rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
    C_eff Δ β hC hΔ hβ
  exact ⟨horth.2.2.1, horth.2.2.2, hmtc0.1, hmtc1.1, hcardy.1, hcardy.2.1⟩

/-- Master synthesis uniting the fifth-order Mock Theta Conjecture (`MTC₀`/`MTC₁`) bilateral
constant-term decompositions, five-fold Euler residue-partition splitting, joint two-conjecture
eliminant identity, Rademacher-Cardy saddle-point quadratic completion & minimal black-hole
entropy bound, short projective-root `p = 71` Householder reflection isometry, octahedral-to-Legendre
elliptic $j$-invariant identity, and quantum-channel $3 \times 3$ Gram determinant conservation. -/
theorem multiChannel_mockTheta_bilateral_tripleProduct_constantTerm_and_rademacherCardy_master_synthesis
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
    (C_eff Δ β : ℝ) (hC : 0 ≤ C_eff) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
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
      (X * J1_5) * mtc0ClearedDifference qfac f0 Phi1 J5_10 J2_5 -
          J2_5 * mtc1ClearedDifference X qfac f1 Phi2 J5_10 J1_5 =
        qfac * ((X * J1_5) * (f0 + 2 * (Phi1 - 1)) - J2_5 * (X * f1 + 2 * (Phi2 - 1))) ∧
      rademacherCardySaddleExponent C_eff Δ β - rademacherCardyMinimalEntropy C_eff Δ =
        (Real.sqrt (2 * Real.pi ^ 2 * C_eff / β) - Real.sqrt (β * Δ)) ^ 2 ∧
      rademacherCardyMinimalEntropy C_eff Δ ≤ rademacherCardySaddleExponent C_eff Δ β ∧
      reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
        (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
      (-256) * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro u₁ u₂ u₃
  have h5split := mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
    X qfac P0_5 P1_5 P2_5 P3_5 P4_5 J2_5 J1_5 J5_10 f0 f1 Phi1 Phi2 hq5 hJ2 hJ1
  have hmain := multiChannel_sixVectorOrthogonality_with_mockThetaBilateralSplit_and_rademacherCardyEntropy
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6
    X qfac f0 f1 Phi1 Phi2 B0_lead B0_tail B1_lead B1_tail J5_10 J2_5 J1_5 P1_5 P4_5 P2_5 P3_5
    h5split.1 hPhi1 h5split.2.1 hPhi2 C_eff Δ β hC hΔ hβ x
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic hi_c hj_c hk_c hiso_c
  refine ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, h5split.2.2.1,
    hmain.2.2.2.2.1, hmain.2.2.2.2.2, ?_, hj.1⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

#print axioms mockThetaConjecture_mtc0_bilateral_constant_term_and_residue_split
#print axioms mockThetaConjecture_mtc1_bilateral_constant_term_and_residue_split
#print axioms mockThetaConjectures_fiveFold_euler_partition_split_and_joint_eliminant_identity
#print axioms rademacher_cardy_saddle_point_completion_of_square_and_minimal_entropy_bound
#print axioms multiChannel_sixVectorOrthogonality_with_mockThetaBilateralSplit_and_rademacherCardyEntropy
#print axioms multiChannel_mockTheta_bilateral_tripleProduct_constantTerm_and_rademacherCardy_master_synthesis

end KFCausalArbitrarySourceMultiChannelMockThetaBilateralTripleProductConstantTermAndRademacherCardyEntropy
end Audit
end UnifiedTheory
