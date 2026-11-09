/- Six-Vector Orthogonality Certificate ($M^T M = I_3$, Global Norm Preservation, and $(\det M)^2 = 1$
Quantum-Channel $3 \times 3$ Spectral Covariance Gram Determinant Conservation from Norm Preservation on
6 Scaled Ramanujan Perfect Directions), Unimodular Scalar-Zero Lattice Generation, Division-Free
Short Projective-Root Integral Householder Reflection Involution on Reflective Ternary Lattices $L_v$,
and the Octahedral-to-Legendre Elliptic $j$-Invariant Identity $-256 J_{\mathrm{oct}}(i, j, k) = j_{\mathrm{Leg}}(-(j/i)^2)$
on the Isotropic Conic $i^2 + j^2 + k^2 = 0$. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceDegreeMPolyState antipodalWeights antipodalSources identicalPackets)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelThreeByThreeSpectralGramDeterminant)
open UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileTernaryQuadraticPencilGL3DeterminantScalingAndRamanujanSixDirectionPerfectReconstruction
  (multiChannelTernaryLinearCombination
   gl3Determinant
   multiChannelTernaryQuadraticPencil_ramanujan_sixDirection_perfect_reconstruction
   multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
   multiChannelThreeByThreeSpectralGramDeterminant_gl3_hadamard_and_popoviciu_bounds)

section SixVectorOrthogonalityShortRootReflectionAndOctahedralLegendreJ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- General ternary quadratic form evaluation
`A x^2 + B y^2 + C z^2 + D x y + E_c x z + F y z` (`Ramanujan.MultiQuintuple.ternaryQuadraticEval`). -/
def ternaryQuadraticEval (A B C D E_c F x y z : ℝ) : ℝ :=
  A * x ^ 2 + B * y ^ 2 + C * z ^ 2 + D * x * y + E_c * x * z + F * y * z

/-- Squared Euclidean norm of the image of `(x, y, z)` under a $3 \times 3$ matrix `(aᵢⱼ)`
(`Ramanujan.MultiQuintuple.ternaryMatrixImageNorm`). -/
def ternaryMatrixImageNorm
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x y z : ℝ) : ℝ :=
  (a₁₁ * x + a₁₂ * y + a₁₃ * z) ^ 2 +
    (a₂₁ * x + a₂₂ * y + a₂₃ * z) ^ 2 +
    (a₃₁ * x + a₃₂ * y + a₃₃ * z) ^ 2

/-- Integral 3-vector dot product (`Ramanujan.MultiQuintuple.ternaryDot`). -/
def ternaryDot (a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) : ℤ :=
  a₁ * b₁ + a₂ * b₂ + a₃ * b₃

/-- Integral 3-vector squared Euclidean norm (`Ramanujan.MultiQuintuple.ternaryNorm`). -/
def ternaryNorm (a₁ a₂ a₃ : ℤ) : ℤ :=
  a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2

/-- Division-free integral Householder reflection coordinate `x - c * t * w`
(`Ramanujan.MultiQuintuple.shortRootReflectCoord`). -/
def shortRootReflectCoord (c t w x : ℤ) : ℤ :=
  x - c * t * w

/-- Residue-restricted ternary lattice norm for the `p = 71`, `(1, 11, 34)` reflective class
(`Ramanujan.MultiQuintuple.reflectiveNorm71`). -/
def reflectiveNorm71 (x y z : ℤ) : ℤ :=
  x ^ 2 + y ^ 2 + (48 * x + 31 * y + 71 * z) ^ 2

/-- First coordinate of the `p = 71` integral lattice reflection (`Ramanujan.MultiQuintuple.reflect71X`). -/
def reflect71X (x y z : ℤ) : ℤ := 37 * x + 24 * y + 54 * z

/-- Second coordinate of the `p = 71` integral lattice reflection (`Ramanujan.MultiQuintuple.reflect71Y`). -/
def reflect71Y (x y z : ℤ) : ℤ := -30 * x - 19 * y - 45 * z

/-- Third coordinate of the `p = 71` integral lattice reflection (`Ramanujan.MultiQuintuple.reflect71Z`). -/
def reflect71Z (x y z : ℤ) : ℤ := -12 * x - 8 * y - 17 * z

/-- Second elementary symmetric polynomial of squared coordinates `i^2 j^2 + j^2 k^2 + k^2 i^2`
(`Ramanujan.MultiQuintuple.ternarySquareSigma2`). -/
def ternarySquareSigma2 {K : Type*} [CommRing K] (i j k : K) : K :=
  i ^ 2 * j ^ 2 + j ^ 2 * k ^ 2 + k ^ 2 * i ^ 2

/-- Third elementary symmetric polynomial of squared coordinates `i^2 j^2 k^2`
(`Ramanujan.MultiQuintuple.ternarySquareSigma3`). -/
def ternarySquareSigma3 {K : Type*} [CommRing K] (i j k : K) : K :=
  i ^ 2 * j ^ 2 * k ^ 2

/-- Octahedral projective invariant `J_oct(i, j, k) = (i^2 j^2 + j^2 k^2 + k^2 i^2)^3 / (i^2 j^2 k^2)^2`
(`Ramanujan.MultiQuintuple.octahedralJ`). -/
def octahedralJ {K : Type*} [Field K] (i j k : K) : K :=
  ternarySquareSigma2 i j k ^ 3 / ternarySquareSigma3 i j k ^ 2

/-- Classical Legendre elliptic-curve `j`-invariant
`j_Leg(λ) = 256 (1 - λ + λ^2)^3 / (λ^2 (1 - λ)^2)` (`Ramanujan.MultiQuintuple.legendreJ`). -/
def legendreJ {K : Type*} [Field K] (lam : K) : K :=
  256 * (1 - lam + lam ^ 2) ^ 3 / (lam ^ 2 * (1 - lam) ^ 2)

/-- **Six-Vector Orthogonality Certificate ($M^T M = I_3$, Global Norm Preservation, and
$(\det M)^2 = 1$ Quantum-Channel $3 \times 3$ Gram Determinant Conservation)**:
If a $3 \times 3$ real matrix $M = (a_{ij})$ preserves the Euclidean norm on the 6 scaled
Ramanujan perfect directions `p(1, 1, 1), p(-1, 1, 1), p(1, -1, 1), p(1, 1, -1), p(2, 1, 1), p(1, 2, 1)`
for `p ≠ 0` (the 4 vectors of norm `3 p^2` and 2 vectors of norm `6 p^2` from
`Ramanujan.MultiQuintuple.ternaryMatrix_norm_preserving_of_six_vectors`), then:
1. $M^T M = I_3$ in all 6 symmetric entries;
2. `ternaryMatrixImageNorm a₁₁ ... a₃₃ x y z = x^2 + y^2 + z^2` for all `(x, y, z) ∈ ℝ^3`;
3. `(gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃)^2 = 1`;
4. Exact conservation of the finite `Q`-channel $3 \times 3$ spectral covariance Gram determinant:
   `Det3_Q(M(w₁, w₂, w₃), ψ) = Det3_Q(w₁, w₂, w₃, ψ)`. -/
theorem six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    (x y z : ℝ) (ψ : E) :
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    (a₁₁ ^ 2 + a₂₁ ^ 2 + a₃₁ ^ 2 = 1 ∧
      a₁₂ ^ 2 + a₂₂ ^ 2 + a₃₂ ^ 2 = 1 ∧
      a₁₃ ^ 2 + a₂₃ ^ 2 + a₃₃ ^ 2 = 1 ∧
      a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂ = 0 ∧
      a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃ = 0 ∧
      a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃ = 0) ∧
    ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x y z =
      x ^ 2 + y ^ 2 + z ^ 2 ∧
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ ψ =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ ψ := by
  intro u₁ u₂ u₃
  let A := a₁₁ ^ 2 + a₂₁ ^ 2 + a₃₁ ^ 2 - 1
  let B := a₁₂ ^ 2 + a₂₂ ^ 2 + a₃₂ ^ 2 - 1
  let C := a₁₃ ^ 2 + a₂₃ ^ 2 + a₃₃ ^ 2 - 1
  let D := 2 * (a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂)
  let E_c := 2 * (a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃)
  let F := 2 * (a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃)
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hdiff : ∀ u v w : ℝ,
      ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ u v w -
        (u ^ 2 + v ^ 2 + w ^ 2) =
        ternaryQuadraticEval A B C D E_c F u v w := by
    intro u v w
    unfold ternaryMatrixImageNorm ternaryQuadraticEval
    dsimp only [A, B, C, D, E_c, F]
    ring
  have hscale : ∀ u v w : ℝ,
      ternaryQuadraticEval A B C D E_c F (p * u) (p * v) (p * w) =
        p ^ 2 * ternaryQuadraticEval A B C D E_c F u v w := by
    intro u v w
    unfold ternaryQuadraticEval
    ring
  have hunscale : ∀ u v w : ℝ,
      ternaryQuadraticEval A B C D E_c F (p * u) (p * v) (p * w) = 0 →
        ternaryQuadraticEval A B C D E_c F u v w = 0 := by
    intro u v w hsc
    rw [hscale u v w] at hsc
    exact (mul_eq_zero.mp hsc).resolve_left hp2
  have q1 : ternaryQuadraticEval A B C D E_c F 1 1 1 = 0 := by
    apply hunscale 1 1 1
    have hd := hdiff p p p
    simp only [mul_one] at hd ⊢
    linarith [hd, h1]
  have q2 : ternaryQuadraticEval A B C D E_c F (-1) 1 1 = 0 := by
    apply hunscale (-1) 1 1
    have hd := hdiff (-p) p p
    have hneg : p * (-1) = -p := by ring
    rw [hneg, mul_one]
    linarith [hd, h2]
  have q3 : ternaryQuadraticEval A B C D E_c F 1 (-1) 1 = 0 := by
    apply hunscale 1 (-1) 1
    have hd := hdiff p (-p) p
    have hneg : p * (-1) = -p := by ring
    rw [mul_one, hneg]
    linarith [hd, h3]
  have q4 : ternaryQuadraticEval A B C D E_c F 1 1 (-1) = 0 := by
    apply hunscale 1 1 (-1)
    have hd := hdiff p p (-p)
    have hneg : p * (-1) = -p := by ring
    rw [mul_one, hneg]
    linarith [hd, h4]
  have q5 : ternaryQuadraticEval A B C D E_c F 2 1 1 = 0 := by
    apply hunscale 2 1 1
    have hd := hdiff (2 * p) p p
    have htwo : p * 2 = 2 * p := by ring
    rw [htwo, mul_one]
    linarith [hd, h5]
  have q6 : ternaryQuadraticEval A B C D E_c F 1 2 1 = 0 := by
    apply hunscale 1 2 1
    have hd := hdiff p (2 * p) p
    have htwo : p * 2 = 2 * p := by ring
    rw [mul_one, htwo]
    linarith [hd, h6]
  unfold ternaryQuadraticEval at q1 q2 q3 q4 q5 q6
  have hA : A = 0 := by linarith
  have hB : B = 0 := by linarith
  have hC : C = 0 := by linarith
  have hD : D = 0 := by linarith
  have hEc : E_c = 0 := by linarith
  have hF : F = 0 := by linarith
  have hg11 : a₁₁ ^ 2 + a₂₁ ^ 2 + a₃₁ ^ 2 = 1 := by dsimp only [A] at hA; linarith
  have hg22 : a₁₂ ^ 2 + a₂₂ ^ 2 + a₃₂ ^ 2 = 1 := by dsimp only [B] at hB; linarith
  have hg33 : a₁₃ ^ 2 + a₂₃ ^ 2 + a₃₃ ^ 2 = 1 := by dsimp only [C] at hC; linarith
  have hg12 : a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂ = 0 := by dsimp only [D] at hD; linarith
  have hg13 : a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃ = 0 := by dsimp only [E_c] at hEc; linarith
  have hg23 : a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃ = 0 := by dsimp only [F] at hF; linarith
  have hnorm_xyz :
      ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x y z =
        x ^ 2 + y ^ 2 + z ^ 2 := by
    have hd := hdiff x y z
    rw [show ternaryQuadraticEval A B C D E_c F x y z = 0 by
      unfold ternaryQuadraticEval; rw [hA, hB, hC, hD, hEc, hF]; ring] at hd
    linarith
  have hdet_sq_gram :
      (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 =
        (a₁₁ ^ 2 + a₂₁ ^ 2 + a₃₁ ^ 2) *
          ((a₁₂ ^ 2 + a₂₂ ^ 2 + a₃₂ ^ 2) * (a₁₃ ^ 2 + a₂₃ ^ 2 + a₃₃ ^ 2) -
            (a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃) ^ 2) -
        (a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂) *
          ((a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂) * (a₁₃ ^ 2 + a₂₃ ^ 2 + a₃₃ ^ 2) -
            (a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃) * (a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃)) +
        (a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃) *
          ((a₁₁ * a₁₂ + a₂₁ * a₂₂ + a₃₁ * a₃₂) * (a₁₂ * a₁₃ + a₂₂ * a₂₃ + a₃₂ * a₃₃) -
            (a₁₂ ^ 2 + a₂₂ ^ 2 + a₃₂ ^ 2) * (a₁₁ * a₁₃ + a₂₁ * a₂₃ + a₃₁ * a₃₃)) := by
    unfold gl3Determinant
    ring
  have hdet_sq : (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 := by
    rw [hdet_sq_gram, hg11, hg22, hg33, hg12, hg13, hg23]
    ring
  have hgl3 := (multiChannelThreeByThreeSpectralGramDeterminant_gl3_transformation_and_sl3_invariance
    P w₁ w₂ w₃ a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ 0 0 0 ψ).2.1 hdet_sq
  exact ⟨⟨hg11, hg22, hg33, hg12, hg13, hg23⟩, hnorm_xyz, hdet_sq, hgl3⟩

/-- **Unimodular Scalar-Zero Lattice Generation and Projective Dual Lift**
(`Ramanujan.MultiQuintuple.dualPerfectGenerators_det`, `dualPerfectVectors_generate_scalarZero`,
`projectiveDual_generated_by_unitLift_and_perfectVectors`):
1. The 6 perfect directions have norms `3 p^2, 3 p^2, 3 p^2, 3 p^2, 6 p^2, 6 p^2`;
2. The three generators `(p, p, p), (2 p, p, p), (p, 2 p, p)` have determinant `p^3`;
3. Every vector `(p x, p y, p z) ∈ p ℤ^3` is an explicit `ℤ`-linear combination of those 3 generators
   with coefficients `α = 3 z - x - y, β = x - z, γ = y - z`;
4. Combining any projective lift `w = λ v + p z` with those 3 generators spans the entire
   integral projective dual lattice. -/
theorem unimodular_scalarZero_lattice_generation_and_projective_dual_lift
    (p_real : ℝ) (p lam i j k w₁ w₂ w₃ z₁ z₂ z₃ t₁ t₂ t₃ x y z : ℤ)
    (hw₁ : w₁ = lam * i + p * z₁)
    (hw₂ : w₂ = lam * j + p * z₂)
    (hw₃ : w₃ = lam * k + p * z₃) :
    let α := 3 * z - x - y
    let β := x - z
    let γ := y - z
    let z₁' := z₁ - lam * t₁
    let z₂' := z₂ - lam * t₂
    let z₃' := z₃ - lam * t₃
    let α' := 3 * z₃' - z₁' - z₂'
    let β' := z₁' - z₃'
    let γ' := z₂' - z₃'
    (ternaryNorm p p p = 3 * p ^ 2 ∧
      ternaryNorm (-p) p p = 3 * p ^ 2 ∧
      ternaryNorm p (-p) p = 3 * p ^ 2 ∧
      ternaryNorm p p (-p) = 3 * p ^ 2 ∧
      ternaryNorm (2 * p) p p = 6 * p ^ 2 ∧
      ternaryNorm p (2 * p) p = 6 * p ^ 2) ∧
    gl3Determinant p_real p_real p_real (2 * p_real) p_real p_real p_real (2 * p_real) p_real =
      p_real ^ 3 ∧
    (p * x = α * p + β * (2 * p) + γ * p ∧
      p * y = α * p + β * p + γ * (2 * p) ∧
      p * z = α * p + β * p + γ * p) ∧
    (w₁ = lam * (i + p * t₁) + α' * p + β' * (2 * p) + γ' * p ∧
      w₂ = lam * (j + p * t₂) + α' * p + β' * p + γ' * (2 * p) ∧
      w₃ = lam * (k + p * t₃) + α' * p + β' * p + γ' * p) := by
  intro α β γ z₁' z₂' z₃' α' β' γ'
  unfold ternaryNorm gl3Determinant
  dsimp only [α, β, γ, z₁', z₂', z₃', α', β', γ']
  rw [hw₁, hw₂, hw₃]
  refine ⟨⟨by ring, by ring, by ring, by ring, by ring, by ring⟩,
    by ring, ⟨by ring, by ring, by ring⟩, ⟨by ring, by ring, by ring⟩⟩

/-- **Division-Free Short Projective-Root Integral Householder Reflection Involution on Reflective
Ternary Lattices $L_v$** (`Ramanujan.MultiQuintuple.shortProjectiveRoot_reflection` and `Reflective71`):
For an isotropic vector `v = (v₁, v₂, v₃)` modulo `p` (`||v||^2 = p h`), projective lift
`w = λ v + p a` of short root norm `||w||^2 = e p` (`c * e = 2`), and lattice point `x ∈ L_v`
(`v · x = p s`), the division-free Householder reflection `R_w(x) = x - c t w` with
`t = λ s + x · a` and `u = λ h + v · a` satisfies:
1. `x · w = p t` and `v · w = p u`;
2. Exact norm preservation `||R_w(x)||^2 = ||x||^2`;
3. Exact congruence-lattice preservation `v · R_w(x) = p (s - c t u)`;
4. Root pairing negation `R_w(x) · w = -p t` and coordinatewise involutivity
   `shortRootReflectCoord c (-t) wᵢ (shortRootReflectCoord c t wᵢ xᵢ) = xᵢ`;
5. Concrete `p = 71`, `(1, 11, 34)` short projective root `w = (6, -5, -9)` of norm `2 * 71 = 142`
   and exact isometry & involutivity of `(reflect71X, reflect71Y, reflect71Z)`. -/
theorem shortProjectiveRoot_householder_reflection_isometry_involution_and_lattice_invariance
    (p e c lam v₁ v₂ v₃ w₁ w₂ w₃ a₁ a₂ a₃ h x₁ x₂ x₃ s : ℤ)
    (hw₁ : w₁ = lam * v₁ + p * a₁)
    (hw₂ : w₂ = lam * v₂ + p * a₂)
    (hw₃ : w₃ = lam * v₃ + p * a₃)
    (hisotropic : ternaryNorm v₁ v₂ v₃ = p * h)
    (hroot : ternaryNorm w₁ w₂ w₃ = e * p)
    (hcoeff : c * e = 2)
    (hx : ternaryDot v₁ v₂ v₃ x₁ x₂ x₃ = p * s) :
    let t := lam * s + ternaryDot x₁ x₂ x₃ a₁ a₂ a₃
    let u := lam * h + ternaryDot v₁ v₂ v₃ a₁ a₂ a₃
    let rx₁ := shortRootReflectCoord c t w₁ x₁
    let rx₂ := shortRootReflectCoord c t w₂ x₂
    let rx₃ := shortRootReflectCoord c t w₃ x₃
    ternaryDot x₁ x₂ x₃ w₁ w₂ w₃ = p * t ∧
    ternaryDot v₁ v₂ v₃ w₁ w₂ w₃ = p * u ∧
    ternaryNorm rx₁ rx₂ rx₃ = ternaryNorm x₁ x₂ x₃ ∧
    ternaryDot v₁ v₂ v₃ rx₁ rx₂ rx₃ = p * (s - c * t * u) ∧
    ternaryDot rx₁ rx₂ rx₃ w₁ w₂ w₃ = -p * t ∧
    (shortRootReflectCoord c (-t) w₁ rx₁ = x₁ ∧
      shortRootReflectCoord c (-t) w₂ rx₂ = x₂ ∧
      shortRootReflectCoord c (-t) w₃ rx₃ = x₃) ∧
    ternaryNorm 6 (-5) (-9) = 2 * 71 ∧
    reflectiveNorm71 (reflect71X x₁ x₂ x₃) (reflect71Y x₁ x₂ x₃) (reflect71Z x₁ x₂ x₃) =
      reflectiveNorm71 x₁ x₂ x₃ ∧
    (reflect71X (reflect71X x₁ x₂ x₃) (reflect71Y x₁ x₂ x₃) (reflect71Z x₁ x₂ x₃) = x₁ ∧
      reflect71Y (reflect71X x₁ x₂ x₃) (reflect71Y x₁ x₂ x₃) (reflect71Z x₁ x₂ x₃) = x₂ ∧
      reflect71Z (reflect71X x₁ x₂ x₃) (reflect71Y x₁ x₂ x₃) (reflect71Z x₁ x₂ x₃) = x₃) := by
  intro t u rx₁ rx₂ rx₃
  have hx_comm : ternaryDot x₁ x₂ x₃ v₁ v₂ v₃ = p * s := by
    unfold ternaryDot at hx ⊢
    linarith
  have hxt : ternaryDot x₁ x₂ x₃ w₁ w₂ w₃ = p * t := by
    dsimp only [t]
    unfold ternaryDot at hx_comm ⊢
    rw [hw₁, hw₂, hw₃]
    linear_combination lam * hx_comm
  have hvw : ternaryDot v₁ v₂ v₃ w₁ w₂ w₃ = p * u := by
    dsimp only [u]
    unfold ternaryNorm at hisotropic
    unfold ternaryDot
    rw [hw₁, hw₂, hw₃]
    linear_combination lam * hisotropic
  have hnorm_diff :
      ternaryNorm rx₁ rx₂ rx₃ - ternaryNorm x₁ x₂ x₃ = 0 := by
    calc
      ternaryNorm rx₁ rx₂ rx₃ - ternaryNorm x₁ x₂ x₃
        = -2 * c * t * ternaryDot x₁ x₂ x₃ w₁ w₂ w₃ + (c * t) ^ 2 * ternaryNorm w₁ w₂ w₃ := by
            dsimp only [rx₁, rx₂, rx₃]
            unfold ternaryNorm ternaryDot shortRootReflectCoord
            ring
      _ = -2 * c * t * (p * t) + (c * t) ^ 2 * (e * p) := by rw [hxt, hroot]
      _ = c * t ^ 2 * p * (-2 + c * e) := by ring
      _ = 0 := by rw [hcoeff]; ring
  have hlat : ternaryDot v₁ v₂ v₃ rx₁ rx₂ rx₃ = p * (s - c * t * u) := by
    calc
      ternaryDot v₁ v₂ v₃ rx₁ rx₂ rx₃
        = ternaryDot v₁ v₂ v₃ x₁ x₂ x₃ - c * t * ternaryDot v₁ v₂ v₃ w₁ w₂ w₃ := by
            dsimp only [rx₁, rx₂, rx₃]
            unfold ternaryDot shortRootReflectCoord
            ring
      _ = p * s - c * t * (p * u) := by rw [hx, hvw]
      _ = p * (s - c * t * u) := by ring
  have hflip : ternaryDot rx₁ rx₂ rx₃ w₁ w₂ w₃ = -p * t := by
    calc
      ternaryDot rx₁ rx₂ rx₃ w₁ w₂ w₃
        = ternaryDot x₁ x₂ x₃ w₁ w₂ w₃ - c * t * ternaryNorm w₁ w₂ w₃ := by
            dsimp only [rx₁, rx₂, rx₃]
            unfold ternaryDot ternaryNorm shortRootReflectCoord
            ring
      _ = p * t - c * t * (e * p) := by rw [hxt, hroot]
      _ = p * t * (1 - c * e) := by ring
      _ = -p * t := by rw [hcoeff]; ring
  refine ⟨hxt, hvw, sub_eq_zero.mp hnorm_diff, hlat, hflip, ?_, ?_, ?_, ?_⟩
  · dsimp only [rx₁, rx₂, rx₃]
    unfold shortRootReflectCoord
    exact ⟨by ring, by ring, by ring⟩
  · unfold ternaryNorm
    norm_num
  · unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
    ring
  · unfold reflect71X reflect71Y reflect71Z
    exact ⟨by ring, by ring, by ring⟩

/-- **Octahedral-to-Legendre Elliptic $j$-Invariant Identity on the Isotropic Conic**
(`Ramanujan.MultiQuintuple.neg_256_octahedralJ_eq_legendreJ`):
For any nonzero field elements `i, j, k : K` on the isotropic conic `i^2 + j^2 + k^2 = 0`:
1. `-256 * octahedralJ i j k = legendreJ (-(j / i) ^ 2)`;
2. `octahedralJ` is invariant under coordinate permutations and independent of overall scaling:
   `octahedralJ j i k = octahedralJ i j k` and `octahedralJ i k j = octahedralJ i j k`. -/
theorem octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic
    {K : Type*} [Field K] {i j k : K}
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hisotropic : i ^ 2 + j ^ 2 + k ^ 2 = 0) :
    -256 * octahedralJ i j k = legendreJ (-(j / i) ^ 2) ∧
    octahedralJ j i k = octahedralJ i j k ∧
    octahedralJ i k j = octahedralJ i j k := by
  have hi2 : i ^ 2 ≠ 0 := pow_ne_zero _ hi
  have hj2 : j ^ 2 ≠ 0 := pow_ne_zero _ hj
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero _ hk
  have hij : i ^ 2 + j ^ 2 ≠ 0 := by
    intro hij
    have hk0 : k ^ 2 = 0 := by linear_combination hisotropic - hij
    exact hk2 hk0
  have hkrel : k ^ 2 = -(i ^ 2 + j ^ 2) := by linear_combination hisotropic
  have hsigma2 :
      ternarySquareSigma2 i j k = -(i ^ 4 + i ^ 2 * j ^ 2 + j ^ 4) := by
    rw [ternarySquareSigma2,
      show i ^ 2 * j ^ 2 + j ^ 2 * k ^ 2 + k ^ 2 * i ^ 2 =
        (i ^ 2 + j ^ 2) * (i ^ 2 + j ^ 2 + k ^ 2) - (i ^ 4 + i ^ 2 * j ^ 2 + j ^ 4) by ring,
      hisotropic, mul_zero, zero_sub]
  have hmain : -256 * octahedralJ i j k = legendreJ (-(j / i) ^ 2) := by
    rw [octahedralJ, hsigma2, ternarySquareSigma3, hkrel, legendreJ]
    field_simp [hi, hj, hi2, hj2, hij]
    ring
  have hperm1 : octahedralJ j i k = octahedralJ i j k := by
    unfold octahedralJ ternarySquareSigma2 ternarySquareSigma3
    ring
  have hperm2 : octahedralJ i k j = octahedralJ i j k := by
    unfold octahedralJ ternarySquareSigma2 ternarySquareSigma3
    ring
  exact ⟨hmain, hperm1, hperm2⟩

/-- Six-Vector Orthogonality Certificate, Quantum-Channel `Det3_Q` Conservation, Short-Root
Householder Reflection Involution, and Octahedral-to-Legendre Elliptic $j$-Invariant Package on
`arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_sixVectorOrthogonality_shortRootReflection_and_octahedralLegendreJ_package
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    (x_int y_int z_int : ℤ)
    {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0)
    {n : ℕ} (M : ℕ) (w_src b_src : Fin n → ℂ) (c_poly : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    let Ψ := arbitrarySourceDegreeMPolyState M w_src b_src c_poly PK
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ Ψ =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
      (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
    -256 * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro Ψ u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 0 0 0 Ψ
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic
    hi_c hj_c hk_c hiso_c
  refine ⟨horth.2.2.1, horth.2.2.2, ?_, hj.1⟩
  unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z
  ring

/-- Master Synthesis of the Six-Vector Orthogonality Certificate, Quantum-Channel $3 \times 3$
Gram Determinant Conservation, Unimodular Scalar-Zero Lattice Generation, Short Projective-Root
Integral Householder Reflection Involution, and Octahedral-to-Legendre Elliptic $j$-Invariant
Identity on Neutral Antipodal Polynomial States. -/
theorem arbitrary_source_multiChannel_sixVectorOrthogonality_shortRootReflection_octahedralLegendreJ_master_synthesis
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q → ℝ)
    (p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℝ) (hp : p ≠ 0)
    (h1 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p p = 3 * p ^ 2)
    (h2 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (-p) p p = 3 * p ^ 2)
    (h3 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (-p) p = 3 * p ^ 2)
    (h4 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p p (-p) = 3 * p ^ 2)
    (h5 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ (2 * p) p p = 6 * p ^ 2)
    (h6 : ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ p (2 * p) p = 6 * p ^ 2)
    (x y z : ℝ) (x_int y_int z_int : ℤ)
    {i_c j_c k_c : ℂ} (hi_c : i_c ≠ 0) (hj_c : j_c ≠ 0) (hk_c : k_c ≠ 0)
    (hiso_c : i_c ^ 2 + j_c ^ 2 + k_c ^ 2 = 0)
    (M : ℕ) (c_poly : Fin (M + 2) → ℂ) (ψ : E) :
    let Ψ := arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c_poly
      (identicalPackets ψ)
    let u₁ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₁₁ a₁₂ a₁₃
    let u₂ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₂₁ a₂₂ a₂₃
    let u₃ := multiChannelTernaryLinearCombination w₁ w₂ w₃ a₃₁ a₃₂ a₃₃
    ternaryMatrixImageNorm a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ x y z =
      x ^ 2 + y ^ 2 + z ^ 2 ∧
    (gl3Determinant a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃) ^ 2 = 1 ∧
    multiChannelThreeByThreeSpectralGramDeterminant P u₁ u₂ u₃ Ψ =
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ Ψ ∧
    gl3Determinant p p p (2 * p) p p p (2 * p) p = p ^ 3 ∧
    reflectiveNorm71 (reflect71X x_int y_int z_int) (reflect71Y x_int y_int z_int)
      (reflect71Z x_int y_int z_int) = reflectiveNorm71 x_int y_int z_int ∧
    -256 * octahedralJ i_c j_c k_c = legendreJ (-(j_c / i_c) ^ 2) := by
  intro Ψ u₁ u₂ u₃
  have horth := six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
    P w₁ w₂ w₃ p a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ hp h1 h2 h3 h4 h5 h6 x y z Ψ
  have hj := octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic
    hi_c hj_c hk_c hiso_c
  refine ⟨horth.2.1, horth.2.2.1, horth.2.2.2, ?_, ?_, hj.1⟩
  · unfold gl3Determinant; ring
  · unfold reflectiveNorm71 reflect71X reflect71Y reflect71Z; ring

end SixVectorOrthogonalityShortRootReflectionAndOctahedralLegendreJ

#print axioms six_vector_orthogonality_certificate_and_quantum_channel_gram_determinant_conservation
#print axioms unimodular_scalarZero_lattice_generation_and_projective_dual_lift
#print axioms shortProjectiveRoot_householder_reflection_isometry_involution_and_lattice_invariance
#print axioms octahedral_to_legendre_elliptic_j_invariant_on_isotropic_conic
#print axioms arbitrarySourceDegreeMPolyState_sixVectorOrthogonality_shortRootReflection_and_octahedralLegendreJ_package
#print axioms arbitrary_source_multiChannel_sixVectorOrthogonality_shortRootReflection_octahedralLegendreJ_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSixVectorOrthogonalityCertificateShortRootHouseholderReflectionAndOctahedralLegendreJInvariant
