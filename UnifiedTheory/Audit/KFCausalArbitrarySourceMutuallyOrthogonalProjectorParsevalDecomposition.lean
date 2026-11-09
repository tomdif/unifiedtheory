/- Mutually Orthogonal Projections (`P₁ P₂ = P₂ P₁ = 0`), Three-Channel (`P₁`, `P₂`, `I - P₁ - P₂`)
and Finite `Q`-Channel (`∑_{q < Q} P_q`, `I - ∑_{q < Q} P_q`) Parseval / Pythagorean `hilbertEnergy`
Decompositions, Resolution-of-Identity Completeness, and Multi-Subspace Arbitrary-Source
Degree-`M` Polynomial Superposition Splitting:
1. Defines `AreMutuallyOrthogonalProjections (P₁ P₂ : E →L[ℂ] E)` and `residualTwoProjector P₁ P₂ := id - (P₁ + P₂)`
   on any complex inner product space `E`, proving:
   - Cross-subspace sesquilinear orthogonality `inner ℂ (P₁ x) (P₂ y) = 0` and `inner ℂ (P₂ x) (P₁ y) = 0`,
   - Closure of orthogonal projections under mutually orthogonal addition: `IsOrthogonalProjection (P₁ + P₂)`,
   - Additive `hilbertEnergy` identity `hilbertEnergy ((P₁ + P₂) x) = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x)`,
   - Exact three-channel vector and `hilbertEnergy` Parseval decomposition:
     `x = P₁ x + P₂ x + residualTwoProjector P₁ P₂ x` and
     `hilbertEnergy x = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x) + hilbertEnergy (residualTwoProjector P₁ P₂ x)`.
2. Defines the finite `Q`-channel projector sum `totalProjector P := ∑ q : Fin Q, P q` and
   `residualMultiProjector P := id - totalProjector P`, proving:
   - Exact `(Q + 1)`-channel vector decomposition `x = (∑ q : Fin Q, P q x) + residualMultiProjector P x`,
   - Pythagorean energy split `hilbertEnergy x = hilbertEnergy (totalProjector P x) + hilbertEnergy (residualMultiProjector P x)`,
   - Exact resolution-of-identity completeness (`totalProjector P = id → residualMultiProjector P = 0`
     and `x = ∑ q : Fin Q, P q x`),
   - Isolate-channel decomposition and two-sided triangle bounds for any anchor channel `q₀ : Fin Q`.
3. Applies three-channel (`P₁`, `P₂`, `I - P₁ - P₂`) and `Q`-channel projector families to
   arbitrary-source multi-packet states (`arbitrarySourceModeState`, `arbitrarySourceDegreeMPolyState`,
   and the antipodal `n = 2` witness), establishing multi-subspace Parseval energy identities
   and projected dominant-mode bounds. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceModeState arbitrarySourceDegreeMPolyState
   antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceModeResponse arbitrarySourceDegreeMPolyResponse
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (IsOrthogonalProjection complementaryProjection hilbertEnergy
   proj_add_complementaryProjection isOrthogonalProjection_complementary
   hilbertEnergy_orthogonalProjection_pythagorean
   hilbertEnergy_add_of_inner_eq_zero
   arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition)

section MutuallyOrthogonalProjectorCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Two continuous linear operators `P₁, P₂ : E →L[ℂ] E` are mutually orthogonal projections
if both are orthogonal projections and their compositions vanish identically (`P₁ ∘ P₂ = 0` and `P₂ ∘ P₁ = 0`). -/
def AreMutuallyOrthogonalProjections (P₁ P₂ : E →L[ℂ] E) : Prop :=
  IsOrthogonalProjection P₁ ∧
  IsOrthogonalProjection P₂ ∧
  (∀ x : E, P₁ (P₂ x) = 0) ∧
  (∀ x : E, P₂ (P₁ x) = 0)

/-- The three-channel residual projection `I - (P₁ + P₂)`. -/
def residualTwoProjector (P₁ P₂ : E →L[ℂ] E) : E →L[ℂ] E :=
  complementaryProjection (P₁ + P₂)

/-- The finite `Q`-channel sum of projections `∑ q : Fin Q, P q`. -/
def totalProjector {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) : E →L[ℂ] E :=
  ∑ q : Fin Q, P q

/-- The finite `Q`-channel complementary residual projector `I - ∑ q : Fin Q, P q`. -/
def residualMultiProjector {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) : E →L[ℂ] E :=
  complementaryProjection (totalProjector P)

/-- Cross-subspace sesquilinear orthogonality for mutually orthogonal projections `P₁` and `P₂`:
`inner ℂ (P₁ x) (P₂ y) = 0` and `inner ℂ (P₂ x) (P₁ y) = 0`. -/
theorem inner_of_mutuallyOrthogonalProjections_eq_zero
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂) (x y : E) :
    inner ℂ (P₁ x) (P₂ y) = 0 ∧
    inner ℂ (P₂ x) (P₁ y) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [hP.1.2 x (P₂ y), hP.2.2.1 y, inner_zero_right]
  · rw [hP.2.1.2 x (P₁ y), hP.2.2.2 y, inner_zero_right]

/-- The sum `P₁ + P₂` of two mutually orthogonal projections is again an orthogonal projection,
and so is its complementary residual projector `residualTwoProjector P₁ P₂ = I - (P₁ + P₂)`. -/
theorem isOrthogonalProjection_add_and_residual_of_mutuallyOrthogonal
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂) :
    IsOrthogonalProjection (P₁ + P₂) ∧
    IsOrthogonalProjection (residualTwoProjector P₁ P₂) := by
  have hsum : IsOrthogonalProjection (P₁ + P₂) := by
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · change P₁ (P₁ x + P₂ x) + P₂ (P₁ x + P₂ x) = P₁ x + P₂ x
      rw [map_add, map_add, hP.1.1 x, hP.2.2.1 x, hP.2.2.2 x, hP.2.1.1 x, add_zero, zero_add]
    · change inner ℂ (P₁ x + P₂ x) y = inner ℂ x (P₁ y + P₂ y)
      rw [inner_add_left, inner_add_right, hP.1.2 x y, hP.2.1.2 x y]
  exact ⟨hsum, isOrthogonalProjection_complementary hsum⟩

/-- Exact `hilbertEnergy` additivity for `P₁ + P₂`:
`hilbertEnergy ((P₁ + P₂) x) = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x)`. -/
theorem hilbertEnergy_add_of_mutuallyOrthogonalProjections
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂) (x : E) :
    hilbertEnergy ((P₁ + P₂) x) = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x) := by
  change hilbertEnergy (P₁ x + P₂ x) = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x)
  have horth := inner_of_mutuallyOrthogonalProjections_eq_zero hP x x
  exact hilbertEnergy_add_of_inner_eq_zero horth.1 horth.2

/-- Exact three-channel vector and `hilbertEnergy` Parseval decomposition for two mutually
orthogonal projections `P₁, P₂` and their residual `I - (P₁ + P₂)`:
`x = P₁ x + P₂ x + residualTwoProjector P₁ P₂ x` and
`hilbertEnergy x = hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x) + hilbertEnergy (residualTwoProjector P₁ P₂ x)`. -/
theorem twoProjector_three_channel_parseval_decomposition
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂) (x : E) :
    P₁ x + P₂ x + residualTwoProjector P₁ P₂ x = x ∧
    hilbertEnergy x =
      hilbertEnergy (P₁ x) + hilbertEnergy (P₂ x) +
        hilbertEnergy (residualTwoProjector P₁ P₂ x) := by
  have hproj := isOrthogonalProjection_add_and_residual_of_mutuallyOrthogonal hP
  have hvec : P₁ x + P₂ x + residualTwoProjector P₁ P₂ x = x :=
    proj_add_complementaryProjection (P₁ + P₂) x
  have henergy :
      hilbertEnergy x =
        hilbertEnergy ((P₁ + P₂) x) + hilbertEnergy (residualTwoProjector P₁ P₂ x) :=
    hilbertEnergy_orthogonalProjection_pythagorean hproj.1 x
  rw [hilbertEnergy_add_of_mutuallyOrthogonalProjections hP x] at henergy
  exact ⟨hvec, henergy⟩

/-- For any complementary pair `(P, I - P)` of orthogonal projections, `P` and `I - P`
satisfy `AreMutuallyOrthogonalProjections P (complementaryProjection P)` with zero three-channel
residual `residualTwoProjector P (complementaryProjection P) = 0`. -/
theorem areMutuallyOrthogonalProjections_self_and_complementary
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) :
    AreMutuallyOrthogonalProjections P (complementaryProjection P) ∧
    residualTwoProjector P (complementaryProjection P) = 0 := by
  refine ⟨⟨hP, isOrthogonalProjection_complementary hP,
    fun x => (KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition.proj_and_complementaryProjection_annihilate hP x).1,
    fun x => (KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition.proj_and_complementaryProjection_annihilate hP x).2⟩, ?_⟩
  ext x
  change x - (P x + complementaryProjection P x) = 0
  rw [proj_add_complementaryProjection P x, sub_self]

/-! ### 2. Finite `Q`-Channel Projector Sums and Resolution of the Identity -/

/-- Pointwise evaluation of `totalProjector P` and exact `(Q + 1)`-channel vector decomposition
`x = (∑ q : Fin Q, P q x) + residualMultiProjector P x`. -/
theorem totalProjector_apply_and_residual_split
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (x : E) :
    totalProjector P x = ∑ q : Fin Q, P q x ∧
    (∑ q : Fin Q, P q x) + residualMultiProjector P x = x := by
  have happ : totalProjector P x = ∑ q : Fin Q, P q x := by
    unfold totalProjector
    exact ContinuousLinearMap.sum_apply Finset.univ P x
  refine ⟨happ, ?_⟩
  rw [← happ]
  exact proj_add_complementaryProjection (totalProjector P) x

/-- When `totalProjector P` is an orthogonal projection, `residualMultiProjector P` is also
an orthogonal projection and `hilbertEnergy x = hilbertEnergy (totalProjector P x) + hilbertEnergy (residualMultiProjector P x)`. -/
theorem totalProjector_and_residual_hilbertEnergy_pythagorean
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E))
    (hP : IsOrthogonalProjection (totalProjector P)) (x : E) :
    IsOrthogonalProjection (residualMultiProjector P) ∧
    hilbertEnergy x =
      hilbertEnergy (totalProjector P x) + hilbertEnergy (residualMultiProjector P x) :=
  ⟨isOrthogonalProjection_complementary hP,
   hilbertEnergy_orthogonalProjection_pythagorean hP x⟩

/-- When `P : Fin Q → (E →L[ℂ] E)` is a resolution of the identity (`totalProjector P = id`),
the residual projector `residualMultiProjector P` vanishes identically and every vector `x`
is reconstructed exactly by its `Q` channel projections `∑ q : Fin Q, P q x = x`. -/
theorem resolution_of_identity_completeness
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E))
    (hid : totalProjector P = ContinuousLinearMap.id ℂ E) (x : E) :
    residualMultiProjector P = 0 ∧
    residualMultiProjector P x = 0 ∧
    ∑ q : Fin Q, P q x = x := by
  have hres : residualMultiProjector P = 0 := by
    unfold residualMultiProjector complementaryProjection
    rw [hid, sub_self]
  have happ := (totalProjector_apply_and_residual_split P x).1
  rw [hid] at happ
  exact ⟨hres, by rw [hres]; rfl, happ.symm⟩

/-- Isolation of an anchor channel `q₀ : Fin Q` inside `totalProjector P x` and two-sided
norm bounds `‖P q₀ x‖ - ∑_{q ≠ q₀} ‖P q x‖ ≤ ‖totalProjector P x‖ ≤ ‖P q₀ x‖ + ∑_{q ≠ q₀} ‖P q x‖`. -/
theorem totalProjector_isolate_channel_and_norm_bounds
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (q₀ : Fin Q) (x : E) :
    totalProjector P x =
      P q₀ x + ∑ q ∈ Finset.univ.erase q₀, P q x ∧
    ‖P q₀ x‖ - ∑ q ∈ Finset.univ.erase q₀, ‖P q x‖ ≤ ‖totalProjector P x‖ ∧
    ‖totalProjector P x‖ ≤ ‖P q₀ x‖ + ∑ q ∈ Finset.univ.erase q₀, ‖P q x‖ := by
  have hiso :
      totalProjector P x = P q₀ x + ∑ q ∈ Finset.univ.erase q₀, P q x := by
    rw [(totalProjector_apply_and_residual_split P x).1]
    exact (Finset.add_sum_erase Finset.univ (fun q : Fin Q => P q x) (Finset.mem_univ q₀)).symm
  have hsum_le :
      ‖∑ q ∈ Finset.univ.erase q₀, P q x‖ ≤ ∑ q ∈ Finset.univ.erase q₀, ‖P q x‖ :=
    norm_sum_le (Finset.univ.erase q₀) (fun q => P q x)
  have hle : ‖totalProjector P x‖ ≤ ‖P q₀ x‖ + ∑ q ∈ Finset.univ.erase q₀, ‖P q x‖ := by
    rw [hiso]
    have h1 := norm_add_le (P q₀ x) (∑ q ∈ Finset.univ.erase q₀, P q x)
    linarith
  have hge : ‖P q₀ x‖ - ∑ q ∈ Finset.univ.erase q₀, ‖P q x‖ ≤ ‖totalProjector P x‖ := by
    have h1 := norm_le_add_norm_add (P q₀ x) (∑ q ∈ Finset.univ.erase q₀, P q x)
    rw [← hiso] at h1
    linarith
  exact ⟨hiso, hge, hle⟩

/-! ### 3. Three-Channel and `Q`-Channel Parseval Decompositions for Arbitrary-Source Degree-`M` Polynomial States -/

/-- Exact three-channel (`P₁`, `P₂`, `residualTwoProjector P₁ P₂`) vector and `hilbertEnergy`
Parseval decomposition for `arbitrarySourceDegreeMPolyState`. -/
theorem arbitrarySourceDegreeMPolyState_three_channel_parseval_decomposition
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    arbitrarySourceDegreeMPolyState M w b c PK =
      arbitrarySourceDegreeMPolyResponse P₁ M w b c PK +
      arbitrarySourceDegreeMPolyResponse P₂ M w b c PK +
      arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK ∧
    hilbertEnergy (arbitrarySourceDegreeMPolyState M w b c PK) =
      hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₁ M w b c PK) +
      hilbertEnergy (arbitrarySourceDegreeMPolyResponse P₂ M w b c PK) +
      hilbertEnergy (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) M w b c PK) := by
  unfold arbitrarySourceDegreeMPolyResponse
  have h3 := twoProjector_three_channel_parseval_decomposition hP
    (arbitrarySourceDegreeMPolyState M w b c PK)
  exact ⟨h3.1.symm, h3.2⟩

/-- Antipodal `n = 2` degree-1 three-channel (`P₁`, `P₂`, `residualTwoProjector P₁ P₂`)
projected formulas, norms, and `hilbertEnergy` Parseval decomposition. -/
theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_three_channel_package
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (c : Fin 2 → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyResponse P₁ 1 antipodalWeights antipodalSources c
        (identicalPackets ψ) = (2 * c 1) • P₁ ψ ∧
    arbitrarySourceDegreeMPolyResponse P₂ 1 antipodalWeights antipodalSources c
        (identicalPackets ψ) = (2 * c 1) • P₂ ψ ∧
    arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) 1 antipodalWeights
        antipodalSources c (identicalPackets ψ) = (2 * c 1) • residualTwoProjector P₁ P₂ ψ ∧
    hilbertEnergy
        (arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ)) =
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse P₁ 1 antipodalWeights antipodalSources c
          (identicalPackets ψ)) +
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse P₂ 1 antipodalWeights antipodalSources c
          (identicalPackets ψ)) +
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) 1 antipodalWeights
          antipodalSources c (identicalPackets ψ)) :=
  ⟨arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul P₁ c ψ,
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul P₂ c ψ,
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul (residualTwoProjector P₁ P₂) c ψ,
   (arbitrarySourceDegreeMPolyState_three_channel_parseval_decomposition hP 1
     antipodalWeights antipodalSources c (identicalPackets ψ)).2⟩

/-- Master Mutually Orthogonal Projector Three-Channel & `Q`-Channel Parseval Energy
Decomposition Synthesis. -/
theorem arbitrary_source_mutually_orthogonal_projector_parseval_master_synthesis
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    {Q : ℕ} (Pq : Fin Q → (E →L[ℂ] E))
    (hid : totalProjector Pq = ContinuousLinearMap.id ℂ E)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (c₁ : Fin 2 → ℂ) (ψ : E) :
    (IsOrthogonalProjection (P₁ + P₂) ∧
     IsOrthogonalProjection (residualTwoProjector P₁ P₂) ∧
     P₁ ψ + P₂ ψ + residualTwoProjector P₁ P₂ ψ = ψ) ∧
    (hilbertEnergy ψ =
       hilbertEnergy (P₁ ψ) + hilbertEnergy (P₂ ψ) +
         hilbertEnergy (residualTwoProjector P₁ P₂ ψ) ∧
     residualMultiProjector Pq = 0 ∧
     ∑ q : Fin Q, Pq q ψ = ψ) ∧
    (hilbertEnergy
       (arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
         (identicalPackets ψ)) =
       hilbertEnergy
         (arbitrarySourceDegreeMPolyResponse P₁ (M + 1) antipodalWeights antipodalSources c
           (identicalPackets ψ)) +
       hilbertEnergy
         (arbitrarySourceDegreeMPolyResponse P₂ (M + 1) antipodalWeights antipodalSources c
           (identicalPackets ψ)) +
       hilbertEnergy
         (arbitrarySourceDegreeMPolyResponse (residualTwoProjector P₁ P₂) (M + 1)
           antipodalWeights antipodalSources c (identicalPackets ψ)) ∧
     arbitrarySourceDegreeMPolyResponse P₁ 1 antipodalWeights antipodalSources c₁
       (identicalPackets ψ) = (2 * c₁ 1) • P₁ ψ ∧
     arbitrarySourceDegreeMPolyResponse P₂ 1 antipodalWeights antipodalSources c₁
       (identicalPackets ψ) = (2 * c₁ 1) • P₂ ψ) := by
  have hproj := isOrthogonalProjection_add_and_residual_of_mutuallyOrthogonal hP
  have h3 := twoProjector_three_channel_parseval_decomposition hP ψ
  have hcomp := resolution_of_identity_completeness Pq hid ψ
  have hpoly := arbitrarySourceDegreeMPolyState_three_channel_parseval_decomposition
    hP (M + 1) antipodalWeights antipodalSources c (identicalPackets ψ)
  have hant := arbitrarySourceDegreeMPolyState_antipodal_deg_one_three_channel_package hP c₁ ψ
  exact ⟨⟨hproj.1, hproj.2, h3.1⟩,
    ⟨h3.2, hcomp.1, hcomp.2.2⟩,
    ⟨hpoly.2, hant.1, hant.2.1⟩⟩

end MutuallyOrthogonalProjectorCalculus

#print axioms inner_of_mutuallyOrthogonalProjections_eq_zero
#print axioms isOrthogonalProjection_add_and_residual_of_mutuallyOrthogonal
#print axioms hilbertEnergy_add_of_mutuallyOrthogonalProjections
#print axioms twoProjector_three_channel_parseval_decomposition
#print axioms areMutuallyOrthogonalProjections_self_and_complementary
#print axioms totalProjector_apply_and_residual_split
#print axioms totalProjector_and_residual_hilbertEnergy_pythagorean
#print axioms resolution_of_identity_completeness
#print axioms totalProjector_isolate_channel_and_norm_bounds
#print axioms arbitrarySourceDegreeMPolyState_three_channel_parseval_decomposition
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_three_channel_package
#print axioms arbitrary_source_mutually_orthogonal_projector_parseval_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
