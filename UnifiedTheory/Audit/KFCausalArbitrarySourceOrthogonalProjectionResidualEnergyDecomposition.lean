/- Orthogonal Projection & Complementary Residual Decomposition (`P` and `I - P`),
Sesquilinear Inner-Product & `hilbertEnergy` Pythagorean Identities, Anchor-Mode vs.
Residual-Tail Decomposition, and Projected Multi-Mode Dominance Bounds for Arbitrary-Source
Degree-`M` Polynomial Superpositions:
1. Defines `IsOrthogonalProjection (P : E →L[ℂ] E)` (`(∀ x, P (P x) = P x) ∧ (∀ x y, inner ℂ (P x) y = inner ℂ x (P y))`)
   and the complementary projection `complementaryProjection P := id - P` on any complex
   inner product space `E`, proving:
   - Exact pointwise decomposition `P x + complementaryProjection P x = x`,
   - Mutual annihilation `P (complementaryProjection P x) = 0` and `complementaryProjection P (P x) = 0`,
   - Idempotency and self-adjointness of `complementaryProjection P` (`isOrthogonalProjection_complementary`),
   - Sesquilinear orthogonality `inner ℂ (P x) (complementaryProjection P y) = 0` and
     `inner ℂ (complementaryProjection P x) (P y) = 0`,
   - Exact sesquilinear Pythagorean identity
     `inner ℂ x y = inner ℂ (P x) (P y) + inner ℂ (complementaryProjection P x) (complementaryProjection P y)`,
   - Real inner-product energy `hilbertEnergy x := (inner ℂ x x).re` Pythagorean decomposition
     `hilbertEnergy x = hilbertEnergy (P x) + hilbertEnergy (complementaryProjection P x)`.
2. Applies orthogonal projections `P` and `complementaryProjection P` to arbitrary-source
   multi-packet states (`arbitrarySourceModeState`, `arbitrarySourceSuperpositionState`,
   and `arbitrarySourceDegreeMPolyState`), proving exact channel splitting, cross-channel
   inner-product vanishing, and `hilbertEnergy` additivity across all polynomial degrees `M`.
3. Establishes anchor-mode (`anchorModeComponent`) and residual-tail (`residualModeSum`)
   decompositions for `k₀ : Fin (M + 1)`, proving exact `hilbertEnergy` additivity under
   anchor-residual orthogonality, two-sided projected triangle bounds, and antipodal `n = 2`
   projected quadratic-mode dominance bounds. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition

noncomputable section

open scoped InnerProduct BigOperators
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceModeState arbitrarySourceSuperpositionState
   arbitrarySourceDegreeMPolyState isNeutralArbitrarySource
   antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceModeResponse arbitrarySourceSuperpositionResponse
   arbitrarySourceDegreeMPolyResponse
   arbitrarySourceModeResponse_eq_mode_of_map
   arbitrarySourceDegreeMPolyResponse_eq_poly_of_map
   arbitrarySourceDegreeMPolyState_isolate_mode
   arbitrarySourceDegreeMPolyResponse_isolate_mode
   arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_le
   arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_ge
   arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge
   arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_strict_pos
   arbitrarySourceDegreeMPolyResponse_antipodal_isolate_mode_one
   arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_norm_ge
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq)

/-! ### 1. Orthogonal Projections, Complementary Projections, and Sesquilinear Pythagorean Identities -/

section OrthogonalProjectionCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `P : E →L[ℂ] E` is an orthogonal projection if it is idempotent
(`∀ x, P (P x) = P x`) and symmetric with respect to the complex inner product
(`∀ x y, inner ℂ (P x) y = inner ℂ x (P y)`). -/
def IsOrthogonalProjection (P : E →L[ℂ] E) : Prop :=
  (∀ x : E, P (P x) = P x) ∧ (∀ x y : E, inner ℂ (P x) y = inner ℂ x (P y))

/-- The complementary continuous linear projection `I - P : E →L[ℂ] E`. -/
def complementaryProjection (P : E →L[ℂ] E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - P

/-- Real-valued inner-product energy `hilbertEnergy x := Re ⟨x, x⟩`. -/
def hilbertEnergy (x : E) : ℝ :=
  (inner ℂ x x).re

/-- Pointwise evaluation of `complementaryProjection P`. -/
theorem complementaryProjection_apply (P : E →L[ℂ] E) (x : E) :
    complementaryProjection P x = x - P x :=
  rfl

/-- Exact two-channel decomposition `P x + (I - P) x = x`. -/
theorem proj_add_complementaryProjection (P : E →L[ℂ] E) (x : E) :
    P x + complementaryProjection P x = x :=
  add_sub_cancel (P x) x

/-- Mutual annihilation `P ((I - P) x) = 0` and `(I - P) (P x) = 0` for an idempotent projection `P`. -/
theorem proj_and_complementaryProjection_annihilate
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) (x : E) :
    P (complementaryProjection P x) = 0 ∧
    complementaryProjection P (P x) = 0 := by
  refine ⟨?_, ?_⟩
  · change P (x - P x) = 0
    rw [map_sub, hP.1 x, sub_self]
  · change P x - P (P x) = 0
    rw [hP.1 x, sub_self]

/-- The complementary projection `I - P` is also an orthogonal projection. -/
theorem isOrthogonalProjection_complementary
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) :
    IsOrthogonalProjection (complementaryProjection P) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · change (x - P x) - P (x - P x) = x - P x
    rw [map_sub, hP.1 x, sub_self, sub_zero]
  · change inner ℂ (x - P x) y = inner ℂ x (y - P y)
    rw [inner_sub_left, inner_sub_right, hP.2 x y]

/-- Cross-channel sesquilinear orthogonality:
`inner ℂ (P x) ((I - P) y) = 0` and `inner ℂ ((I - P) x) (P y) = 0`. -/
theorem inner_proj_complementaryProjection_zero
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) (x y : E) :
    inner ℂ (P x) (complementaryProjection P y) = 0 ∧
    inner ℂ (complementaryProjection P x) (P y) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [hP.2 x (complementaryProjection P y),
      (proj_and_complementaryProjection_annihilate hP y).1, inner_zero_right]
  · have hC := isOrthogonalProjection_complementary hP
    rw [hC.2 x (P y), (proj_and_complementaryProjection_annihilate hP y).2, inner_zero_right]

/-- Exact sesquilinear Pythagorean decomposition:
`inner ℂ x y = inner ℂ (P x) (P y) + inner ℂ ((I - P) x) ((I - P) y)`. -/
theorem inner_orthogonalProjection_pythagorean
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) (x y : E) :
    inner ℂ x y =
      inner ℂ (P x) (P y) + inner ℂ (complementaryProjection P x) (complementaryProjection P y) := by
  have hC := isOrthogonalProjection_complementary hP
  have h1 : inner ℂ (P x) (P y) = inner ℂ x (P y) := by
    rw [hP.2 x (P y), hP.1 y]
  have h2 : inner ℂ (complementaryProjection P x) (complementaryProjection P y) =
      inner ℂ x (complementaryProjection P y) := by
    rw [hC.2 x (complementaryProjection P y), hC.1 y]
  rw [h1, h2, ← inner_add_right, proj_add_complementaryProjection P y]

/-- Exact `hilbertEnergy` Pythagorean identity for any orthogonal projection `P`:
`hilbertEnergy x = hilbertEnergy (P x) + hilbertEnergy ((I - P) x)`. -/
theorem hilbertEnergy_orthogonalProjection_pythagorean
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P) (x : E) :
    hilbertEnergy x =
      hilbertEnergy (P x) + hilbertEnergy (complementaryProjection P x) := by
  unfold hilbertEnergy
  rw [inner_orthogonalProjection_pythagorean hP x x, Complex.add_re]

/-- General `hilbertEnergy` additivity for any two orthogonal vectors `u, v : E`
satisfying `inner ℂ u v = 0` and `inner ℂ v u = 0`. -/
theorem hilbertEnergy_add_of_inner_eq_zero
    {u v : E} (huv : inner ℂ u v = 0) (hvu : inner ℂ v u = 0) :
    hilbertEnergy (u + v) = hilbertEnergy u + hilbertEnergy v := by
  unfold hilbertEnergy
  rw [inner_add_left, inner_add_right, inner_add_right, huv, hvu, add_zero, zero_add, Complex.add_re]

/-- Two-sided triangle and reverse-triangle norm bounds for `P x` and `(I - P) x`. -/
theorem orthogonalProjection_norm_triangle_bounds (P : E →L[ℂ] E) (x : E) :
    ‖P x‖ - ‖complementaryProjection P x‖ ≤ ‖x‖ ∧
    ‖complementaryProjection P x‖ - ‖P x‖ ≤ ‖x‖ ∧
    ‖x‖ ≤ ‖P x‖ + ‖complementaryProjection P x‖ := by
  have hle : ‖x‖ ≤ ‖P x‖ + ‖complementaryProjection P x‖ := by
    have h := norm_add_le (P x) (complementaryProjection P x)
    rwa [proj_add_complementaryProjection P x] at h
  have hge1 : ‖P x‖ ≤ ‖x‖ + ‖complementaryProjection P x‖ := by
    have h := norm_le_add_norm_add (P x) (complementaryProjection P x)
    rwa [proj_add_complementaryProjection P x] at h
  have hge2 : ‖complementaryProjection P x‖ ≤ ‖x‖ + ‖P x‖ := by
    have h := norm_le_add_norm_add (complementaryProjection P x) (P x)
    rw [add_comm (complementaryProjection P x) (P x), proj_add_complementaryProjection P x] at h
    exact h
  exact ⟨by linarith, by linarith, hle⟩

/-! ### 2. Projected Arbitrary-Source Multi-Packet Mode and Degree-`M` Polynomial States -/

/-- Exact decomposition of `arbitrarySourceModeState` into its projected `P`-channel and
complementary `(I - P)`-channel responses, with cross-channel orthogonality and
`hilbertEnergy` Pythagorean additivity. -/
theorem arbitrarySourceModeState_orthogonalProjection_decomposition
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P)
    {n : ℕ} (w b : Fin n → ℂ) (k : ℕ) (PK : Fin n → E) :
    arbitrarySourceModeState w b k PK =
      arbitrarySourceModeResponse P w b k PK +
        arbitrarySourceModeResponse (complementaryProjection P) w b k PK ∧
    inner ℂ (arbitrarySourceModeResponse P w b k PK)
      (arbitrarySourceModeResponse (complementaryProjection P) w b k PK) = 0 ∧
    hilbertEnergy (arbitrarySourceModeState w b k PK) =
      hilbertEnergy (arbitrarySourceModeResponse P w b k PK) +
        hilbertEnergy (arbitrarySourceModeResponse (complementaryProjection P) w b k PK) := by
  unfold arbitrarySourceModeResponse
  exact ⟨(proj_add_complementaryProjection P _).symm,
    (inner_proj_complementaryProjection_zero hP _ _).1,
    hilbertEnergy_orthogonalProjection_pythagorean hP _⟩

/-- Exact decomposition of `arbitrarySourceDegreeMPolyState` into its projected `P`-channel and
complementary `(I - P)`-channel responses, with cross-channel orthogonality and
`hilbertEnergy` Pythagorean additivity. -/
theorem arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P)
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ) (PK : Fin n → E) :
    arbitrarySourceDegreeMPolyState M w b c PK =
      arbitrarySourceDegreeMPolyResponse P M w b c PK +
        arbitrarySourceDegreeMPolyResponse (complementaryProjection P) M w b c PK ∧
    inner ℂ (arbitrarySourceDegreeMPolyResponse P M w b c PK)
      (arbitrarySourceDegreeMPolyResponse (complementaryProjection P) M w b c PK) = 0 ∧
    hilbertEnergy (arbitrarySourceDegreeMPolyState M w b c PK) =
      hilbertEnergy (arbitrarySourceDegreeMPolyResponse P M w b c PK) +
        hilbertEnergy (arbitrarySourceDegreeMPolyResponse (complementaryProjection P) M w b c PK) := by
  unfold arbitrarySourceDegreeMPolyResponse
  exact ⟨(proj_add_complementaryProjection P _).symm,
    (inner_proj_complementaryProjection_zero hP _ _).1,
    hilbertEnergy_orthogonalProjection_pythagorean hP _⟩

/-- Both `P` and `complementaryProjection P` preserve neutrality of arbitrary-source
packet configurations (`isNeutralArbitrarySource w b PK`). -/
theorem isNeutralArbitrarySource_preserved_by_projection_and_complement
    (P : E →L[ℂ] E) {n : ℕ} (w b : Fin n → ℂ) (PK : Fin n → E)
    (hneutral : isNeutralArbitrarySource w b PK) :
    isNeutralArbitrarySource w b (fun i => P (PK i)) ∧
    isNeutralArbitrarySource w b (fun i => complementaryProjection P (PK i)) := by
  unfold isNeutralArbitrarySource at hneutral ⊢
  unfold arbitrarySourceSuperpositionState at hneutral ⊢
  refine ⟨?_, ?_⟩
  · have hmap : ∑ i : Fin n, (w i * b i) • P (PK i) =
        P (∑ i : Fin n, (w i * b i) • PK i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (P.map_smul (w i * b i) (PK i)).symm
    rw [hmap, hneutral, map_zero]
  · have hmap : ∑ i : Fin n, (w i * b i) • complementaryProjection P (PK i) =
        complementaryProjection P (∑ i : Fin n, (w i * b i) • PK i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact ((complementaryProjection P).map_smul (w i * b i) (PK i)).symm
    rw [hmap, hneutral, map_zero]

/-! ### 3. Anchor-Mode vs. Residual-Tail Decomposition and Projected Dominance Bounds -/

/-- The isolated anchor-mode vector `c k₀ • arbitrarySourceModeState w b k₀ PK`. -/
def anchorModeComponent
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (PK : Fin n → E) (k₀ : Fin (M + 1)) : E :=
  c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) PK

/-- The residual multi-mode tail sum `∑_{k ≠ k₀} c k • arbitrarySourceModeState w b k PK`. -/
def residualModeSum
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (PK : Fin n → E) (k₀ : Fin (M + 1)) : E :=
  ∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) PK

/-- Exact decomposition of `arbitrarySourceDegreeMPolyState` into `anchorModeComponent + residualModeSum`
and exact `hilbertEnergy` additivity when the anchor mode is orthogonal to the residual sum. -/
theorem arbitrarySourceDegreeMPolyState_anchor_residual_energy_decomposition
    {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (PK : Fin n → E) (k₀ : Fin (M + 1))
    (horth1 : inner ℂ (anchorModeComponent M w b c PK k₀) (residualModeSum M w b c PK k₀) = 0)
    (horth2 : inner ℂ (residualModeSum M w b c PK k₀) (anchorModeComponent M w b c PK k₀) = 0) :
    arbitrarySourceDegreeMPolyState M w b c PK =
      anchorModeComponent M w b c PK k₀ + residualModeSum M w b c PK k₀ ∧
    hilbertEnergy (arbitrarySourceDegreeMPolyState M w b c PK) =
      hilbertEnergy (anchorModeComponent M w b c PK k₀) +
        hilbertEnergy (residualModeSum M w b c PK k₀) := by
  have hsplit :
      arbitrarySourceDegreeMPolyState M w b c PK =
        anchorModeComponent M w b c PK k₀ + residualModeSum M w b c PK k₀ :=
    arbitrarySourceDegreeMPolyState_isolate_mode M w b c PK k₀
  refine ⟨hsplit, ?_⟩
  rw [hsplit]
  exact hilbertEnergy_add_of_inner_eq_zero horth1 horth2

/-- Projected anchor-mode dominance lower bound in both the `P`-channel and the
complementary `(I - P)`-channel. -/
theorem arbitrarySourceDegreeMPolyResponse_projected_and_complementary_dominance
    (P : E →L[ℂ] E) {n : ℕ} (M : ℕ) (w b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (PK : Fin n → E) (k₀ : Fin (M + 1)) (θP θQ : ℝ)
    (hdomP : ∑ k ∈ Finset.univ.erase k₀,
        ‖c k‖ * ‖arbitrarySourceModeResponse P w b (k : ℕ) PK‖ ≤
      θP * (‖c k₀‖ * ‖arbitrarySourceModeResponse P w b (k₀ : ℕ) PK‖))
    (hdomQ : ∑ k ∈ Finset.univ.erase k₀,
        ‖c k‖ * ‖arbitrarySourceModeResponse (complementaryProjection P) w b (k : ℕ) PK‖ ≤
      θQ * (‖c k₀‖ * ‖arbitrarySourceModeResponse (complementaryProjection P) w b (k₀ : ℕ) PK‖)) :
    (1 - θP) * (‖c k₀‖ * ‖arbitrarySourceModeResponse P w b (k₀ : ℕ) PK‖) ≤
      ‖arbitrarySourceDegreeMPolyResponse P M w b c PK‖ ∧
    (1 - θQ) * (‖c k₀‖ * ‖arbitrarySourceModeResponse (complementaryProjection P) w b (k₀ : ℕ) PK‖) ≤
      ‖arbitrarySourceDegreeMPolyResponse (complementaryProjection P) M w b c PK‖ :=
  ⟨arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge P M w b c PK k₀ θP hdomP,
   arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge
     (complementaryProjection P) M w b c PK k₀ θQ hdomQ⟩

/-- Antipodal `n = 2` degree-1 projected and complementary responses:
exact `(2 * c 1) • P ψ` and `(2 * c 1) • (I - P) ψ` formulas, norm identities, and
`hilbertEnergy` Pythagorean decomposition. -/
theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_projected_decomposition
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P)
    (c : Fin 2 → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c
        (identicalPackets ψ) = (2 * c 1) • P ψ ∧
    arbitrarySourceDegreeMPolyResponse (complementaryProjection P) 1 antipodalWeights
        antipodalSources c (identicalPackets ψ) = (2 * c 1) • complementaryProjection P ψ ∧
    ‖arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ = 2 * ‖c 1‖ * ‖P ψ‖ ∧
    ‖arbitrarySourceDegreeMPolyResponse (complementaryProjection P) 1 antipodalWeights
        antipodalSources c (identicalPackets ψ)‖ = 2 * ‖c 1‖ * ‖complementaryProjection P ψ‖ ∧
    hilbertEnergy
        (arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ)) =
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c
          (identicalPackets ψ)) +
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse (complementaryProjection P) 1 antipodalWeights
          antipodalSources c (identicalPackets ψ)) :=
  ⟨arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul P c ψ,
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul
     (complementaryProjection P) c ψ,
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq P c ψ,
   arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq
     (complementaryProjection P) c ψ,
   (arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition hP 1
     antipodalWeights antipodalSources c (identicalPackets ψ)).2.2⟩

/-- Master Orthogonal Projection, Complementary Residual Energy Decomposition,
and Antipodal Multi-Mode Synthesis. -/
theorem arbitrary_source_orthogonal_projection_residual_energy_master_synthesis
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (c₁ : Fin 2 → ℂ) (ψ : E) :
    (IsOrthogonalProjection (complementaryProjection P) ∧
     P (complementaryProjection P ψ) = 0 ∧
     complementaryProjection P (P ψ) = 0 ∧
     inner ℂ (P ψ) (complementaryProjection P ψ) = 0 ∧
     hilbertEnergy ψ = hilbertEnergy (P ψ) + hilbertEnergy (complementaryProjection P ψ)) ∧
    (arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ) =
      arbitrarySourceDegreeMPolyResponse P (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ) +
      arbitrarySourceDegreeMPolyResponse (complementaryProjection P) (M + 1)
        antipodalWeights antipodalSources c (identicalPackets ψ) ∧
     hilbertEnergy
        (arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
          (identicalPackets ψ)) =
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse P (M + 1) antipodalWeights antipodalSources c
          (identicalPackets ψ)) +
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse (complementaryProjection P) (M + 1)
          antipodalWeights antipodalSources c (identicalPackets ψ))) ∧
    (arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c₁
        (identicalPackets ψ) = (2 * c₁ 1) • P ψ ∧
     ‖arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c₁
        (identicalPackets ψ)‖ = 2 * ‖c₁ 1‖ * ‖P ψ‖) := by
  have hpoly := arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition
    hP (M + 1) antipodalWeights antipodalSources c (identicalPackets ψ)
  exact ⟨⟨isOrthogonalProjection_complementary hP,
          (proj_and_complementaryProjection_annihilate hP ψ).1,
          (proj_and_complementaryProjection_annihilate hP ψ).2,
          (inner_proj_complementaryProjection_zero hP ψ ψ).1,
          hilbertEnergy_orthogonalProjection_pythagorean hP ψ⟩,
         ⟨hpoly.1, hpoly.2.2⟩,
         ⟨arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul P c₁ ψ,
          arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq P c₁ ψ⟩⟩

end OrthogonalProjectionCalculus

#print axioms complementaryProjection_apply
#print axioms proj_add_complementaryProjection
#print axioms proj_and_complementaryProjection_annihilate
#print axioms isOrthogonalProjection_complementary
#print axioms inner_proj_complementaryProjection_zero
#print axioms inner_orthogonalProjection_pythagorean
#print axioms hilbertEnergy_orthogonalProjection_pythagorean
#print axioms hilbertEnergy_add_of_inner_eq_zero
#print axioms orthogonalProjection_norm_triangle_bounds
#print axioms arbitrarySourceModeState_orthogonalProjection_decomposition
#print axioms arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition
#print axioms isNeutralArbitrarySource_preserved_by_projection_and_complement
#print axioms arbitrarySourceDegreeMPolyState_anchor_residual_energy_decomposition
#print axioms arbitrarySourceDegreeMPolyResponse_projected_and_complementary_dominance
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_projected_decomposition
#print axioms arbitrary_source_orthogonal_projection_residual_energy_master_synthesis

end

end UnifiedTheory.Audit.KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
