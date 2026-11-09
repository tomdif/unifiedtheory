/- Multi-mode decomposition and anchor-mode dominance bounds for arbitrary-source
(`b : Fin n → ℂ`) degree-`M` polynomial superpositions: exact reduction to higher
source-moment modes `k ≥ 1` under neutral constant-mode configurations
(`isNeutralArbitrarySource w b P`), general anchor-mode isolation (`k₀ : Fin (M + 1)`)
via `Finset.univ.erase k₀`, two-sided triangle and reverse-triangle bounds,
strict positivity under dominant quadratic-source modes (`k₀ = 1`) for the
antipodal `n = 2` witness `w = ![1, 1], b = ![1, -1]`, and continuous linear
response operator (`R : E →L[ℂ] F`) mode decomposition and dominance bounds. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
noncomputable section
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
  (unitMonomialPolyProfile)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (factoredPolyProfile degreeMPolyProfile)
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceModeState arbitrarySourceSuperpositionState
   arbitrarySourceDegreeMPolyState isNeutralArbitrarySource
   antipodalWeights antipodalSources identicalPackets
   arbitrarySourceModeState_zero_eq_superposition
   antipodal_is_neutral_arbitrary_source
   antipodal_mode_one_eq_two_smul
   antipodal_mode_one_norm_eq_two_mul
   arbitrarySourceDegreeMPolyState_split_zero)

/-! ### 1. Neutral Constant-Mode Recovery and Reduction to Higher Source-Moment Modes -/

theorem arbitrarySourceModeState_zero_of_neutral
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E)
    (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceModeState w b 0 P = 0 := by
  rw [arbitrarySourceModeState_zero_eq_superposition]
  exact hneutral

theorem arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceDegreeMPolyState M w b c P =
      ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P := by
  rw [arbitrarySourceDegreeMPolyState_split_zero,
      arbitrarySourceModeState_zero_of_neutral w b P hneutral,
      smul_zero, zero_add]

theorem arbitrarySourceDegreeMPolyState_antipodal_eq_higher_modes
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ) (c : Fin (M + 1) → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyState M antipodalWeights antipodalSources c (identicalPackets ψ) =
      ∑ r : Fin M,
        c r.succ • arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 1)
          (identicalPackets ψ) :=
  arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral M
    antipodalWeights antipodalSources c (identicalPackets ψ)
    (antipodal_is_neutral_arbitrary_source ψ)

theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_eq_two_smul
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Fin 2 → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ) =
      (2 * c 1) • ψ := by
  rw [arbitrarySourceDegreeMPolyState_antipodal_eq_higher_modes 1 c ψ, Fin.sum_univ_one]
  change c 1 • arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ) =
    (2 * c 1) • ψ
  rw [antipodal_mode_one_eq_two_smul ψ, smul_smul, mul_comm]

theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_eq
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Fin 2 → ℂ) (ψ : E) :
    ‖arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ)‖ =
      2 * ‖c 1‖ * ‖ψ‖ := by
  rw [arbitrarySourceDegreeMPolyState_antipodal_deg_one_eq_two_smul, norm_smul, norm_mul]
  simp

theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Fin 2 → ℂ) (ψ : E) (hc1 : c 1 ≠ 0) (hψ : ψ ≠ 0) :
    arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ) ≠ 0 := by
  intro hzero
  have hnorm :
      ‖arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ)‖ = 0 := by
    rw [hzero, norm_zero]
  rw [arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_eq] at hnorm
  have hc1_pos : 0 < ‖c 1‖ := norm_pos_iff.mpr hc1
  have hψ_pos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hprod : 0 < 2 * ‖c 1‖ * ‖ψ‖ := by positivity
  linarith

theorem arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_sq_eq
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Fin 2 → ℂ) (ψ : E) :
    ‖arbitrarySourceDegreeMPolyState 1 antipodalWeights antipodalSources c (identicalPackets ψ)‖ ^ 2 =
      4 * ‖c 1‖ ^ 2 * ‖ψ‖ ^ 2 := by
  rw [arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_eq]
  ring

theorem antipodal_mode_one_norm_sq_eq_four_mul
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    ‖arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ)‖ ^ 2 =
      4 * ‖ψ‖ ^ 2 := by
  rw [antipodal_mode_one_norm_eq_two_mul]
  ring

theorem antipodal_mode_one_norm_sq_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) (hψ : ψ ≠ 0) :
    0 < ‖arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ)‖ ^ 2 := by
  rw [antipodal_mode_one_norm_sq_eq_four_mul]
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  positivity

/-! ### 2. General Anchor-Mode Isolation (`k₀ : Fin (M + 1)`) and Dominant-Mode Positivity -/

theorem arbitrarySourceDegreeMPolyState_isolate_mode
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    arbitrarySourceDegreeMPolyState M w b c P =
      c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) P +
        ∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P := by
  unfold arbitrarySourceDegreeMPolyState
  exact (Finset.add_sum_erase Finset.univ
    (fun k : Fin (M + 1) => c k • arbitrarySourceModeState w b (k : ℕ) P)
    (Finset.mem_univ k₀)).symm

theorem arbitrarySourceDegreeMPolyState_isolate_mode_norm_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    ‖arbitrarySourceDegreeMPolyState M w b c P‖ ≤
      ‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖ +
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ := by
  rw [arbitrarySourceDegreeMPolyState_isolate_mode M w b c P k₀]
  have h1 : ‖c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) P +
      ∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ ≤
    ‖c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) P‖ +
      ‖∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ :=
    norm_add_le _ _
  have h2 : ‖∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      ∑ k ∈ Finset.univ.erase k₀, ‖c k • arbitrarySourceModeState w b (k : ℕ) P‖ :=
    norm_sum_le (Finset.univ.erase k₀) _
  simp only [norm_smul] at h1 h2
  linarith

theorem arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    ‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖ -
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      ‖arbitrarySourceDegreeMPolyState M w b c P‖ := by
  rw [arbitrarySourceDegreeMPolyState_isolate_mode M w b c P k₀]
  have h1 : ‖c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) P‖ ≤
      ‖c k₀ • arbitrarySourceModeState w b (k₀ : ℕ) P +
        ∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ +
      ‖∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ :=
    norm_le_add_norm_add _ _
  have h2 : ‖∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      ∑ k ∈ Finset.univ.erase k₀, ‖c k • arbitrarySourceModeState w b (k : ℕ) P‖ :=
    norm_sum_le (Finset.univ.erase k₀) _
  simp only [norm_smul] at h1 h2
  linarith

theorem arbitrarySourceDegreeMPolyState_isolate_mode_two_sided_bounds
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖ -
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      ‖arbitrarySourceDegreeMPolyState M w b c P‖) ∧
    (‖arbitrarySourceDegreeMPolyState M w b c P‖ ≤
      ‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖ +
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖) :=
  ⟨arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge M w b c P k₀,
   arbitrarySourceDegreeMPolyState_isolate_mode_norm_le M w b c P k₀⟩

theorem arbitrarySourceDegreeMPolyState_dominant_anchor_mode_norm_ge
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) (θ : ℝ)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)) :
    (1 - θ) * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖) ≤
      ‖arbitrarySourceDegreeMPolyState M w b c P‖ := by
  have hge := arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge M w b c P k₀
  linarith

theorem arbitrarySourceDegreeMPolyState_dominant_anchor_mode_strict_pos
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)) :
    0 < ‖arbitrarySourceDegreeMPolyState M w b c P‖ := by
  have hge := arbitrarySourceDegreeMPolyState_dominant_anchor_mode_norm_ge M w b c P k₀ θ hdom
  have hmul : 0 < (1 - θ) * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖) :=
    mul_pos (by linarith) hpos
  linarith

theorem arbitrarySourceDegreeMPolyState_dominant_anchor_mode_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)) :
    arbitrarySourceDegreeMPolyState M w b c P ≠ 0 :=
  norm_pos_iff.mp
    (arbitrarySourceDegreeMPolyState_dominant_anchor_mode_strict_pos M w b c P k₀ θ hθ hpos hdom)

theorem arbitrarySourceDegreeMPolyState_neutral_isolate_mode_one
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 2) → ℂ)
    (P : Fin n → E) (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceDegreeMPolyState (M + 1) w b c P =
      c 1 • arbitrarySourceModeState w b 1 P +
        ∑ r : Fin M, c r.succ.succ • arbitrarySourceModeState w b ((r : ℕ) + 2) P := by
  rw [arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral (M + 1) w b c P hneutral,
      Fin.sum_univ_succ]
  rfl

theorem arbitrarySourceDegreeMPolyState_antipodal_isolate_mode_one
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c (identicalPackets ψ) =
      (2 * c 1) • ψ +
        ∑ r : Fin M,
          c r.succ.succ •
            arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
              (identicalPackets ψ) := by
  rw [arbitrarySourceDegreeMPolyState_neutral_isolate_mode_one M
        antipodalWeights antipodalSources c (identicalPackets ψ)
        (antipodal_is_neutral_arbitrary_source ψ),
      antipodal_mode_one_eq_two_smul ψ, smul_smul, mul_comm]

theorem arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_norm_ge
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖c r.succ.succ •
          arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
            (identicalPackets ψ)‖ ≤
      θ * (2 * ‖c 1‖ * ‖ψ‖)) :
    (1 - θ) * (2 * ‖c 1‖ * ‖ψ‖) ≤
      ‖arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ := by
  rw [arbitrarySourceDegreeMPolyState_antipodal_isolate_mode_one M c ψ]
  have h1 : ‖(2 * c 1) • ψ‖ ≤
      ‖(2 * c 1) • ψ +
        ∑ r : Fin M,
          c r.succ.succ •
            arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
              (identicalPackets ψ)‖ +
      ‖∑ r : Fin M,
        c r.succ.succ •
          arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
            (identicalPackets ψ)‖ :=
    norm_le_add_norm_add _ _
  have h2 : ‖∑ r : Fin M,
      c r.succ.succ •
        arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
          (identicalPackets ψ)‖ ≤
    ∑ r : Fin M,
      ‖c r.succ.succ •
        arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
          (identicalPackets ψ)‖ :=
    norm_sum_le Finset.univ _
  have h3 : ‖(2 * c 1) • ψ‖ = 2 * ‖c 1‖ * ‖ψ‖ := by
    rw [norm_smul, norm_mul]
    simp
  linarith

theorem arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_strict_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) (θ : ℝ) (hθ : θ < 1)
    (hc1 : c 1 ≠ 0) (hψ : ψ ≠ 0)
    (hdom : ∑ r : Fin M,
        ‖c r.succ.succ •
          arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
            (identicalPackets ψ)‖ ≤
      θ * (2 * ‖c 1‖ * ‖ψ‖)) :
    0 < ‖arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ := by
  have hge := arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_norm_ge M c ψ θ hdom
  have hc1_pos : 0 < ‖c 1‖ := norm_pos_iff.mpr hc1
  have hψ_pos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hpos : 0 < 2 * ‖c 1‖ * ‖ψ‖ := by positivity
  have hmul : 0 < (1 - θ) * (2 * ‖c 1‖ * ‖ψ‖) := mul_pos (by linarith) hpos
  linarith

/-! ### 3. Continuous Linear Multi-Packet Response Maps (`R : E →L[ℂ] F`) and Mode Dominance -/

def arbitrarySourceModeResponse
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (k : ℕ) (P : Fin n → E) : F :=
  R (arbitrarySourceModeState w b k P)

def arbitrarySourceSuperpositionResponse
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E) : F :=
  R (arbitrarySourceSuperpositionState w b P)

def arbitrarySourceDegreeMPolyResponse
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) : F :=
  R (arbitrarySourceDegreeMPolyState M w b c P)

theorem arbitrarySourceModeResponse_eq_mode_of_map
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (k : ℕ) (P : Fin n → E) :
    arbitrarySourceModeResponse R w b k P =
      arbitrarySourceModeState w b k (fun i => R (P i)) := by
  unfold arbitrarySourceModeResponse arbitrarySourceModeState
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact R.map_smul (w i * b i ^ (k + 1)) (P i)

theorem arbitrarySourceSuperpositionResponse_eq_superposition_of_map
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E) :
    arbitrarySourceSuperpositionResponse R w b P =
      arbitrarySourceSuperpositionState w b (fun i => R (P i)) := by
  unfold arbitrarySourceSuperpositionResponse arbitrarySourceSuperpositionState
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact R.map_smul (w i * b i) (P i)

theorem arbitrarySourceDegreeMPolyResponse_eq_sum_modes
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    arbitrarySourceDegreeMPolyResponse R M w b c P =
      ∑ k : Fin (M + 1), c k • arbitrarySourceModeResponse R w b (k : ℕ) P := by
  unfold arbitrarySourceDegreeMPolyResponse arbitrarySourceDegreeMPolyState
    arbitrarySourceModeResponse
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact R.map_smul (c k) _

theorem arbitrarySourceDegreeMPolyResponse_eq_poly_of_map
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    arbitrarySourceDegreeMPolyResponse R M w b c P =
      arbitrarySourceDegreeMPolyState M w b c (fun i => R (P i)) := by
  rw [arbitrarySourceDegreeMPolyResponse_eq_sum_modes]
  unfold arbitrarySourceDegreeMPolyState
  apply Finset.sum_congr rfl
  intro k _
  rw [arbitrarySourceModeResponse_eq_mode_of_map]

theorem arbitrarySourceSuperpositionResponse_zero_of_neutral
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E)
    (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceSuperpositionResponse R w b P = 0 := by
  unfold arbitrarySourceSuperpositionResponse
  rw [hneutral, map_zero]

theorem arbitrarySourceDegreeMPolyResponse_eq_higher_modes_of_neutral
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceDegreeMPolyResponse R M w b c P =
      ∑ r : Fin M, c r.succ • arbitrarySourceModeResponse R w b ((r : ℕ) + 1) P := by
  unfold arbitrarySourceDegreeMPolyResponse arbitrarySourceModeResponse
  rw [arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral M w b c P hneutral, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact R.map_smul (c r.succ) _

theorem arbitrarySourceDegreeMPolyResponse_isolate_mode
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    arbitrarySourceDegreeMPolyResponse R M w b c P =
      c k₀ • arbitrarySourceModeResponse R w b (k₀ : ℕ) P +
        ∑ k ∈ Finset.univ.erase k₀, c k • arbitrarySourceModeResponse R w b (k : ℕ) P := by
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map,
      arbitrarySourceDegreeMPolyState_isolate_mode M w b c (fun i => R (P i)) k₀]
  simp only [arbitrarySourceModeResponse_eq_mode_of_map]

theorem arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_le
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    ‖arbitrarySourceDegreeMPolyResponse R M w b c P‖ ≤
      ‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖ +
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeResponse R w b (k : ℕ) P‖ := by
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map]
  simpa only [arbitrarySourceModeResponse_eq_mode_of_map] using
    arbitrarySourceDegreeMPolyState_isolate_mode_norm_le M w b c (fun i => R (P i)) k₀

theorem arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_ge
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) :
    ‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖ -
        ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeResponse R w b (k : ℕ) P‖ ≤
      ‖arbitrarySourceDegreeMPolyResponse R M w b c P‖ := by
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map]
  simpa only [arbitrarySourceModeResponse_eq_mode_of_map] using
    arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge M w b c (fun i => R (P i)) k₀

theorem arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) (θ : ℝ)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeResponse R w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖)) :
    (1 - θ) * (‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖) ≤
      ‖arbitrarySourceDegreeMPolyResponse R M w b c P‖ := by
  have hge := arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_ge R M w b c P k₀
  linarith

theorem arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_strict_pos
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (k₀ : Fin (M + 1)) (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeResponse R w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖)) :
    0 < ‖arbitrarySourceDegreeMPolyResponse R M w b c P‖ := by
  have hge := arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge R M w b c P k₀ θ hdom
  have hmul : 0 < (1 - θ) * (‖c k₀‖ * ‖arbitrarySourceModeResponse R w b (k₀ : ℕ) P‖) :=
    mul_pos (by linarith) hpos
  linarith

theorem arbitrarySourceDegreeMPolyResponse_antipodal_isolate_mode_one
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyResponse R (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ) =
      (2 * c 1) • R ψ +
        ∑ r : Fin M,
          c r.succ.succ •
            arbitrarySourceModeResponse R antipodalWeights antipodalSources ((r : ℕ) + 2)
              (identicalPackets ψ) := by
  have hid : (fun i : Fin 2 => R (identicalPackets ψ i)) = identicalPackets (R ψ) := rfl
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map, hid,
      arbitrarySourceDegreeMPolyState_antipodal_isolate_mode_one M c (R ψ)]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [arbitrarySourceModeResponse_eq_mode_of_map, hid]

theorem arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_norm_ge
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖c r.succ.succ •
          arbitrarySourceModeResponse R antipodalWeights antipodalSources ((r : ℕ) + 2)
            (identicalPackets ψ)‖ ≤
      θ * (2 * ‖c 1‖ * ‖R ψ‖)) :
    (1 - θ) * (2 * ‖c 1‖ * ‖R ψ‖) ≤
      ‖arbitrarySourceDegreeMPolyResponse R (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ := by
  have hid : (fun i : Fin 2 => R (identicalPackets ψ i)) = identicalPackets (R ψ) := rfl
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map, hid]
  apply arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_norm_ge M c (R ψ) θ
  simpa only [arbitrarySourceModeResponse_eq_mode_of_map, hid] using hdom

theorem arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_strict_pos
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) (θ : ℝ) (hθ : θ < 1)
    (hc1 : c 1 ≠ 0) (hRψ : R ψ ≠ 0)
    (hdom : ∑ r : Fin M,
        ‖c r.succ.succ •
          arbitrarySourceModeResponse R antipodalWeights antipodalSources ((r : ℕ) + 2)
            (identicalPackets ψ)‖ ≤
      θ * (2 * ‖c 1‖ * ‖R ψ‖)) :
    0 < ‖arbitrarySourceDegreeMPolyResponse R (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ := by
  have hge :=
    arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_norm_ge R M c ψ θ hdom
  have hc1_pos : 0 < ‖c 1‖ := norm_pos_iff.mpr hc1
  have hRψ_pos : 0 < ‖R ψ‖ := norm_pos_iff.mpr hRψ
  have hpos : 0 < 2 * ‖c 1‖ * ‖R ψ‖ := by positivity
  have hmul : 0 < (1 - θ) * (2 * ‖c 1‖ * ‖R ψ‖) := mul_pos (by linarith) hpos
  linarith

theorem arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) (c : Fin 2 → ℂ) (ψ : E) :
    arbitrarySourceDegreeMPolyResponse R 1 antipodalWeights antipodalSources c
        (identicalPackets ψ) =
      (2 * c 1) • R ψ := by
  have hid : (fun i : Fin 2 => R (identicalPackets ψ i)) = identicalPackets (R ψ) := rfl
  rw [arbitrarySourceDegreeMPolyResponse_eq_poly_of_map, hid,
      arbitrarySourceDegreeMPolyState_antipodal_deg_one_eq_two_smul c (R ψ)]

theorem arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (R : E →L[ℂ] F) (c : Fin 2 → ℂ) (ψ : E) :
    ‖arbitrarySourceDegreeMPolyResponse R 1 antipodalWeights antipodalSources c
        (identicalPackets ψ)‖ =
      2 * ‖c 1‖ * ‖R ψ‖ := by
  rw [arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul, norm_smul, norm_mul]
  simp

theorem scaleAmplitude_antipodal_linear_sum_zero (c₀ : ℂ) :
    ∑ i : Fin 2, scaleAmplitude antipodalWeights (fun _ => c₀) i * antipodalSources i = 0 := by
  simp [Fin.sum_univ_two, scaleAmplitude, antipodalWeights, antipodalSources]

theorem degreeMPolyProfile_zero_eq_constant {n : ℕ} (c₀ : Fin n → ℂ)
    (d : Fin 0 → Fin n → ℂ) (i : Fin n) :
    degreeMPolyProfile 0 c₀ d i = factoredPolyProfile c₀ (unitMonomialPolyProfile n 0 i) i := by
  simp [degreeMPolyProfile, factoredPolyProfile, unitMonomialPolyProfile]

theorem arbitrary_source_multi_mode_orthogonal_decomposition_master_synthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ) (c : Fin (M + 2) → ℂ) (ψ : E) (hψ : ψ ≠ 0) :
    (arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ) =
      (2 * c 1) • ψ +
        ∑ r : Fin M,
          c r.succ.succ •
            arbitrarySourceModeState antipodalWeights antipodalSources ((r : ℕ) + 2)
              (identicalPackets ψ)) ∧
    (0 < ‖arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ)‖ ^ 2) ∧
    (∀ k₀ : Fin (M + 2),
      ‖c k₀‖ * ‖arbitrarySourceModeState antipodalWeights antipodalSources (k₀ : ℕ)
          (identicalPackets ψ)‖ -
        ∑ k ∈ Finset.univ.erase k₀,
          ‖c k‖ * ‖arbitrarySourceModeState antipodalWeights antipodalSources (k : ℕ)
            (identicalPackets ψ)‖ ≤
      ‖arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
        (identicalPackets ψ)‖) ∧
    (∑ i : Fin 2, scaleAmplitude antipodalWeights (fun _ => c 0) i * antipodalSources i = 0) :=
  ⟨arbitrarySourceDegreeMPolyState_antipodal_isolate_mode_one M c ψ,
   antipodal_mode_one_norm_sq_pos ψ hψ,
   fun k₀ => arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge (M + 1)
     antipodalWeights antipodalSources c (identicalPackets ψ) k₀,
   scaleAmplitude_antipodal_linear_sum_zero (c 0)⟩

#print axioms arbitrarySourceModeState_zero_of_neutral
#print axioms arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral
#print axioms arbitrarySourceDegreeMPolyState_antipodal_eq_higher_modes
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_eq_two_smul
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_eq
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_nonzero
#print axioms arbitrarySourceDegreeMPolyState_antipodal_deg_one_norm_sq_eq
#print axioms antipodal_mode_one_norm_sq_eq_four_mul
#print axioms antipodal_mode_one_norm_sq_pos
#print axioms arbitrarySourceDegreeMPolyState_isolate_mode
#print axioms arbitrarySourceDegreeMPolyState_isolate_mode_norm_le
#print axioms arbitrarySourceDegreeMPolyState_isolate_mode_norm_ge
#print axioms arbitrarySourceDegreeMPolyState_isolate_mode_two_sided_bounds
#print axioms arbitrarySourceDegreeMPolyState_dominant_anchor_mode_norm_ge
#print axioms arbitrarySourceDegreeMPolyState_dominant_anchor_mode_strict_pos
#print axioms arbitrarySourceDegreeMPolyState_dominant_anchor_mode_nonzero
#print axioms arbitrarySourceDegreeMPolyState_neutral_isolate_mode_one
#print axioms arbitrarySourceDegreeMPolyState_antipodal_isolate_mode_one
#print axioms arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_norm_ge
#print axioms arbitrarySourceDegreeMPolyState_antipodal_dominant_mode_one_strict_pos
#print axioms arbitrarySourceModeResponse_eq_mode_of_map
#print axioms arbitrarySourceSuperpositionResponse_eq_superposition_of_map
#print axioms arbitrarySourceDegreeMPolyResponse_eq_sum_modes
#print axioms arbitrarySourceDegreeMPolyResponse_eq_poly_of_map
#print axioms arbitrarySourceSuperpositionResponse_zero_of_neutral
#print axioms arbitrarySourceDegreeMPolyResponse_eq_higher_modes_of_neutral
#print axioms arbitrarySourceDegreeMPolyResponse_isolate_mode
#print axioms arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_le
#print axioms arbitrarySourceDegreeMPolyResponse_isolate_mode_norm_ge
#print axioms arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_norm_ge
#print axioms arbitrarySourceDegreeMPolyResponse_dominant_anchor_mode_strict_pos
#print axioms arbitrarySourceDegreeMPolyResponse_antipodal_isolate_mode_one
#print axioms arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_norm_ge
#print axioms arbitrarySourceDegreeMPolyResponse_antipodal_dominant_mode_one_strict_pos
#print axioms arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_eq_two_smul
#print axioms arbitrarySourceDegreeMPolyResponse_antipodal_deg_one_norm_eq
#print axioms scaleAmplitude_antipodal_linear_sum_zero
#print axioms degreeMPolyProfile_zero_eq_constant
#print axioms arbitrary_source_multi_mode_orthogonal_decomposition_master_synthesis
end
end UnifiedTheory.Audit.KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
