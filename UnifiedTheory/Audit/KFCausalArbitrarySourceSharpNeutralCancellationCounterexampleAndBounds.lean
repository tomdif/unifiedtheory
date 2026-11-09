/- Sharp neutral cancellation counterexample (`n = 2`, antipodal non-zero sources
`b = ![1, -1]`, unit weights `w = ![1, 1]`, identical packet profiles) showing
that arbitrary-source linear superpositions and constant polynomial modes can
vanish identically by destructive interference while quadratic-source modes
`∑ i, w_i b_i^2 P_i = 2 • ψ` remain strictly non-zero, together with exact
two-sided triangle and reverse-triangle norm bounds, necessary-and-sufficient
non-degeneracy characterizations, and strict positivity under dominant constant
modes across all normed multi-packet maps. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceDominantConstantModeResponseLowerBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
  (unitMonomialPolyProfile)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (factoredPolyProfile degreeMPolyProfile
   state_factored_eq_sum_smul
   state_factored_neutral_zero momentum_factored_neutral_zero
   output_factored_neutral_zero momentumOutput_factored_neutral_zero
   seconds_factored_neutral_zero hamiltonianOutput_factored_neutral_zero
   fullEnergy_factored_eq_norm_sum_sq
   fullEnergy_factored_neutral_zero fullResponse_factored_neutral_zero
   full_bound_degreeM_neutral)
open KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis
  (state_degreeM_arbitrary_source_norm_le
   state_degreeM_arbitrary_source_norm_ge
   momentum_degreeM_arbitrary_source_norm_le
   momentum_degreeM_arbitrary_source_norm_ge
   output_degreeM_arbitrary_source_norm_le
   output_degreeM_arbitrary_source_norm_ge
   momentumOutput_degreeM_arbitrary_source_norm_le
   momentumOutput_degreeM_arbitrary_source_norm_ge
   seconds_degreeM_arbitrary_source_norm_le
   seconds_degreeM_arbitrary_source_norm_ge
   hamiltonianOutput_degreeM_arbitrary_source_norm_le
   hamiltonianOutput_degreeM_arbitrary_source_norm_ge)
open KFCausalArbitrarySourceDominantConstantModeResponseLowerBound
  (state_degreeM_dominant_constant_norm_ge
   momentum_degreeM_dominant_constant_norm_ge
   hamiltonianOutput_degreeM_dominant_constant_norm_ge
   constant_mode_fullResponse_zero_couplings_lower_arbitrary_source)

/-! ### 1. Abstract Arbitrary-Source Polynomial Modes and Antipodal Neutral Counterexample -/

def arbitrarySourceModeState {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (k : ℕ) (P : Fin n → E) : E :=
  ∑ i : Fin n, (w i * b i ^ (k + 1)) • P i

def arbitrarySourceSuperpositionState {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E) : E :=
  ∑ i : Fin n, (w i * b i) • P i

def arbitrarySourceDegreeMPolyState {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) : E :=
  ∑ k : Fin (M + 1), c k • arbitrarySourceModeState w b (k : ℕ) P

def isNeutralArbitrarySource {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E) : Prop :=
  arbitrarySourceSuperpositionState w b P = 0

def antipodalWeights : Fin 2 → ℂ := ![1, 1]

def antipodalSources : Fin 2 → ℂ := ![1, -1]

def identicalPackets {E : Type*} (ψ : E) : Fin 2 → E := fun _ => ψ

theorem antipodalSources_zero_ne_zero : antipodalSources 0 ≠ 0 := by
  simp [antipodalSources]

theorem antipodalSources_one_ne_zero : antipodalSources 1 ≠ 0 := by
  simp [antipodalSources]

theorem antipodalSources_distinct : antipodalSources 0 ≠ antipodalSources 1 := by
  intro h
  have h1 : (1 : ℂ) = -1 := by simpa [antipodalSources] using h
  have h2 : (1 : ℝ) = -1 := by
    have := congrArg Complex.re h1
    simpa using this
  linarith

theorem antipodalWeights_sources_linear_sum_zero :
    ∑ i : Fin 2, antipodalWeights i * antipodalSources i = 0 := by
  simp [Fin.sum_univ_two, antipodalWeights, antipodalSources]

theorem antipodalWeights_sources_quadratic_sum_eq_two :
    ∑ i : Fin 2, antipodalWeights i * antipodalSources i ^ 2 = 2 := by
  simp [Fin.sum_univ_two, antipodalWeights, antipodalSources]
  norm_num

theorem arbitrarySourceModeState_zero_eq_superposition
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (w : Fin n → ℂ) (b : Fin n → ℂ) (P : Fin n → E) :
    arbitrarySourceModeState w b 0 P = arbitrarySourceSuperpositionState w b P := by
  unfold arbitrarySourceModeState arbitrarySourceSuperpositionState
  simp [pow_one]

theorem antipodal_superposition_eq_zero
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    arbitrarySourceSuperpositionState antipodalWeights antipodalSources (identicalPackets ψ) = 0 := by
  unfold arbitrarySourceSuperpositionState identicalPackets
  rw [← Finset.sum_smul, antipodalWeights_sources_linear_sum_zero, zero_smul]

theorem antipodal_is_neutral_arbitrary_source
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    isNeutralArbitrarySource antipodalWeights antipodalSources (identicalPackets ψ) :=
  antipodal_superposition_eq_zero ψ

theorem antipodal_mode_zero_vanishes
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    arbitrarySourceModeState antipodalWeights antipodalSources 0 (identicalPackets ψ) = 0 := by
  rw [arbitrarySourceModeState_zero_eq_superposition]
  exact antipodal_superposition_eq_zero ψ

theorem antipodal_mode_one_eq_two_smul
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ) =
      (2 : ℂ) • ψ := by
  unfold arbitrarySourceModeState identicalPackets
  rw [← Finset.sum_smul, antipodalWeights_sources_quadratic_sum_eq_two]

theorem antipodal_mode_one_norm_eq_two_mul
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) :
    ‖arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ)‖ =
      2 * ‖ψ‖ := by
  rw [antipodal_mode_one_eq_two_smul, norm_smul]
  simp

theorem antipodal_mode_one_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) (hψ : ψ ≠ 0) :
    arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ) ≠ 0 := by
  intro hzero
  have hnorm : ‖arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ)‖ = 0 := by
    rw [hzero, norm_zero]
  rw [antipodal_mode_one_norm_eq_two_mul] at hnorm
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  linarith

theorem antipodal_neutral_cancellation_counterexample
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (ψ : E) (hψ : ψ ≠ 0) :
    antipodalSources 0 ≠ 0 ∧
      antipodalSources 1 ≠ 0 ∧
      antipodalSources 0 ≠ antipodalSources 1 ∧
      isNeutralArbitrarySource antipodalWeights antipodalSources (identicalPackets ψ) ∧
      arbitrarySourceModeState antipodalWeights antipodalSources 0 (identicalPackets ψ) = 0 ∧
      arbitrarySourceModeState antipodalWeights antipodalSources 1 (identicalPackets ψ) ≠ 0 :=
  ⟨antipodalSources_zero_ne_zero,
   antipodalSources_one_ne_zero,
   antipodalSources_distinct,
   antipodal_is_neutral_arbitrary_source ψ,
   antipodal_mode_zero_vanishes ψ,
   antipodal_mode_one_nonzero ψ hψ⟩

/-! ### 2. Concrete Multi-Packet `n = 2` Antipodal Neutral Cancellation Counterexample -/

variable (ε h a₀ w₀ p₀ : ℝ) (b₀ : ℂ) (Q : Polynomial ℂ)
  (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
  (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem state_antipodal_constant_mode_zero :
    state 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  state_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ antipodalWeights_sources_linear_sum_zero

theorem momentum_antipodal_constant_mode_zero :
    momentum 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  momentum_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ antipodalWeights_sources_linear_sum_zero

theorem output_antipodal_constant_mode_zero (j : Fin 8) :
    output 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  output_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ hb antipodalWeights_sources_linear_sum_zero j

theorem momentumOutput_antipodal_constant_mode_zero (j : Fin 8) :
    momentumOutput 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  momentumOutput_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ hb antipodalWeights_sources_linear_sum_zero j

theorem seconds_antipodal_constant_mode_zero
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j = 0 :=
  seconds_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ antipodalWeights_sources_linear_sum_zero hb_narrow j

theorem hamiltonianOutput_antipodal_constant_mode_zero
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow mass2 quartic vacuum t = 0 :=
  hamiltonianOutput_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ antipodalWeights_sources_linear_sum_zero hb_narrow mass2 quartic vacuum t

theorem fullEnergy_antipodal_constant_mode_zero (mass2 quartic vacuum t : ℝ) :
    fullEnergy 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  fullEnergy_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ hb antipodalWeights_sources_linear_sum_zero mass2 quartic vacuum t

theorem fullResponse_antipodal_constant_mode_zero (mass2 quartic vacuum t : ℝ) :
    fullResponse 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  fullResponse_factored_neutral_zero 2 ε h a₀ w₀ p₀ b₀ antipodalWeights antipodalSources 1
    hε ha₀ hh hw₀ hb antipodalWeights_sources_linear_sum_zero mass2 quartic vacuum t

theorem state_antipodal_quadratic_source_mode_eq_two_smul :
    state 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀)
      (factoredPolyProfile (fun i => antipodalSources i ^ 2) Q)
      hε (fun _ => ha₀) hh (fun _ => hw₀) =
    (2 : ℂ) •
      state 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (fun _ => 1) (fun _ => b₀) (fun _ => Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  rw [state_factored_eq_sum_smul, antipodalWeights_sources_quadratic_sum_eq_two]

theorem fullEnergy_antipodal_quadratic_source_mode_eq_four_mul (mass2 quartic vacuum t : ℝ) :
    fullEnergy 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
      antipodalWeights (fun _ => b₀)
      (factoredPolyProfile (fun i => antipodalSources i ^ 2) Q)
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t =
    4 *
      fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (fun _ => 1) (fun _ => b₀) (fun _ => Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  rw [fullEnergy_factored_eq_norm_sum_sq, antipodalWeights_sources_quadratic_sum_eq_two]
  norm_num

/-! ### 3. Two-Sided Triangle/Reverse-Triangle Bounds and Non-Degeneracy Characterizations -/

theorem arbitrarySourceDegreeMPolyState_split_zero
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    arbitrarySourceDegreeMPolyState M w b c P =
      c 0 • arbitrarySourceModeState w b 0 P +
        ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P := by
  unfold arbitrarySourceDegreeMPolyState
  rw [Fin.sum_univ_succ]
  rfl

theorem arbitrarySourceDegreeMPolyState_norm_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    ‖arbitrarySourceDegreeMPolyState M w b c P‖ ≤
      ‖c 0‖ * ‖arbitrarySourceModeState w b 0 P‖ +
        ∑ r : Fin M, ‖c r.succ‖ * ‖arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ := by
  rw [arbitrarySourceDegreeMPolyState_split_zero]
  have h1 : ‖c 0 • arbitrarySourceModeState w b 0 P +
      ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ ≤
    ‖c 0 • arbitrarySourceModeState w b 0 P‖ +
      ‖∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ :=
    norm_add_le _ _
  have h2 : ‖∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ ≤
      ∑ r : Fin M, ‖c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ :=
    norm_sum_le Finset.univ _
  simp only [norm_smul] at h1 h2
  linarith

theorem arbitrarySourceDegreeMPolyState_norm_ge
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    ‖c 0‖ * ‖arbitrarySourceModeState w b 0 P‖ -
        ∑ r : Fin M, ‖c r.succ‖ * ‖arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ ≤
      ‖arbitrarySourceDegreeMPolyState M w b c P‖ := by
  rw [arbitrarySourceDegreeMPolyState_split_zero]
  have h1 : ‖c 0 • arbitrarySourceModeState w b 0 P‖ ≤
      ‖c 0 • arbitrarySourceModeState w b 0 P +
        ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ +
      ‖∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ :=
    norm_le_add_norm_add _ _
  have h2 : ‖∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ ≤
      ∑ r : Fin M, ‖c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ :=
    norm_sum_le Finset.univ _
  simp only [norm_smul] at h1 h2
  linarith

theorem arbitrarySourceDegreeMPolyState_norm_pos_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) :
    0 < ‖arbitrarySourceDegreeMPolyState M w b c P‖ ↔
      arbitrarySourceDegreeMPolyState M w b c P ≠ 0 :=
  norm_pos_iff

theorem arbitrarySourceDegreeMPolyState_dominant_zero_mode_pos
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (M : ℕ) (w : Fin n → ℂ) (b : Fin n → ℂ) (c : Fin (M + 1) → ℂ)
    (P : Fin n → E) (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖c 0‖ * ‖arbitrarySourceModeState w b 0 P‖)
    (hdom : ∑ r : Fin M, ‖c r.succ‖ * ‖arbitrarySourceModeState w b ((r : ℕ) + 1) P‖ ≤
      θ * (‖c 0‖ * ‖arbitrarySourceModeState w b 0 P‖)) :
    0 < ‖arbitrarySourceDegreeMPolyState M w b c P‖ := by
  have hge := arbitrarySourceDegreeMPolyState_norm_ge M w b c P
  have hmul : 0 < (1 - θ) * (‖c 0‖ * ‖arbitrarySourceModeState w b 0 P‖) :=
    mul_pos (by linarith) hpos
  linarith

variable (n M : ℕ) (a w p : Fin n → ℝ) (C b c₀ : Fin n → ℂ)
  (d : Fin M → Fin n → ℂ) (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i)

theorem state_degreeM_arbitrary_source_two_sided_norm_bounds :
    (‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖) ∧
    (‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ≤
      ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ +
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) :=
  ⟨state_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw,
   state_degreeM_arbitrary_source_norm_le n M ε h a w p C b c₀ d hε ha hh hw⟩

theorem momentum_degreeM_arbitrary_source_two_sided_norm_bounds :
    (‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖) ∧
    (‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ +
        ∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) :=
  ⟨momentum_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw,
   momentum_degreeM_arbitrary_source_norm_le n M ε h a w p C b c₀ d hε ha hh hw⟩

theorem output_degreeM_arbitrary_source_two_sided_norm_bounds (j : Fin 8) :
    (‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖) ∧
    (‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ +
        ∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) :=
  ⟨output_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw hb j,
   output_degreeM_arbitrary_source_norm_le n M ε h a w p C b c₀ d hε ha hh hw hb j⟩

theorem momentumOutput_degreeM_arbitrary_source_two_sided_norm_bounds (j : Fin 8) :
    (‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖) ∧
    (‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ +
        ∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) :=
  ⟨momentumOutput_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw hb j,
   momentumOutput_degreeM_arbitrary_source_norm_le n M ε h a w p C b c₀ d hε ha hh hw hb j⟩

theorem seconds_degreeM_arbitrary_source_two_sided_norm_bounds
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    (‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ -
        ∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖) ∧
    (‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ +
        ∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖) :=
  ⟨seconds_degreeM_arbitrary_source_norm_ge n M ε h a w p C b c₀ d hε ha hh hw hb_narrow j,
   seconds_degreeM_arbitrary_source_norm_le n M ε h a w p C b c₀ d hε ha hh hw hb_narrow j⟩

theorem hamiltonianOutput_degreeM_arbitrary_source_two_sided_norm_bounds
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    (‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ -
        ∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖) ∧
    (‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ +
        ∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖) :=
  ⟨hamiltonianOutput_degreeM_arbitrary_source_norm_ge
     n M ε h a w p C b c₀ d hε ha hh hw hb_narrow mass2 quartic vacuum t,
   hamiltonianOutput_degreeM_arbitrary_source_norm_le
     n M ε h a w p C b c₀ d hε ha hh hw hb_narrow mass2 quartic vacuum t⟩

theorem state_degreeM_arbitrary_source_norm_pos_iff :
    0 < ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ↔
      state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw ≠ 0 :=
  norm_pos_iff

theorem state_degreeM_dominant_constant_strict_pos (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖)
    (hdom : ∑ r : Fin M,
        ‖state n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      θ * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    0 < ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  have hge := state_degreeM_dominant_constant_norm_ge n M ε h a w p C b c₀ d hε ha hh hw θ hdom
  have hmul : 0 < (1 - θ) *
      ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ :=
    mul_pos (by linarith) hpos
  linarith

theorem momentum_degreeM_dominant_constant_strict_pos (θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖)
    (hdom : ∑ r : Fin M,
        ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      θ * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    0 < ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  have hge := momentum_degreeM_dominant_constant_norm_ge n M ε h a w p C b c₀ d hε ha hh hw θ hdom
  have hmul : 0 < (1 - θ) *
      ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ :=
    mul_pos (by linarith) hpos
  linarith

theorem hamiltonianOutput_degreeM_dominant_constant_strict_pos
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t θ : ℝ) (hθ : θ < 1)
    (hpos : 0 < ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖)
    (hdom : ∑ r : Fin M,
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1))
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      θ * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖) :
    0 < ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  have hge := hamiltonianOutput_degreeM_dominant_constant_norm_ge
    n M ε h a w p C b c₀ d hε ha hh hw hb_narrow mass2 quartic vacuum t θ hdom
  have hmul : 0 < (1 - θ) *
      ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ :=
    mul_pos (by linarith) hpos
  linarith

theorem arbitrary_source_sharp_neutral_cancellation_and_bounds_master_synthesis
    (t : ℝ) :
    (state 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        antipodalWeights (fun _ => b₀) (factoredPolyProfile antipodalSources 1)
        hε (fun _ => ha₀) hh (fun _ => hw₀) = 0) ∧
    (state 2 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        antipodalWeights (fun _ => b₀)
        (factoredPolyProfile (fun i => antipodalSources i ^ 2) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) =
      (2 : ℂ) •
        state 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
          (fun _ => 1) (fun _ => b₀) (fun _ => Q)
          hε (fun _ => ha₀) hh (fun _ => hw₀)) ∧
    ((‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ -
          ∑ r : Fin M,
            ‖state n ε h a w p (scaleAmplitude C (d r)) b
              (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
        ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖) ∧
      (‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ≤
        ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ +
          ∑ r : Fin M,
            ‖state n ε h a w p (scaleAmplitude C (d r)) b
              (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖)) ∧
    (-(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t ≤
      fullResponse n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (m2 q4 v0 : ℝ),
      0 ≤ m2 → 0 ≤ q4 → 0 ≤ v0 →
      ∀ (n' M' : ℕ) (ε' h' a₀' w₀' p₀' : ℝ) (b₀' : ℂ) (C' c₀' : Fin n' → ℂ)
      (d' : Fin M' → Fin n' → ℂ)
      (hε' : 0 < ε') (ha₀' : 0 < a₀') (hh' : h' ≠ 0) (hw₀' : 1 ≤ w₀')
      (hb' : |h'| ≤ 2 * Real.pi * ε' / 3)
      (_hneutral : ∀ r : Fin M', ∑ i : Fin n', C' i * d' r i = 0) (t' : ℝ),
      -(K / ε') * fullEnergy n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t' ≤
      fullResponse n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t') :=
  ⟨state_antipodal_constant_mode_zero ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀,
   state_antipodal_quadratic_source_mode_eq_two_smul ε h a₀ w₀ p₀ b₀ Q hε ha₀ hh hw₀,
   state_degreeM_arbitrary_source_two_sided_norm_bounds ε h hε hh n M a w p C b c₀ d ha hw,
   constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
     n ε h a w p C b c₀ hε ha hh hw hb t,
   full_bound_degreeM_neutral⟩

#print axioms antipodalSources_zero_ne_zero
#print axioms antipodalSources_one_ne_zero
#print axioms antipodalSources_distinct
#print axioms antipodalWeights_sources_linear_sum_zero
#print axioms antipodalWeights_sources_quadratic_sum_eq_two
#print axioms arbitrarySourceModeState_zero_eq_superposition
#print axioms antipodal_superposition_eq_zero
#print axioms antipodal_is_neutral_arbitrary_source
#print axioms antipodal_mode_zero_vanishes
#print axioms antipodal_mode_one_eq_two_smul
#print axioms antipodal_mode_one_norm_eq_two_mul
#print axioms antipodal_mode_one_nonzero
#print axioms antipodal_neutral_cancellation_counterexample
#print axioms state_antipodal_constant_mode_zero
#print axioms momentum_antipodal_constant_mode_zero
#print axioms output_antipodal_constant_mode_zero
#print axioms momentumOutput_antipodal_constant_mode_zero
#print axioms seconds_antipodal_constant_mode_zero
#print axioms hamiltonianOutput_antipodal_constant_mode_zero
#print axioms fullEnergy_antipodal_constant_mode_zero
#print axioms fullResponse_antipodal_constant_mode_zero
#print axioms state_antipodal_quadratic_source_mode_eq_two_smul
#print axioms fullEnergy_antipodal_quadratic_source_mode_eq_four_mul
#print axioms arbitrarySourceDegreeMPolyState_split_zero
#print axioms arbitrarySourceDegreeMPolyState_norm_le
#print axioms arbitrarySourceDegreeMPolyState_norm_ge
#print axioms arbitrarySourceDegreeMPolyState_norm_pos_iff
#print axioms arbitrarySourceDegreeMPolyState_dominant_zero_mode_pos
#print axioms state_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms momentum_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms output_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms momentumOutput_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms seconds_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms hamiltonianOutput_degreeM_arbitrary_source_two_sided_norm_bounds
#print axioms state_degreeM_arbitrary_source_norm_pos_iff
#print axioms state_degreeM_dominant_constant_strict_pos
#print axioms momentum_degreeM_dominant_constant_strict_pos
#print axioms hamiltonianOutput_degreeM_dominant_constant_strict_pos
#print axioms arbitrary_source_sharp_neutral_cancellation_and_bounds_master_synthesis
end
end UnifiedTheory.Audit.KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
