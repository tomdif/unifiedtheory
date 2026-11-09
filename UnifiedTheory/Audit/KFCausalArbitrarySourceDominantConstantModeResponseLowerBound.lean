/- Arbitrary-source (`b : Fin n → ℂ`) degree-`M` polynomial dominant-constant-mode
norm lower bounds (`(1 - θ) * ‖Φ₀‖ ≤ ‖Φ_M‖` and `(1 / 2) * ‖Φ₀‖ ≤ ‖Φ_M‖`),
common-constant scalar factoring reverse-triangle lower bounds, squared-norm
Cauchy-Young lower and upper bounds across all normed multi-packet maps, and
arbitrary-source constant-mode clock-kinetic and zero-coupling full-response
lower bounds. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalArbitrarySourceDominantConstantModeResponseLowerBound
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
  (clockKineticEnergy clockKineticResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude staticEnergy staticResponse
   radialKineticEnergy radialKineticResponse
   clockKinetic_lower_constant
   static_add_radialKinetic_response_lower
   fullResponse_zero_couplings_lower)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
  (unitMonomialPolyProfile)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (degreeMPolyProfile full_bound_degreeM_neutral)
open KFCausalArbitrarySourceDegreeMPolynomialSuperpositionSynthesis
  (state_degreeM_arbitrary_source_eq
   momentum_degreeM_arbitrary_source_eq
   output_degreeM_arbitrary_source_eq
   momentumOutput_degreeM_arbitrary_source_eq
   seconds_degreeM_arbitrary_source_eq
   hamiltonianOutput_degreeM_arbitrary_source_eq
   hamiltonian_degreeM_arbitrary_source_action
   state_degreeM_common_constant_arbitrary_source_eq
   momentum_degreeM_common_constant_arbitrary_source_eq
   output_degreeM_common_constant_arbitrary_source_eq
   momentumOutput_degreeM_common_constant_arbitrary_source_eq
   seconds_degreeM_common_constant_arbitrary_source_eq
   hamiltonianOutput_degreeM_common_constant_arbitrary_source_eq
   hamiltonian_degreeM_common_constant_arbitrary_source_action)

private lemma dominant_mode_norm_lower {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E) (θ : ℝ)
    (hdom : ∑ r : Fin M, ‖f r‖ ≤ θ * ‖x‖) :
    (1 - θ) * ‖x‖ ≤ ‖x + ∑ r : Fin M, f r‖ := by
  have h1 : ‖x‖ ≤ ‖x + ∑ r : Fin M, f r‖ + ‖∑ r : Fin M, f r‖ :=
    norm_le_add_norm_add x (∑ r : Fin M, f r)
  have h2 : ‖∑ r : Fin M, f r‖ ≤ ∑ r : Fin M, ‖f r‖ :=
    norm_sum_le Finset.univ f
  linarith

private lemma half_dominant_mode_norm_lower {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E)
    (hdom : ∑ r : Fin M, ‖f r‖ ≤ (1 / 2) * ‖x‖) :
    (1 / 2) * ‖x‖ ≤ ‖x + ∑ r : Fin M, f r‖ := by
  have h := dominant_mode_norm_lower x f (1 / 2) hdom
  linarith

private lemma common_constant_norm_ge {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] {M : ℕ} (z : ℂ) (x : E) (f : Fin M → E) :
    ‖z‖ * ‖x‖ - ∑ r : Fin M, ‖f r‖ ≤ ‖z • x + ∑ r : Fin M, f r‖ := by
  have h1 : ‖z • x‖ ≤ ‖z • x + ∑ r : Fin M, f r‖ + ‖∑ r : Fin M, f r‖ :=
    norm_le_add_norm_add (z • x) (∑ r : Fin M, f r)
  have h2 : ‖∑ r : Fin M, f r‖ ≤ ∑ r : Fin M, ‖f r‖ :=
    norm_sum_le Finset.univ f
  rw [norm_smul] at h1
  linarith

private lemma sq_norm_add_sum_le {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E) :
    ‖x + ∑ r : Fin M, f r‖ ^ 2 ≤
      2 * ‖x‖ ^ 2 + 2 * (∑ r : Fin M, ‖f r‖) ^ 2 := by
  have h1 : ‖x + ∑ r : Fin M, f r‖ ≤ ‖x‖ + ∑ r : Fin M, ‖f r‖ := by
    have ha := norm_add_le x (∑ r : Fin M, f r)
    have hb := norm_sum_le Finset.univ f
    linarith
  have h2 : ‖x + ∑ r : Fin M, f r‖ ^ 2 ≤ (‖x‖ + ∑ r : Fin M, ‖f r‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 0 ≤ (‖x‖ - ∑ r : Fin M, ‖f r‖) ^ 2 := sq_nonneg _
  linarith

private lemma sq_norm_add_sum_ge {E : Type*} [SeminormedAddCommGroup E]
    {M : ℕ} (x : E) (f : Fin M → E) :
    (1 / 2) * ‖x‖ ^ 2 - (∑ r : Fin M, ‖f r‖) ^ 2 ≤
      ‖x + ∑ r : Fin M, f r‖ ^ 2 := by
  have h1 : ‖x‖ ≤ ‖x + ∑ r : Fin M, f r‖ + ∑ r : Fin M, ‖f r‖ := by
    have ha := norm_le_add_norm_add x (∑ r : Fin M, f r)
    have hb := norm_sum_le Finset.univ f
    linarith
  have h2 : ‖x‖ ^ 2 ≤ (‖x + ∑ r : Fin M, f r‖ + ∑ r : Fin M, ‖f r‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 0 ≤ (‖x + ∑ r : Fin M, f r‖ - ∑ r : Fin M, ‖f r‖) ^ 2 := sq_nonneg _
  linarith

variable (n M : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b c₀ : Fin n → ℂ)
  (d : Fin M → Fin n → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### 1. Dominant Constant Mode (`(1 - θ) * ‖Φ₀‖ ≤ ‖Φ_M‖`) Across All 7 Normed Maps -/

theorem state_degreeM_dominant_constant_norm_ge (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖state n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      θ * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    (1 - θ) * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [state_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem momentum_degreeM_dominant_constant_norm_ge (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      θ * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    (1 - θ) * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem output_degreeM_dominant_constant_norm_ge (j : Fin 8) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖output n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      θ * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖) :
    (1 - θ) * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [output_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem momentumOutput_degreeM_dominant_constant_norm_ge (j : Fin 8) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      θ * ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖) :
    (1 - θ) *
        ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem seconds_degreeM_dominant_constant_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ ≤
      θ * ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖) :
    (1 - θ) *
        ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem hamiltonianOutput_degreeM_dominant_constant_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1))
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      θ * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖) :
    (1 - θ) *
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact dominant_mode_norm_lower _ _ θ hdom

theorem hamiltonian_degreeM_dominant_constant_action_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t
          ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
           hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      θ * ‖hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t
          ⟨state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw,
           hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw;
    (1 - θ) * ‖H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ := by
  dsimp only
  rw [hamiltonian_degreeM_arbitrary_source_action n M ε h a w p C b c₀ d
    hε ha hh hw hb_narrow mass2 quartic vacuum t]
  exact dominant_mode_norm_lower _ _ θ hdom

/-! ### 2. Half-Dominant (`θ = 1 / 2`) Constant-Mode Norm Lower Bounds Across All 7 Maps -/

theorem state_degreeM_half_dominant_constant_norm_ge
    (hdom : ∑ r : Fin M,
        ‖state n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      (1 / 2) * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    (1 / 2) * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [state_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem momentum_degreeM_half_dominant_constant_norm_ge
    (hdom : ∑ r : Fin M,
        ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      (1 / 2) * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖) :
    (1 / 2) * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem output_degreeM_half_dominant_constant_norm_ge (j : Fin 8)
    (hdom : ∑ r : Fin M,
        ‖output n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      (1 / 2) * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖) :
    (1 / 2) * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [output_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem momentumOutput_degreeM_half_dominant_constant_norm_ge (j : Fin 8)
    (hdom : ∑ r : Fin M,
        ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      (1 / 2) *
        ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖) :
    (1 / 2) *
        ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem seconds_degreeM_half_dominant_constant_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8)
    (hdom : ∑ r : Fin M,
        ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ ≤
      (1 / 2) *
        ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖) :
    (1 / 2) *
        ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem hamiltonianOutput_degreeM_half_dominant_constant_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ)
    (hdom : ∑ r : Fin M,
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
          (unitMonomialPolyProfile n ((r : ℕ) + 1))
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      (1 / 2) * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖) :
    (1 / 2) *
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact half_dominant_mode_norm_lower _ _ hdom

theorem hamiltonian_degreeM_half_dominant_constant_action_norm_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ)
    (hdom : ∑ r : Fin M,
        ‖hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t
          ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
           hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      (1 / 2) * ‖hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t
          ⟨state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw,
           hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw;
    (1 / 2) * ‖H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ := by
  dsimp only
  rw [hamiltonian_degreeM_arbitrary_source_action n M ε h a w p C b c₀ d
    hε ha hh hw hb_narrow mass2 quartic vacuum t]
  exact half_dominant_mode_norm_lower _ _ hdom

/-! ### 3. Common-Constant Scalar Factoring (`c₀ = fun _ => z`) Reverse-Triangle Lower Bounds -/

theorem state_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ) :
    ‖z‖ * ‖state n ε h a w p C b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw‖ := by
  rw [state_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem momentum_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ) :
    ‖z‖ * ‖momentum n ε h a w p C b (fun _ => 1) hε ha hh hw‖ -
        ∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw‖ := by
  rw [momentum_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem output_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ) (j : Fin 8) :
    ‖z‖ * ‖output n ε h a w p C b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb j‖ := by
  rw [output_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem momentumOutput_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ) (j : Fin 8) :
    ‖z‖ * ‖momentumOutput n ε h a w p C b (fun _ => 1) hε ha hh hw hb j‖ -
        ∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖ ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb j‖ := by
  rw [momentumOutput_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem seconds_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    ‖z‖ * ‖seconds n ε h a w p C b (fun _ => 1) hε ha hh hw hb_narrow j‖ -
        ∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖ ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw hb_narrow j‖ := by
  rw [seconds_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem hamiltonianOutput_degreeM_common_constant_arbitrary_source_norm_ge (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    ‖z‖ * ‖hamiltonianOutput n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ -
        ∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ := by
  rw [hamiltonianOutput_degreeM_common_constant_arbitrary_source_eq]
  exact common_constant_norm_ge z _ _

theorem hamiltonian_degreeM_common_constant_arbitrary_source_action_norm_ge (z : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d) hε ha hh hw;
    let ψ₁ := state n ε h a w p C b (fun _ => 1) hε ha hh hw;
    ‖z‖ * ‖H ⟨ψ₁, hamiltonian_domain n ε h a w p C b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ -
        ∑ r : Fin M, ‖H ⟨state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw,
          hamiltonian_domain n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ≤
      ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (degreeMPolyProfile M (fun _ => z) d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ := by
  dsimp only
  rw [hamiltonian_degreeM_common_constant_arbitrary_source_action n M ε h a w p C b d
    hε ha hh hw z hb_narrow mass2 quartic vacuum t]
  exact common_constant_norm_ge z _ _

/-! ### 4. Squared-Norm Cauchy-Young Upper and Lower Bounds Across All 6 Normed Packet Maps -/

theorem state_degreeM_arbitrary_source_norm_sq_le :
    ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 ≤
      2 * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 := by
  rw [state_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem state_degreeM_arbitrary_source_norm_sq_ge :
    (1 / 2) * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 -
        (∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 := by
  rw [state_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

theorem momentum_degreeM_arbitrary_source_norm_sq_le :
    ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 ≤
      2 * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem momentum_degreeM_arbitrary_source_norm_sq_ge :
    (1 / 2) * ‖momentum n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 -
        (∑ r : Fin M,
          ‖momentum n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 ≤
      ‖momentum n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 := by
  rw [momentum_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

theorem output_degreeM_arbitrary_source_norm_sq_le (j : Fin 8) :
    ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ^ 2 ≤
      2 * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) ^ 2 := by
  rw [output_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem output_degreeM_arbitrary_source_norm_sq_ge (j : Fin 8) :
    (1 / 2) * ‖output n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 -
        (∑ r : Fin M,
          ‖output n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) ^ 2 ≤
      ‖output n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ^ 2 := by
  rw [output_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

theorem momentumOutput_degreeM_arbitrary_source_norm_sq_le (j : Fin 8) :
    ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ^ 2 ≤
      2 * ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) ^ 2 := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem momentumOutput_degreeM_arbitrary_source_norm_sq_ge (j : Fin 8) :
    (1 / 2) *
        ‖momentumOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 -
        (∑ r : Fin M,
          ‖momentumOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb j‖) ^ 2 ≤
      ‖momentumOutput n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb j‖ ^ 2 := by
  rw [momentumOutput_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

theorem seconds_degreeM_arbitrary_source_norm_sq_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ ^ 2 ≤
      2 * ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖) ^ 2 := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem seconds_degreeM_arbitrary_source_norm_sq_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    (1 / 2) *
        ‖seconds n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ ^ 2 -
        (∑ r : Fin M,
          ‖seconds n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw hb_narrow j‖) ^ 2 ≤
      ‖seconds n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw hb_narrow j‖ ^ 2 := by
  rw [seconds_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

theorem hamiltonianOutput_degreeM_arbitrary_source_norm_sq_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 ≤
      2 * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖) ^ 2 := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_le _ _

theorem hamiltonianOutput_degreeM_arbitrary_source_norm_sq_ge
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    (1 / 2) *
        ‖hamiltonianOutput n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 -
        (∑ r : Fin M,
          ‖hamiltonianOutput n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1))
            hε ha hh hw hb_narrow mass2 quartic vacuum t‖) ^ 2 ≤
      ‖hamiltonianOutput n ε h a w p C b (degreeMPolyProfile M c₀ d)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 := by
  rw [hamiltonianOutput_degreeM_arbitrary_source_eq]
  exact sq_norm_add_sum_ge _ _

/-! ### 5. Arbitrary-Source Constant-Mode Response Lower Bounds and Master Synthesis -/

theorem constant_mode_clockKinetic_lower_arbitrary_source (t : ℝ) :
    -(1 / (4 * ε)) *
        clockKineticEnergy n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb t ≤
      clockKineticResponse n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb t :=
  clockKinetic_lower_constant n ε h a w p C b c₀ hε ha hh hw hb t

theorem constant_mode_fullResponse_zero_couplings_lower_arbitrary_source (t : ℝ) :
    -(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t ≤
      fullResponse n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t :=
  fullResponse_zero_couplings_lower n ε h a w p C b c₀ hε ha hh hw hb t

theorem constant_mode_static_add_radialKinetic_lower_arbitrary_source (t : ℝ) :
    -(1 / (4 * ε)) *
        (staticEnergy n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb +
          Real.exp (2 * t) *
            radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb) ≤
      staticResponse n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb +
        Real.exp (2 * t) *
          radialKineticResponse n ε h a w p C b (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb :=
  static_add_radialKinetic_response_lower n ε h a w p C b c₀ hε ha hh hw hb t

theorem arbitrary_source_dominant_constant_mode_master_synthesis (t : ℝ) :
    ((1 / 2) * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 -
        (∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 ≤
      ‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2) ∧
    (‖state n ε h a w p C b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 ≤
      2 * ‖state n ε h a w p (scaleAmplitude C c₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 +
        2 * (∑ r : Fin M,
          ‖state n ε h a w p (scaleAmplitude C (d r)) b
            (unitMonomialPolyProfile n ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2) ∧
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
  ⟨state_degreeM_arbitrary_source_norm_sq_ge n M ε h a w p C b c₀ d hε ha hh hw,
   state_degreeM_arbitrary_source_norm_sq_le n M ε h a w p C b c₀ d hε ha hh hw,
   constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
     n ε h a w p C b c₀ hε ha hh hw hb t,
   full_bound_degreeM_neutral⟩

#print axioms state_degreeM_dominant_constant_norm_ge
#print axioms momentum_degreeM_dominant_constant_norm_ge
#print axioms output_degreeM_dominant_constant_norm_ge
#print axioms momentumOutput_degreeM_dominant_constant_norm_ge
#print axioms seconds_degreeM_dominant_constant_norm_ge
#print axioms hamiltonianOutput_degreeM_dominant_constant_norm_ge
#print axioms hamiltonian_degreeM_dominant_constant_action_norm_ge
#print axioms state_degreeM_half_dominant_constant_norm_ge
#print axioms momentum_degreeM_half_dominant_constant_norm_ge
#print axioms output_degreeM_half_dominant_constant_norm_ge
#print axioms momentumOutput_degreeM_half_dominant_constant_norm_ge
#print axioms seconds_degreeM_half_dominant_constant_norm_ge
#print axioms hamiltonianOutput_degreeM_half_dominant_constant_norm_ge
#print axioms hamiltonian_degreeM_half_dominant_constant_action_norm_ge
#print axioms state_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms momentum_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms output_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms momentumOutput_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms seconds_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms hamiltonianOutput_degreeM_common_constant_arbitrary_source_norm_ge
#print axioms hamiltonian_degreeM_common_constant_arbitrary_source_action_norm_ge
#print axioms state_degreeM_arbitrary_source_norm_sq_le
#print axioms state_degreeM_arbitrary_source_norm_sq_ge
#print axioms momentum_degreeM_arbitrary_source_norm_sq_le
#print axioms momentum_degreeM_arbitrary_source_norm_sq_ge
#print axioms output_degreeM_arbitrary_source_norm_sq_le
#print axioms output_degreeM_arbitrary_source_norm_sq_ge
#print axioms momentumOutput_degreeM_arbitrary_source_norm_sq_le
#print axioms momentumOutput_degreeM_arbitrary_source_norm_sq_ge
#print axioms seconds_degreeM_arbitrary_source_norm_sq_le
#print axioms seconds_degreeM_arbitrary_source_norm_sq_ge
#print axioms hamiltonianOutput_degreeM_arbitrary_source_norm_sq_le
#print axioms hamiltonianOutput_degreeM_arbitrary_source_norm_sq_ge
#print axioms constant_mode_clockKinetic_lower_arbitrary_source
#print axioms constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
#print axioms constant_mode_static_add_radialKinetic_lower_arbitrary_source
#print axioms arbitrary_source_dominant_constant_mode_master_synthesis
end
end UnifiedTheory.Audit.KFCausalArbitrarySourceDominantConstantModeResponseLowerBound
