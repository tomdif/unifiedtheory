/- Complete polynomial-profile vector-space linearity (`0`, `+`, `-`, `•`) and
exact affine neutral polynomial decomposition (`C (d₀ i) + C (d₁ i) * X`) for
multi-packet reciprocal-neutral superpositions with arbitrary differing complex
sources `b : Fin n → ℂ` across all 9 state, momentum, factor, lift, and strong
Hamiltonian maps, together with triangle and quadratic Cauchy-Schwarz bounds. -/
import UnifiedTheory.Audit.KFCausalCommonComplexAffineNeutralPolynomialDecomposition
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift fullEnergy)
open KFCausalReciprocalNeutralKineticResponse
  (factorEnergy clockKineticEnergy physical_energy)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude state_constant_eq momentum_constant_eq
   output_constant_eq momentumOutput_constant_eq
   staticEnergy radialKineticEnergy growingEnergy residualEnergy)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (seconds_scalar_polynomial_eq hamiltonianOutput_scalar_polynomial_eq
   inputLift_scalar_polynomial_eq momentumLift_scalar_polynomial_eq)
open KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse
  (massChannelEnergy quarticChannelEnergy vacuumChannelEnergy)
open KFCausalCommonComplexAffineNeutralPolynomialDecomposition
  (packet_state_add packet_state_scale packet_state_smul
   packet_momentum_add packet_momentum_scale packet_momentum_smul
   packet_output_add packet_output_scale packet_output_smul
   packet_momentumOutput_add packet_momentumOutput_scale packet_momentumOutput_smul
   packet_second_add packet_second_scale packet_second_smul
   state_poly_add state_poly_scale state_poly_smul
   momentum_poly_add momentum_poly_scale momentum_poly_smul
   output_poly_add output_poly_scale output_poly_smul
   momentumOutput_poly_add momentumOutput_poly_scale momentumOutput_poly_smul
   seconds_poly_add seconds_poly_scale seconds_poly_smul
   hamiltonianOutput_poly_add hamiltonianOutput_poly_scale hamiltonianOutput_poly_smul
   inputLift_poly_add inputLift_poly_scale inputLift_poly_smul
   momentumLift_poly_add momentumLift_poly_scale momentumLift_poly_smul
   affinePolynomial
   state_affine_poly_eq momentum_affine_poly_eq
   output_affine_poly_eq momentumOutput_affine_poly_eq
   seconds_affine_poly_eq hamiltonianOutput_affine_poly_eq
   inputLift_affine_poly_eq momentumLift_affine_poly_eq
   hamiltonian_affine_poly_action)

private theorem poly_zero_eq_smul {n : ℕ} :
    (fun _ : Fin n => (0 : Polynomial ℂ)) =
      fun _ : Fin n => Polynomial.C (0 : ℂ) * (0 : Polynomial ℂ) := by
  funext _
  simp

private theorem poly_neg_eq_smul {n : ℕ} (P : Fin n → Polynomial ℂ) :
    (fun i : Fin n => -P i) =
      fun i : Fin n => Polynomial.C (-1 : ℂ) * P i := by
  funext i
  simp

private theorem norm_add_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 0 ≤ (‖x‖ - ‖y‖) ^ 2 := sq_nonneg (‖x‖ - ‖y‖)
  linarith

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d₀ d₁ : Fin n → ℂ)
  (P P₁ P₂ : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### 1. Zero, Negation, and Subtraction Linearity Across All 9 Maps for Arbitrary Sources -/

theorem state_poly_zero :
    state n ε h a w p C b (fun _ => 0) hε ha hh hw = 0 := by
  rw [poly_zero_eq_smul, state_poly_smul, zero_smul]

theorem momentum_poly_zero :
    momentum n ε h a w p C b (fun _ => 0) hε ha hh hw = 0 := by
  rw [poly_zero_eq_smul, momentum_poly_smul, zero_smul]

theorem output_poly_zero (j : Fin 8) :
    output n ε h a w p C b (fun _ => 0) hε ha hh hw hb j = 0 := by
  rw [poly_zero_eq_smul, output_poly_smul, zero_smul]

theorem momentumOutput_poly_zero (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun _ => 0) hε ha hh hw hb j = 0 := by
  rw [poly_zero_eq_smul, momentumOutput_poly_smul, zero_smul]

theorem seconds_poly_zero (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun _ => 0) hε ha hh hw hb_narrow j = 0 := by
  rw [poly_zero_eq_smul, seconds_poly_smul, zero_smul]

theorem hamiltonianOutput_poly_zero (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun _ => 0)
        hε ha hh hw hb_narrow mass2 quartic vacuum t = 0 := by
  rw [poly_zero_eq_smul, hamiltonianOutput_poly_smul, zero_smul]

theorem inputLift_poly_zero (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun _ => 0) hε ha hh hw hb mass2 quartic vacuum t = 0 := by
  rw [poly_zero_eq_smul, inputLift_poly_smul, zero_smul]

theorem momentumLift_poly_zero (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun _ => 0) hε ha hh hw hb mass2 quartic vacuum t = 0 := by
  rw [poly_zero_eq_smul, momentumLift_poly_smul, zero_smul]

theorem hamiltonian_poly_zero_action (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (fun _ => 0) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (fun _ => 0)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ = 0 := by
  dsimp only
  rw [hamiltonian_action n ε h a w p C b (fun _ => 0) hε ha hh hw hb_narrow mass2 quartic vacuum t]
  exact hamiltonianOutput_poly_zero n ε h a w p C b hε ha hh hw hb_narrow
    mass2 quartic vacuum t

theorem state_poly_neg :
    state n ε h a w p C b (fun i => -P i) hε ha hh hw =
      -state n ε h a w p C b P hε ha hh hw := by
  rw [poly_neg_eq_smul, state_poly_smul, neg_one_smul]

theorem momentum_poly_neg :
    momentum n ε h a w p C b (fun i => -P i) hε ha hh hw =
      -momentum n ε h a w p C b P hε ha hh hw := by
  rw [poly_neg_eq_smul, momentum_poly_smul, neg_one_smul]

theorem output_poly_neg (j : Fin 8) :
    output n ε h a w p C b (fun i => -P i) hε ha hh hw hb j =
      -output n ε h a w p C b P hε ha hh hw hb j := by
  rw [poly_neg_eq_smul, output_poly_smul, neg_one_smul]

theorem momentumOutput_poly_neg (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => -P i) hε ha hh hw hb j =
      -momentumOutput n ε h a w p C b P hε ha hh hw hb j := by
  rw [poly_neg_eq_smul, momentumOutput_poly_smul, neg_one_smul]

theorem seconds_poly_neg (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => -P i) hε ha hh hw hb_narrow j =
      -seconds n ε h a w p C b P hε ha hh hw hb_narrow j := by
  rw [poly_neg_eq_smul, seconds_poly_smul, neg_one_smul]

theorem hamiltonianOutput_poly_neg (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => -P i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      -hamiltonianOutput n ε h a w p C b P
        hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  rw [poly_neg_eq_smul, hamiltonianOutput_poly_smul, neg_one_smul]

theorem inputLift_poly_neg (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => -P i) hε ha hh hw hb mass2 quartic vacuum t =
      -inputLift n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t := by
  rw [poly_neg_eq_smul, inputLift_poly_smul, neg_one_smul]

theorem momentumLift_poly_neg (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => -P i) hε ha hh hw hb mass2 quartic vacuum t =
      -momentumLift n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t := by
  rw [poly_neg_eq_smul, momentumLift_poly_smul, neg_one_smul]

theorem state_poly_sub :
    state n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw =
      state n ε h a w p C b P₁ hε ha hh hw -
        state n ε h a w p C b P₂ hε ha hh hw := by
  simp only [sub_eq_add_neg]
  rw [state_poly_add, state_poly_neg]

theorem momentum_poly_sub :
    momentum n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw =
      momentum n ε h a w p C b P₁ hε ha hh hw -
        momentum n ε h a w p C b P₂ hε ha hh hw := by
  simp only [sub_eq_add_neg]
  rw [momentum_poly_add, momentum_poly_neg]

theorem output_poly_sub (j : Fin 8) :
    output n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw hb j =
      output n ε h a w p C b P₁ hε ha hh hw hb j -
        output n ε h a w p C b P₂ hε ha hh hw hb j := by
  simp only [sub_eq_add_neg]
  rw [output_poly_add, output_poly_neg]

theorem momentumOutput_poly_sub (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw hb j =
      momentumOutput n ε h a w p C b P₁ hε ha hh hw hb j -
        momentumOutput n ε h a w p C b P₂ hε ha hh hw hb j := by
  simp only [sub_eq_add_neg]
  rw [momentumOutput_poly_add, momentumOutput_poly_neg]

theorem seconds_poly_sub (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw hb_narrow j =
      seconds n ε h a w p C b P₁ hε ha hh hw hb_narrow j -
        seconds n ε h a w p C b P₂ hε ha hh hw hb_narrow j := by
  simp only [sub_eq_add_neg]
  rw [seconds_poly_add, seconds_poly_neg]

theorem hamiltonianOutput_poly_sub (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => P₁ i - P₂ i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p C b P₁
          hε ha hh hw hb_narrow mass2 quartic vacuum t -
        hamiltonianOutput n ε h a w p C b P₂
          hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  simp only [sub_eq_add_neg]
  rw [hamiltonianOutput_poly_add, hamiltonianOutput_poly_neg]

theorem inputLift_poly_sub (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p C b P₁ hε ha hh hw hb mass2 quartic vacuum t -
        inputLift n ε h a w p C b P₂ hε ha hh hw hb mass2 quartic vacuum t := by
  simp only [sub_eq_add_neg]
  rw [inputLift_poly_add, inputLift_poly_neg]

theorem momentumLift_poly_sub (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p C b P₁ hε ha hh hw hb mass2 quartic vacuum t -
        momentumLift n ε h a w p C b P₂ hε ha hh hw hb mass2 quartic vacuum t := by
  simp only [sub_eq_add_neg]
  rw [momentumLift_poly_add, momentumLift_poly_neg]

theorem hamiltonian_poly_add_action (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw;
    let ψ₁ := state n ε h a w p C b P₁ hε ha hh hw;
    let ψ₂ := state n ε h a w p C b P₂ hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (fun i => P₁ i + P₂ i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₁, hamiltonian_domain n ε h a w p C b P₁
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₂, hamiltonian_domain n ε h a w p C b P₂
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw hb_narrow
    mass2 quartic vacuum t

theorem hamiltonian_poly_smul_action (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (c : ℂ) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψc := state n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw;
    let ψ := state n ε h a w p C b P hε ha hh hw;
    H ⟨ψc, hamiltonian_domain n ε h a w p C b (fun i => Polynomial.C c * P i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      c • H ⟨ψ, hamiltonian_domain n ε h a w p C b P
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_poly_smul n ε h a w p C b P hε ha hh hw hb_narrow c
    mass2 quartic vacuum t

theorem hamiltonian_poly_sub_action (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (fun i => P₁ i - P₂ i) hε ha hh hw;
    let ψ₁ := state n ε h a w p C b P₁ hε ha hh hw;
    let ψ₂ := state n ε h a w p C b P₂ hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (fun i => P₁ i - P₂ i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₁, hamiltonian_domain n ε h a w p C b P₁
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ -
        H ⟨ψ₂, hamiltonian_domain n ε h a w p C b P₂
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_poly_sub n ε h a w p C b P₁ P₂ hε ha hh hw hb_narrow
    mass2 quartic vacuum t

/-! ### 2. Unabsorbed Affine Decomposition (`C (d₀ i)` + `C (d₁ i) * X`) Across All 9 Maps -/

abbrev affinePolyProfile {n : ℕ} (d₀ d₁ : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  affinePolynomial d₀ d₁

theorem state_affine_split_unabsorbed :
    state n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw =
      state n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw +
        state n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw :=
  state_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw

theorem momentum_affine_split_unabsorbed :
    momentum n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw =
      momentum n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw +
        momentum n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw :=
  momentum_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw

theorem output_affine_split_unabsorbed (j : Fin 8) :
    output n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb j =
      output n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw hb j +
        output n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb j :=
  output_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb j

theorem momentumOutput_affine_split_unabsorbed (j : Fin 8) :
    momentumOutput n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb j =
      momentumOutput n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw hb j +
        momentumOutput n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb j :=
  momentumOutput_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb j

theorem seconds_affine_split_unabsorbed (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb_narrow j =
      seconds n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw hb_narrow j +
        seconds n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb_narrow j :=
  seconds_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw hb_narrow j

theorem hamiltonianOutput_affine_split_unabsorbed
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (affinePolyProfile d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p C b (fun i => Polynomial.C (d₀ i))
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  hamiltonianOutput_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X)
    hε ha hh hw hb_narrow mass2 quartic vacuum t

theorem inputLift_affine_split_unabsorbed (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p C b (fun i => Polynomial.C (d₀ i))
          hε ha hh hw hb mass2 quartic vacuum t +
        inputLift n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t :=
  inputLift_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X)
    hε ha hh hw hb mass2 quartic vacuum t

theorem momentumLift_affine_split_unabsorbed (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p C b (fun i => Polynomial.C (d₀ i))
          hε ha hh hw hb mass2 quartic vacuum t +
        momentumLift n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t :=
  momentumLift_poly_add n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X)
    hε ha hh hw hb mass2 quartic vacuum t

theorem hamiltonian_affine_split_unabsorbed_action
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw;
    let ψ₀ := state n ε h a w p C b (fun i => Polynomial.C (d₀ i)) hε ha hh hw;
    let ψ₁ := state n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (affinePolyProfile d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₀, hamiltonian_domain n ε h a w p C b (fun i => Polynomial.C (d₀ i))
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₁, hamiltonian_domain n ε h a w p C b (fun i => Polynomial.C (d₁ i) * Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ :=
  hamiltonian_poly_add_action n ε h a w p C b
    (fun i => Polynomial.C (d₀ i)) (fun i => Polynomial.C (d₁ i) * Polynomial.X)
    hε ha hh hw hb_narrow mass2 quartic vacuum t

/-! ### 3. Quadratic Cauchy-Schwarz and Energy Domination Bounds for Arbitrary Sources -/

theorem state_affine_norm_sq_le :
    ‖state n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw‖ ^ 2 ≤
      2 * ‖state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 +
        2 * ‖state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw‖ ^ 2 := by
  rw [state_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem momentum_affine_norm_sq_le :
    ‖momentum n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw‖ ^ 2 ≤
      2 * ‖momentum n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw‖ ^ 2 +
        2 * ‖momentum n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw‖ ^ 2 := by
  rw [momentum_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem output_affine_norm_sq_le (j : Fin 8) :
    ‖output n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb j‖ ^ 2 ≤
      2 * ‖output n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 +
        2 * ‖output n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j‖ ^ 2 := by
  rw [output_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem momentumOutput_affine_norm_sq_le (j : Fin 8) :
    ‖momentumOutput n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb j‖ ^ 2 ≤
      2 * ‖momentumOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j‖ ^ 2 +
        2 * ‖momentumOutput n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j‖ ^ 2 := by
  rw [momentumOutput_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem seconds_affine_norm_sq_le (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    ‖seconds n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb_narrow j‖ ^ 2 ≤
      2 * ‖seconds n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb_narrow j‖ ^ 2 +
        2 * ‖seconds n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb_narrow j‖ ^ 2 := by
  rw [seconds_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem hamiltonianOutput_affine_norm_sq_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    ‖hamiltonianOutput n ε h a w p C b (affinePolyProfile d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 ≤
      2 * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 +
        2 * ‖hamiltonianOutput n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t‖ ^ 2 := by
  rw [hamiltonianOutput_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem inputLift_affine_norm_sq_le (mass2 quartic vacuum t : ℝ) :
    ‖inputLift n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 ≤
      2 * ‖inputLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 +
        2 * ‖inputLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 := by
  rw [inputLift_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem momentumLift_affine_norm_sq_le (mass2 quartic vacuum t : ℝ) :
    ‖momentumLift n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 ≤
      2 * ‖momentumLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 +
        2 * ‖momentumLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t‖ ^ 2 := by
  rw [momentumLift_affine_poly_eq]
  exact norm_add_sq_le_two _ _

theorem hamiltonian_affine_action_norm_sq_le
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw;
    let ψ₁ := state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw;
    ‖H ⟨ψ, hamiltonian_domain n ε h a w p C b (affinePolyProfile d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ^ 2 ≤
      2 * ‖H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ^ 2 +
        2 * ‖H ⟨ψ₁, hamiltonian_domain n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩‖ ^ 2 := by
  dsimp only
  rw [hamiltonian_affine_poly_action n ε h a w p C b hε ha hh hw d₀ d₁ hb_narrow
    mass2 quartic vacuum t]
  exact norm_add_sq_le_two _ _

theorem factorEnergy_affine_le (j : Fin 8) :
    factorEnergy n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb j ≤
      2 * factorEnergy n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j +
        2 * factorEnergy n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j :=
  output_affine_norm_sq_le n ε h a w p C b d₀ d₁ hε ha hh hw hb j

theorem potentialEnergy_affine_le (mass2 quartic vacuum : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    potentialEnergy mass2 quartic vacuum n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb ≤
      2 * potentialEnergy mass2 quartic vacuum n ε h a w p (scaleAmplitude C d₀) b
          (fun _ => 1) hε ha hh hw hb +
        2 * potentialEnergy mass2 quartic vacuum n ε h a w p (scaleAmplitude C d₁) b
          (fun _ => Polynomial.X) hε ha hh hw hb := by
  have h5 := output_affine_norm_sq_le n ε h a w p C b d₀ d₁ hε ha hh hw hb 5
  have h6 := output_affine_norm_sq_le n ε h a w p C b d₀ d₁ hε ha hh hw hb 6
  have h7 := output_affine_norm_sq_le n ε h a w p C b d₀ d₁ hε ha hh hw hb 7
  have hm := mul_le_mul_of_nonneg_left h5 (div_nonneg hmass (by norm_num : (0 : ℝ) ≤ 2))
  have hq := mul_le_mul_of_nonneg_left h6 (div_nonneg hquartic (by norm_num : (0 : ℝ) ≤ 4))
  have hv := mul_le_mul_of_nonneg_left h7 hvacuum
  unfold potentialEnergy
  linarith

theorem fullEnergy_affine_le (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h a w p C b (affinePolyProfile d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t ≤
      2 * fullEnergy n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        2 * fullEnergy n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hj := output_affine_norm_sq_le n ε h a w p C b d₀ d₁ hε ha hh hw hb j
  have hw_nonneg : 0 ≤ ‖KFCausalPhysicalEnergyFactors.energyWeight mass2 quartic vacuum t j‖ ^ 2 :=
    sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hj hw_nonneg
  linarith

#print axioms state_poly_zero
#print axioms momentum_poly_zero
#print axioms output_poly_zero
#print axioms momentumOutput_poly_zero
#print axioms seconds_poly_zero
#print axioms hamiltonianOutput_poly_zero
#print axioms inputLift_poly_zero
#print axioms momentumLift_poly_zero
#print axioms hamiltonian_poly_zero_action
#print axioms state_poly_neg
#print axioms momentum_poly_neg
#print axioms output_poly_neg
#print axioms momentumOutput_poly_neg
#print axioms seconds_poly_neg
#print axioms hamiltonianOutput_poly_neg
#print axioms inputLift_poly_neg
#print axioms momentumLift_poly_neg
#print axioms state_poly_sub
#print axioms momentum_poly_sub
#print axioms output_poly_sub
#print axioms momentumOutput_poly_sub
#print axioms seconds_poly_sub
#print axioms hamiltonianOutput_poly_sub
#print axioms inputLift_poly_sub
#print axioms momentumLift_poly_sub
#print axioms hamiltonian_poly_add_action
#print axioms hamiltonian_poly_smul_action
#print axioms hamiltonian_poly_sub_action
#print axioms state_affine_split_unabsorbed
#print axioms momentum_affine_split_unabsorbed
#print axioms output_affine_split_unabsorbed
#print axioms momentumOutput_affine_split_unabsorbed
#print axioms seconds_affine_split_unabsorbed
#print axioms hamiltonianOutput_affine_split_unabsorbed
#print axioms inputLift_affine_split_unabsorbed
#print axioms momentumLift_affine_split_unabsorbed
#print axioms hamiltonian_affine_split_unabsorbed_action
#print axioms state_affine_norm_sq_le
#print axioms momentum_affine_norm_sq_le
#print axioms output_affine_norm_sq_le
#print axioms momentumOutput_affine_norm_sq_le
#print axioms seconds_affine_norm_sq_le
#print axioms hamiltonianOutput_affine_norm_sq_le
#print axioms inputLift_affine_norm_sq_le
#print axioms momentumLift_affine_norm_sq_le
#print axioms hamiltonian_affine_action_norm_sq_le
#print axioms factorEnergy_affine_le
#print axioms potentialEnergy_affine_le
#print axioms fullEnergy_affine_le
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition
