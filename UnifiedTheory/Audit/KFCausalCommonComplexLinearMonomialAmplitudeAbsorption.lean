/- Linear-monomial amplitude absorption (`(C, fun i => C (d₁ i) * X)` equals
`(scaleAmplitude C d₁, fun _ => X)`) across all packet, superposition, energy,
response, and initial-derivative functionals, together with the canonical
two-basis (`unitConstantPolyProfile n` and `unitLinearPolyProfile n`) reduction
for affine neutral polynomial profiles under both arbitrary and common complex
sources. -/
import UnifiedTheory.Audit.KFCausalCommonComplexAffineNeutralPolynomialDecomposition
import UnifiedTheory.Audit.KFCausalCommonComplexScalarPolynomialHamiltonianResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexLinearMonomialAmplitudeAbsorption
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
  (factorEnergy factorRate clockKineticEnergy clockKineticResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalCommonRealGaussianInitialResponse (expectation initialRate)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude staticEnergy staticResponse radialKineticEnergy radialKineticResponse
   growingEnergy growingResponse residualEnergy residualResponse)
open KFCausalCommonComplexAffineNeutralPolynomialDecomposition
  (packet_state_scale packet_momentum_scale packet_output_scale
   packet_momentumOutput_scale packet_second_scale
   state_poly_scale momentum_poly_scale output_poly_scale
   momentumOutput_poly_scale seconds_poly_scale hamiltonianOutput_poly_scale
   inputLift_poly_scale momentumLift_poly_scale
   affinePolynomial
   state_affine_poly_eq momentum_affine_poly_eq
   output_affine_poly_eq momentumOutput_affine_poly_eq
   seconds_affine_poly_eq hamiltonianOutput_affine_poly_eq
   inputLift_affine_poly_eq momentumLift_affine_poly_eq
   hamiltonian_affine_poly_action)

/-! ### 1. Canonical Constant and Linear Monomial Profiles and Single-Packet Absorption -/

abbrev linearPolyProfile {n : ℕ} (d₁ : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  fun i => Polynomial.C (d₁ i) * Polynomial.X

abbrev unitLinearPolyProfile (n : ℕ) : Fin n → Polynomial ℂ :=
  fun _ => Polynomial.X

abbrev unitConstantPolyProfile (n : ℕ) : Fin n → Polynomial ℂ :=
  fun _ => 1

abbrev commonSource (n : ℕ) (b₀ : ℂ) : Fin n → ℂ :=
  fun _ => b₀

theorem linear_monomial_eval_eq (a d₁ x : ℂ) :
    a * (Polynomial.C d₁ * Polynomial.X).eval x =
      (a * d₁) * (Polynomial.X : Polynomial ℂ).eval x := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem linear_monomial_derivative_eval_eq (a d₁ x : ℂ) :
    a * (Polynomial.derivative (Polynomial.C d₁ * Polynomial.X)).eval x =
      (a * d₁) * (Polynomial.derivative (Polynomial.X : Polynomial ℂ)).eval x := by
  simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
  ring

theorem linear_monomial_second_derivative_eval_eq (a d₁ x : ℂ) :
    a * (Polynomial.derivative (Polynomial.derivative (Polynomial.C d₁ * Polynomial.X))).eval x =
      (a * d₁) *
        (Polynomial.derivative (Polynomial.derivative (Polynomial.X : Polynomial ℂ))).eval x := by
  simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X,
    Polynomial.derivative_one, mul_zero, Polynomial.eval_zero]

theorem packet_profile_linear_monomial_eq (ε a h w : ℝ) (C : ℂ) (p : ℝ) (b d₁ : ℂ)
    (x : Configuration) :
    KFCausalReciprocalNeutralPackets.profile ε a h w C p b (Polynomial.C d₁ * Polynomial.X) x =
      KFCausalReciprocalNeutralPackets.profile ε a h w (C * d₁) p b Polynomial.X x := by
  unfold KFCausalReciprocalNeutralPackets.profile
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem packet_state_linear_monomial_eq (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b d₁ : ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b
        (Polynomial.C d₁ * Polynomial.X) =
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw (C * d₁) p b Polynomial.X :=
  packet_state_scale ε a h w hε ha hh hw C p b d₁ Polynomial.X

theorem packet_momentum_linear_monomial_eq (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b d₁ : ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b
        (Polynomial.C d₁ * Polynomial.X) =
      KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw (C * d₁) p b Polynomial.X :=
  packet_momentum_scale ε a h w hε ha hh hw C p b d₁ Polynomial.X

theorem packet_output_linear_monomial_eq (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b d₁ : ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b
        (Polynomial.C d₁ * Polynomial.X) hb j =
      KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw (C * d₁) p b
        Polynomial.X hb j :=
  packet_output_scale ε a h w hε ha hh hw C p b d₁ Polynomial.X hb j

theorem packet_momentumOutput_linear_monomial_eq (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b d₁ : ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b
        (Polynomial.C d₁ * Polynomial.X) hb j =
      KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw (C * d₁) p b
        Polynomial.X hb j :=
  packet_momentumOutput_scale ε a h w hε ha hh hw C p b d₁ Polynomial.X hb j

theorem packet_second_linear_monomial_eq (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (C : ℂ) (p : ℝ) (b d₁ : ℂ)
    (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b
        (Polynomial.C d₁ * Polynomial.X) j =
      KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb (C * d₁) p b
        Polynomial.X j :=
  packet_second_scale ε a h w hε ha hh hw hb C p b d₁ Polynomial.X j

/-! ### 2. Multi-Packet Linear-Monomial Amplitude Absorption Across All Maps and Functionals -/

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d₀ d₁ : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem state_linear_monomial_eq :
    state n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw :=
  state_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n) hε ha hh hw

theorem momentum_linear_monomial_eq :
    momentum n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw :=
  momentum_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n) hε ha hh hw

theorem output_linear_monomial_eq (j : Fin 8) :
    output n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw hb j :=
  output_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n) hε ha hh hw hb j

theorem momentumOutput_linear_monomial_eq (j : Fin 8) :
    momentumOutput n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb j :=
  momentumOutput_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n) hε ha hh hw hb j

theorem seconds_linear_monomial_eq (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb_narrow j :=
  seconds_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n) hε ha hh hw hb_narrow j

theorem hamiltonianOutput_linear_monomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  hamiltonianOutput_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n)
    hε ha hh hw hb_narrow mass2 quartic vacuum t

theorem inputLift_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t :=
  inputLift_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n)
    hε ha hh hw hb mass2 quartic vacuum t

theorem momentumLift_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t :=
  momentumLift_poly_scale n ε h a w p C b d₁ (unitLinearPolyProfile n)
    hε ha hh hw hb mass2 quartic vacuum t

theorem hamiltonian_linear_monomial_action
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw;
    let ψ₁ := state n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₁, hamiltonian_domain n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_linear_monomial_eq n ε h a w p C b d₁ hε ha hh hw
    hb_narrow mass2 quartic vacuum t

theorem factorEnergy_linear_monomial_eq (j : Fin 8) :
    factorEnergy n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb j =
      factorEnergy n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw hb j := by
  unfold factorEnergy
  rw [output_linear_monomial_eq]

theorem factorRate_linear_monomial_eq (j : Fin 8) :
    factorRate n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb j =
      factorRate n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw hb j := by
  unfold factorRate
  rw [output_linear_monomial_eq, momentumOutput_linear_monomial_eq]

theorem staticEnergy_linear_monomial_eq :
    staticEnergy n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb =
      staticEnergy n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold staticEnergy
  simp only [factorEnergy_linear_monomial_eq]

theorem staticResponse_linear_monomial_eq :
    staticResponse n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb =
      staticResponse n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold staticResponse
  simp only [factorRate_linear_monomial_eq]

theorem radialKineticEnergy_linear_monomial_eq :
    radialKineticEnergy n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb =
      radialKineticEnergy n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold radialKineticEnergy
  simp only [factorEnergy_linear_monomial_eq]

theorem radialKineticResponse_linear_monomial_eq :
    radialKineticResponse n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb =
      radialKineticResponse n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold radialKineticResponse
  simp only [factorRate_linear_monomial_eq]

theorem clockKineticEnergy_linear_monomial_eq (t : ℝ) :
    clockKineticEnergy n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb t =
      clockKineticEnergy n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb t := by
  unfold clockKineticEnergy
  simp only [factorEnergy_linear_monomial_eq]

theorem clockKineticResponse_linear_monomial_eq (t : ℝ) :
    clockKineticResponse n ε h a w p C b (linearPolyProfile d₁) hε ha hh hw hb t =
      clockKineticResponse n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb t := by
  unfold clockKineticResponse
  simp only [factorRate_linear_monomial_eq]

theorem potentialEnergy_linear_monomial_eq (mass2 quartic vacuum : ℝ) :
    potentialEnergy mass2 quartic vacuum n ε h a w p C b
        (linearPolyProfile d₁) hε ha hh hw hb =
      potentialEnergy mass2 quartic vacuum n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold potentialEnergy
  simp only [output_linear_monomial_eq]

theorem potentialResponse_linear_monomial_eq (mass2 quartic vacuum : ℝ) :
    potentialResponse mass2 quartic vacuum n ε h a w p C b
        (linearPolyProfile d₁) hε ha hh hw hb =
      potentialResponse mass2 quartic vacuum n ε h a w p (scaleAmplitude C d₁) b
        (unitLinearPolyProfile n) hε ha hh hw hb := by
  unfold potentialResponse
  simp only [output_linear_monomial_eq, momentumOutput_linear_monomial_eq]

theorem growingEnergy_linear_monomial_eq (mass2 quartic vacuum : ℝ) :
    growingEnergy n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum =
      growingEnergy n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum := by
  unfold growingEnergy
  rw [radialKineticEnergy_linear_monomial_eq, potentialEnergy_linear_monomial_eq]

theorem growingResponse_linear_monomial_eq (mass2 quartic vacuum : ℝ) :
    growingResponse n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum =
      growingResponse n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum := by
  unfold growingResponse
  rw [radialKineticResponse_linear_monomial_eq, potentialResponse_linear_monomial_eq]

theorem residualEnergy_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    residualEnergy n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum t =
      residualEnergy n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t := by
  unfold residualEnergy
  rw [staticEnergy_linear_monomial_eq, potentialEnergy_linear_monomial_eq]

theorem residualResponse_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    residualResponse n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum t =
      residualResponse n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t := by
  unfold residualResponse
  rw [staticResponse_linear_monomial_eq, potentialResponse_linear_monomial_eq]

theorem fullEnergy_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum t =
      fullEnergy n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    KFCausalReciprocalNeutralHamiltonian.energy_decomposition]
  simp only [output_linear_monomial_eq]

theorem fullResponse_linear_monomial_eq (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb mass2 quartic vacuum t =
      fullResponse n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.response_decomposition,
    KFCausalReciprocalNeutralHamiltonian.response_decomposition]
  simp only [output_linear_monomial_eq, momentumOutput_linear_monomial_eq]

theorem expectation_linear_monomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum s τ t : ℝ) :
    expectation n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ t =
      expectation n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ t := by
  unfold expectation
  rw [state_linear_monomial_eq]

theorem initialRate_linear_monomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum s τ : ℝ) :
    initialRate n ε h a w p C b (linearPolyProfile d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ =
      initialRate n ε h a w p (scaleAmplitude C d₁) b (unitLinearPolyProfile n)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ := by
  unfold initialRate
  rw [hamiltonianOutput_linear_monomial_eq, state_linear_monomial_eq]

/-! ### 3. Common-Complex-Source Canonical Two-Basis Reduction (`1` and `X`) -/

theorem state_commonSource_affine_two_basis_eq (b₀ : ℂ) :
    state n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw +
        state n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw :=
  state_affine_poly_eq n ε h a w p C (commonSource n b₀) hε ha hh hw d₀ d₁

theorem momentum_commonSource_affine_two_basis_eq (b₀ : ℂ) :
    momentum n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw +
        momentum n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw :=
  momentum_affine_poly_eq n ε h a w p C (commonSource n b₀) hε ha hh hw d₀ d₁

theorem output_commonSource_affine_two_basis_eq (b₀ : ℂ) (j : Fin 8) :
    output n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw hb j +
        output n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw hb j :=
  output_affine_poly_eq n ε h a w p C (commonSource n b₀) hε ha hh hw hb d₀ d₁ j

theorem momentumOutput_commonSource_affine_two_basis_eq (b₀ : ℂ) (j : Fin 8) :
    momentumOutput n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw hb j +
        momentumOutput n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw hb j :=
  momentumOutput_affine_poly_eq n ε h a w p C (commonSource n b₀) hε ha hh hw hb d₀ d₁ j

theorem hamiltonianOutput_commonSource_affine_two_basis_eq (b₀ : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  hamiltonianOutput_affine_poly_eq n ε h a w p C (commonSource n b₀)
    hε ha hh hw d₀ d₁ hb_narrow mass2 quartic vacuum t

theorem hamiltonian_commonSource_affine_two_basis_action (b₀ : ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
      (unitConstantPolyProfile n) hε ha hh hw;
    let ψ₁ := state n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
      (unitLinearPolyProfile n) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C (commonSource n b₀) (affinePolynomial d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C d₀) (commonSource n b₀)
          (unitConstantPolyProfile n) hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₁, hamiltonian_domain n ε h a w p (scaleAmplitude C d₁) (commonSource n b₀)
          (unitLinearPolyProfile n) hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ :=
  hamiltonian_affine_poly_action n ε h a w p C (commonSource n b₀)
    hε ha hh hw d₀ d₁ hb_narrow mass2 quartic vacuum t

#print axioms linear_monomial_eval_eq
#print axioms linear_monomial_derivative_eval_eq
#print axioms linear_monomial_second_derivative_eval_eq
#print axioms packet_profile_linear_monomial_eq
#print axioms packet_state_linear_monomial_eq
#print axioms packet_momentum_linear_monomial_eq
#print axioms packet_output_linear_monomial_eq
#print axioms packet_momentumOutput_linear_monomial_eq
#print axioms packet_second_linear_monomial_eq
#print axioms state_linear_monomial_eq
#print axioms momentum_linear_monomial_eq
#print axioms output_linear_monomial_eq
#print axioms momentumOutput_linear_monomial_eq
#print axioms seconds_linear_monomial_eq
#print axioms hamiltonianOutput_linear_monomial_eq
#print axioms inputLift_linear_monomial_eq
#print axioms momentumLift_linear_monomial_eq
#print axioms hamiltonian_linear_monomial_action
#print axioms factorEnergy_linear_monomial_eq
#print axioms factorRate_linear_monomial_eq
#print axioms staticEnergy_linear_monomial_eq
#print axioms staticResponse_linear_monomial_eq
#print axioms radialKineticEnergy_linear_monomial_eq
#print axioms radialKineticResponse_linear_monomial_eq
#print axioms clockKineticEnergy_linear_monomial_eq
#print axioms clockKineticResponse_linear_monomial_eq
#print axioms potentialEnergy_linear_monomial_eq
#print axioms potentialResponse_linear_monomial_eq
#print axioms growingEnergy_linear_monomial_eq
#print axioms growingResponse_linear_monomial_eq
#print axioms residualEnergy_linear_monomial_eq
#print axioms residualResponse_linear_monomial_eq
#print axioms fullEnergy_linear_monomial_eq
#print axioms fullResponse_linear_monomial_eq
#print axioms expectation_linear_monomial_eq
#print axioms initialRate_linear_monomial_eq
#print axioms state_commonSource_affine_two_basis_eq
#print axioms momentum_commonSource_affine_two_basis_eq
#print axioms output_commonSource_affine_two_basis_eq
#print axioms momentumOutput_commonSource_affine_two_basis_eq
#print axioms hamiltonianOutput_commonSource_affine_two_basis_eq
#print axioms hamiltonian_commonSource_affine_two_basis_action
end
end UnifiedTheory.Audit.KFCausalCommonComplexLinearMonomialAmplitudeAbsorption
