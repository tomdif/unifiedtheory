/- Amplitude-absorption identities and uniform Hamiltonian and initial-derivative
response bounds for common-complex-source finite reciprocal neutral superpositions
with arbitrary packet-dependent scalar-constant neutral polynomials
`P = fun i => Polynomial.C (d i)`. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianInitialResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexScalarPolynomialHamiltonianResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
  (factorEnergy factorRate clockKineticEnergy clockKineticResponse
   physical_energy physical_response)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalCommonRealGaussianInitialResponse
  (expectation initialRate initial_derivative_tendsto)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude constantPolynomial packet_second_constant
   state_constant_eq momentum_constant_eq output_constant_eq momentumOutput_constant_eq
   factorEnergy_constant_eq factorRate_constant_eq
   staticEnergy staticResponse radialKineticEnergy radialKineticResponse
   growingEnergy growingResponse residualEnergy residualResponse
   staticEnergy_constant_eq staticResponse_constant_eq
   radialKineticEnergy_constant_eq radialKineticResponse_constant_eq
   clockKineticEnergy_constant_eq clockKineticResponse_constant_eq
   staticEnergy_nonnegative radialKineticEnergy_nonnegative
   radialKineticResponse_bounds staticResponse_lower_constant
   source_re_im)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### Multi-Channel Decompositions of Full Energy and Full Response -/

theorem potentialEnergy_nonnegative (mass2 quartic vacuum : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    0 ≤ potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  unfold potentialEnergy
  positivity

theorem growingEnergy_nonnegative (mass2 quartic vacuum : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    0 ≤ growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum :=
  add_nonneg (radialKineticEnergy_nonnegative n ε h a w p C b P hε ha hh hw hb)
    (potentialEnergy_nonnegative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
      hmass hquartic hvacuum)

theorem residualEnergy_nonnegative (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    0 ≤ residualEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t :=
  add_nonneg (staticEnergy_nonnegative n ε h a w p C b P hε ha hh hw hb)
    (mul_nonneg (Real.exp_pos (2 * t)).le
      (potentialEnergy_nonnegative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
        hmass hquartic hvacuum))

theorem fullEnergy_eq_clockKinetic_add_potential (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_energy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
    hmass hquartic hvacuum]
  unfold clockKineticEnergy potentialEnergy factorEnergy
  ring

theorem fullResponse_eq_clockKinetic_add_potential (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_response n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
    hmass hquartic hvacuum]
  unfold clockKineticResponse potentialResponse factorRate
  norm_num [Complex.add_im, Complex.div_im, Complex.mul_im]
  ring

theorem fullEnergy_eq_three_channel (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticEnergy staticEnergy radialKineticEnergy
  ring

theorem fullResponse_eq_three_channel (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticResponse staticResponse radialKineticResponse
  ring

theorem fullEnergy_eq_static_add_growing (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum := by
  rw [fullEnergy_eq_three_channel n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold growingEnergy
  ring

theorem fullResponse_eq_static_add_growing (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          growingResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum := by
  rw [fullResponse_eq_three_channel n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold growingResponse
  ring

theorem fullEnergy_eq_radialKinetic_add_residual (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb +
        residualEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t := by
  rw [fullEnergy_eq_three_channel n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold residualEnergy
  ring

theorem fullResponse_eq_radialKinetic_add_residual (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      Real.exp (2 * t) * radialKineticResponse n ε h a w p C b P hε ha hh hw hb +
        residualResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t := by
  rw [fullResponse_eq_three_channel n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold residualResponse
  ring

theorem fullEnergy_hasDerivAt (mass2 quartic vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) :
    HasDerivAt (fun s => fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)
      (2 * Real.exp (2 * t) *
        growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) t := by
  have he := (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he' : HasDerivAt (fun s : ℝ => Real.exp (2 * s)) (2 * Real.exp (2 * t)) t := by
    convert he using 1
    ring
  have hd := (he'.mul_const
    (growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)).const_add
    (staticEnergy n ε h a w p C b P hε ha hh hw hb)
  have hfun : (fun s => fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s) =
      fun s => staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * s) *
          growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum :=
    funext (fun s => fullEnergy_eq_static_add_growing n ε h a w p C b P hε ha hh hw hb
      mass2 quartic vacuum s hmass hquartic hvacuum)
  rwa [hfun]

/-! ### Exact Amplitude-Absorption Identities for All States, Form Lifts, Energies, and Responses -/

theorem state_scalar_polynomial_eq :
    state n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw :=
  state_constant_eq n ε h a w p C b d hε ha hh hw

theorem momentum_scalar_polynomial_eq :
    momentum n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw :=
  momentum_constant_eq n ε h a w p C b d hε ha hh hw

theorem output_scalar_polynomial_eq (j : Fin 8) :
    output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j :=
  output_constant_eq n ε h a w p C b d hε ha hh hw hb j

theorem momentumOutput_scalar_polynomial_eq (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j :=
  momentumOutput_constant_eq n ε h a w p C b d hε ha hh hw hb j

theorem seconds_scalar_polynomial_eq (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb_narrow j := by
  unfold seconds scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_second_constant ε (a i) h (w i) hε (ha i) hh (hw i) hb_narrow (C i) (p i) (b i) (d i) j)

theorem hamiltonianOutput_scalar_polynomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold hamiltonianOutput
  rw [funext (seconds_scalar_polynomial_eq n ε h a w p C b d hε ha hh hw hb_narrow)]

theorem inputLift_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  exact state_constant_eq n ε h a w p C b d hε ha hh hw

theorem momentumLift_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  exact momentum_constant_eq n ε h a w p C b d hε ha hh hw

theorem staticEnergy_scalar_polynomial_eq :
    staticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      staticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb :=
  staticEnergy_constant_eq n ε h a w p C b d hε ha hh hw hb

theorem staticResponse_scalar_polynomial_eq :
    staticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      staticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb :=
  staticResponse_constant_eq n ε h a w p C b d hε ha hh hw hb

theorem radialKineticEnergy_scalar_polynomial_eq :
    radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      radialKineticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb :=
  radialKineticEnergy_constant_eq n ε h a w p C b d hε ha hh hw hb

theorem radialKineticResponse_scalar_polynomial_eq :
    radialKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      radialKineticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb :=
  radialKineticResponse_constant_eq n ε h a w p C b d hε ha hh hw hb

theorem clockKineticEnergy_scalar_polynomial_eq (t : ℝ) :
    clockKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t =
      clockKineticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb t :=
  clockKineticEnergy_constant_eq n ε h a w p C b d hε ha hh hw hb t

theorem clockKineticResponse_scalar_polynomial_eq (t : ℝ) :
    clockKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t =
      clockKineticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb t :=
  clockKineticResponse_constant_eq n ε h a w p C b d hε ha hh hw hb t

theorem potentialEnergy_scalar_polynomial_eq (mass2 quartic vacuum : ℝ) :
    potentialEnergy mass2 quartic vacuum n ε h a w p C b
        (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      potentialEnergy mass2 quartic vacuum n ε h a w p (scaleAmplitude C d) b
        (fun _ => 1) hε ha hh hw hb := by
  unfold potentialEnergy
  simp only [output_constant_eq]

theorem potentialResponse_scalar_polynomial_eq (mass2 quartic vacuum : ℝ) :
    potentialResponse mass2 quartic vacuum n ε h a w p C b
        (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      potentialResponse mass2 quartic vacuum n ε h a w p (scaleAmplitude C d) b
        (fun _ => 1) hε ha hh hw hb := by
  unfold potentialResponse
  simp only [output_constant_eq, momentumOutput_constant_eq]

theorem unit_potentialEnergy_scalar_polynomial_eq :
    KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy n ε h a w p C b
        (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy n ε h a w p
        (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy
  simp only [output_constant_eq]

theorem unit_potentialResponse_scalar_polynomial_eq :
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse n ε h a w p C b
        (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      KFCausalReciprocalNeutralPotentialTransport.potentialResponse n ε h a w p
        (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold KFCausalReciprocalNeutralPotentialTransport.potentialResponse
  simp only [output_constant_eq, momentumOutput_constant_eq]

theorem growingEnergy_scalar_polynomial_eq (mass2 quartic vacuum : ℝ) :
    growingEnergy n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum =
      growingEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum := by
  unfold growingEnergy
  rw [radialKineticEnergy_constant_eq, potentialEnergy_scalar_polynomial_eq]

theorem growingResponse_scalar_polynomial_eq (mass2 quartic vacuum : ℝ) :
    growingResponse n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum =
      growingResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum := by
  unfold growingResponse
  rw [radialKineticResponse_constant_eq, potentialResponse_scalar_polynomial_eq]

theorem residualEnergy_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    residualEnergy n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      residualEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  unfold residualEnergy
  rw [staticEnergy_constant_eq, potentialEnergy_scalar_polynomial_eq]

theorem residualResponse_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    residualResponse n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      residualResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  unfold residualResponse
  rw [staticResponse_constant_eq, potentialResponse_scalar_polynomial_eq]

theorem fullEnergy_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      fullEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition,
    KFCausalReciprocalNeutralHamiltonian.energy_decomposition]
  simp only [output_constant_eq]

theorem fullResponse_scalar_polynomial_eq (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t =
      fullResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralHamiltonian.response_decomposition,
    KFCausalReciprocalNeutralHamiltonian.response_decomposition]
  simp only [output_constant_eq, momentumOutput_constant_eq]

theorem expectation_scalar_polynomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum s τ t : ℝ) :
    expectation n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ t =
      expectation n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ t := by
  unfold expectation
  rw [state_constant_eq]

theorem initialRate_scalar_polynomial_eq
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum s τ : ℝ) :
    initialRate n ε h a w p C b (fun i => Polynomial.C (d i))
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ =
      initialRate n ε h a w p (scaleAmplitude C d) b (fun _ => 1)
        hε ha hh hw hb_narrow mass2 quartic vacuum s τ := by
  unfold initialRate
  rw [hamiltonianOutput_scalar_polynomial_eq, state_constant_eq]

/-! ### Lifted Potential, Growing, Residual, Full, and Initial-Derivative Response Bounds -/

theorem potential_response_lower_scalar_polynomial :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * potentialEnergy mass2 quartic vacuum n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      potentialResponse mass2 quartic vacuum n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := KFCausalCommonComplexGaussianPotentialResponse.potential_response_lower
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb
  rw [potentialEnergy_scalar_polynomial_eq, potentialResponse_scalar_polynomial_eq]
  exact hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p
    (scaleAmplitude C d) hε ha hh hw hb

theorem potential_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * potentialEnergy mass2 quartic vacuum n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      potentialResponse mass2 quartic vacuum n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_scalar_polynomial
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb
  simpa only [source_re_im] using hb0

theorem growing_response_lower_scalar_polynomial :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * growingEnergy n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum ≤
      growingResponse n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum := by
  let hpot := potential_response_lower_scalar_polynomial
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb
  have hp := hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb
  have hrk := (radialKineticResponse_bounds n ε h a w p C (fun _ => source A D)
    (fun i => Polynomial.C (d i)) hε ha hh hw hb).1
  have hke := radialKineticEnergy_nonnegative n ε h a w p C (fun _ => source A D)
    (fun i => Polynomial.C (d i)) hε ha hh hw hb
  have hMε : 0 ≤ M / ε := div_nonneg hM.1 hε.le
  have hk0 : -(M / ε) * radialKineticEnergy n ε h a w p C (fun _ => source A D)
      (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hMε) hke
  unfold growingEnergy growingResponse
  linarith

theorem growing_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * growingEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum ≤
      growingResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum := by
  let hgrow := growing_response_lower_scalar_polynomial
  let M := Classical.choose hgrow
  have hM := Classical.choose_spec hgrow
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb
  simpa only [source_re_im] using hb0

theorem residual_response_lower_scalar_polynomial :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * residualEnergy n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum t ≤
      residualResponse n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum t := by
  let hpot := potential_response_lower_scalar_polynomial
  let M₀ := Classical.choose hpot
  have hM₀ := Classical.choose_spec hpot
  let M := max M₀ 1
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_right M₀ 1)
  have hM₀M : M₀ ≤ M := le_max_left M₀ 1
  have h1M : (1 / 4 : ℝ) ≤ M := by linarith [le_max_right M₀ 1]
  refine ⟨M, hM, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb t
  have hp0 := hM₀.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb
  have hpe := potentialEnergy_nonnegative n ε h a w p C (fun _ => source A D)
    (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum hmass hquartic hvacuum
  have hμ : M₀ / ε ≤ M / ε := div_le_div_of_nonneg_right hM₀M hε.le
  have hp := (mul_le_mul_of_nonneg_right (neg_le_neg hμ) hpe).trans hp0
  have hst0 := staticResponse_lower_constant n ε h a w p C (fun _ => source A D) d hε ha hh hw hb
  have hse := staticEnergy_nonnegative n ε h a w p C (fun _ => source A D)
    (fun i => Polynomial.C (d i)) hε ha hh hw hb
  have hκ : 1 / (4 * ε) ≤ M / ε := by
    rw [show 1 / (4 * ε) = (1 / 4) / ε by ring]
    exact div_le_div_of_nonneg_right h1M hε.le
  have hst := (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hse).trans hst0
  have hs := add_le_add hst (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2 * t)).le)
  unfold residualEnergy residualResponse
  convert hs using 1
  ring

theorem residual_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * residualEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum t ≤
      residualResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb
        mass2 quartic vacuum t := by
  let hres := residual_response_lower_scalar_polynomial
  let M := Classical.choose hres
  have hM := Classical.choose_spec hres
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb t
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb t
  simpa only [source_re_im] using hb0

theorem full_bound_scalar_polynomial :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * fullEnergy n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t ≤
      fullResponse n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t := by
  let hfull := KFCausalCommonComplexGaussianHamiltonianResponse.full_bound
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb t
  rw [fullEnergy_scalar_polynomial_eq, fullResponse_scalar_polynomial_eq]
  exact hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p
    (scaleAmplitude C d) hε ha hh hw hb t

theorem full_bound_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * fullEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t ≤
      fullResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic vacuum t := by
  let hfull := full_bound_scalar_polynomial
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb t
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb t
  simpa only [source_re_im] using hb0

theorem hamiltonian_bound_scalar_polynomial :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (t : ℝ),
      let ψ := state n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw;
      let Bψ := momentum n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw;
      let H := hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t;
      let ψH : H.domain := ⟨ψ, hamiltonian_domain n ε h a w p C
        (fun _ => source A D) (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum t⟩;
      -(M / ε) * (inner ℂ (H ψH) ψ).re ≤ (-2 / h) * (inner ℂ (H ψH) Bψ).im := by
  let hfull := full_bound_scalar_polynomial
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb t
  dsimp only
  rw [hamiltonian_action n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
      hε ha hh hw hb mass2 quartic vacuum t,
    ← KFCausalReciprocalNeutralStrongResponse.energy_identity
      n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
      hε ha hh hw hb mass2 quartic vacuum t,
    ← KFCausalReciprocalNeutralStrongResponse.response_identity
      n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
      hε ha hh hw hb mass2 quartic vacuum t]
  exact hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw
    (original_strip ε h hε hb) t

theorem hamiltonian_bound_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (t : ℝ),
      let ψ := state n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw;
      let Bψ := momentum n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw;
      let H := hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t;
      let ψH : H.domain := ⟨ψ, hamiltonian_domain n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum t⟩;
      -(M / ε) * (inner ℂ (H ψH) ψ).re ≤ (-2 / h) * (inner ℂ (H ψH) Bψ).im := by
  let hham := hamiltonian_bound_scalar_polynomial
  let M := Classical.choose hham
  have hM := Classical.choose_spec hham
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb t
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb t
  simpa only [source_re_im] using hb0

theorem common_complex_scalar_polynomial_limit_lower :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (s : ℝ),
      ∃ R : ℝ,
        -(M / ε) * fullEnergy n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
          hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s ≤ R ∧
        Tendsto
          (fun τ => deriv (expectation n ε h a w p C (fun _ => source A D)
            (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum s τ) s)
          (𝓝[≠] 0) (𝓝 R) := by
  let hfull := full_bound_scalar_polynomial
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb s
  exact ⟨_, hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d
      hε ha hh hw (original_strip ε h hε hb) s,
    initial_derivative_tendsto n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
      hε ha hh hw hb mass2 quartic vacuum s⟩

theorem common_source_scalar_polynomial_limit_lower :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (s : ℝ),
      ∃ R : ℝ,
        -(M / ε) * fullEnergy n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i))
          hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s ≤ R ∧
        Tendsto
          (fun τ => deriv (expectation n ε h a w p C (fun _ => b₀)
            (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum s τ) s)
          (𝓝[≠] 0) (𝓝 R) := by
  let hlim := common_complex_scalar_polynomial_limit_lower
  let M := Classical.choose hlim
  have hM := Classical.choose_spec hlim
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb s
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb s
  simpa only [source_re_im] using hb0

theorem common_complex_scalar_polynomial_eventually_lower :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (s δ : ℝ), 0 < δ →
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        -(M / ε) * fullEnergy n ε h a w p C (fun _ => source A D) (fun i => Polynomial.C (d i))
          hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s - δ <
        deriv (expectation n ε h a w p C (fun _ => source A D)
          (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum s τ) s := by
  let hlim := common_complex_scalar_polynomial_limit_lower
  let M := Classical.choose hlim
  have hM := Classical.choose_spec hlim
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb s δ hδ
  let hex := hM.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C d hε ha hh hw hb s
  let R := Classical.choose hex
  have hR := Classical.choose_spec hex
  exact hR.2.eventually (eventually_gt_nhds (by linarith [hR.1]))

theorem common_source_scalar_polynomial_eventually_lower :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (s δ : ℝ), 0 < δ →
      ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
        -(M / ε) * fullEnergy n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i))
          hε ha hh hw (original_strip ε h hε hb) mass2 quartic vacuum s - δ <
        deriv (expectation n ε h a w p C (fun _ => b₀)
          (fun i => Polynomial.C (d i)) hε ha hh hw hb mass2 quartic vacuum s τ) s := by
  let hev := common_complex_scalar_polynomial_eventually_lower
  let M := Classical.choose hev
  have hM := Classical.choose_spec hev
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C d hε ha hh hw hb s δ hδ
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C d hε ha hh hw hb s δ hδ
  simpa only [source_re_im] using hb0

#print axioms potentialEnergy_nonnegative
#print axioms growingEnergy_nonnegative
#print axioms residualEnergy_nonnegative
#print axioms fullEnergy_eq_clockKinetic_add_potential
#print axioms fullResponse_eq_clockKinetic_add_potential
#print axioms fullEnergy_eq_three_channel
#print axioms fullResponse_eq_three_channel
#print axioms fullEnergy_eq_static_add_growing
#print axioms fullResponse_eq_static_add_growing
#print axioms fullEnergy_eq_radialKinetic_add_residual
#print axioms fullResponse_eq_radialKinetic_add_residual
#print axioms fullEnergy_hasDerivAt
#print axioms state_scalar_polynomial_eq
#print axioms momentum_scalar_polynomial_eq
#print axioms output_scalar_polynomial_eq
#print axioms momentumOutput_scalar_polynomial_eq
#print axioms seconds_scalar_polynomial_eq
#print axioms hamiltonianOutput_scalar_polynomial_eq
#print axioms inputLift_scalar_polynomial_eq
#print axioms momentumLift_scalar_polynomial_eq
#print axioms staticEnergy_scalar_polynomial_eq
#print axioms staticResponse_scalar_polynomial_eq
#print axioms radialKineticEnergy_scalar_polynomial_eq
#print axioms radialKineticResponse_scalar_polynomial_eq
#print axioms clockKineticEnergy_scalar_polynomial_eq
#print axioms clockKineticResponse_scalar_polynomial_eq
#print axioms potentialEnergy_scalar_polynomial_eq
#print axioms potentialResponse_scalar_polynomial_eq
#print axioms unit_potentialEnergy_scalar_polynomial_eq
#print axioms unit_potentialResponse_scalar_polynomial_eq
#print axioms growingEnergy_scalar_polynomial_eq
#print axioms growingResponse_scalar_polynomial_eq
#print axioms residualEnergy_scalar_polynomial_eq
#print axioms residualResponse_scalar_polynomial_eq
#print axioms fullEnergy_scalar_polynomial_eq
#print axioms fullResponse_scalar_polynomial_eq
#print axioms expectation_scalar_polynomial_eq
#print axioms initialRate_scalar_polynomial_eq
#print axioms potential_response_lower_scalar_polynomial
#print axioms potential_response_lower_common_source
#print axioms growing_response_lower_scalar_polynomial
#print axioms growing_response_lower_common_source
#print axioms residual_response_lower_scalar_polynomial
#print axioms residual_response_lower_common_source
#print axioms full_bound_scalar_polynomial
#print axioms full_bound_common_source
#print axioms hamiltonian_bound_scalar_polynomial
#print axioms hamiltonian_bound_common_source
#print axioms common_complex_scalar_polynomial_limit_lower
#print axioms common_source_scalar_polynomial_limit_lower
#print axioms common_complex_scalar_polynomial_eventually_lower
#print axioms common_source_scalar_polynomial_eventually_lower
end
end UnifiedTheory.Audit.KFCausalCommonComplexScalarPolynomialHamiltonianResponse
