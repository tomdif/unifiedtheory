/- Three-channel potential decomposition, coupling linearity in `(mass2, quartic, vacuum)`,
zero-quartic and zero-vacuum channel specializations, arbitrary-source clock-integral
identities for each individual potential channel, and uniform single-channel and two-channel
response bounds for common-complex-source scalar-polynomial superpositions. -/
import UnifiedTheory.Audit.KFCausalCommonComplexScalarPolynomialHamiltonianResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
  (factorEnergy factorRate clockKineticEnergy clockKineticResponse
   physical_energy physical_response)
open KFCausalWeightedReciprocalNeutralWholeClock
  (positiveSlice weakResponse reducedResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport
  (potentialEnergy potentialResponse potentialEnergy_integral
   potentialResponse_weak_integral potentialResponse_reduced_integral)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude factorEnergy_constant_eq factorRate_constant_eq
   staticEnergy staticResponse radialKineticEnergy radialKineticResponse
   growingEnergy growingResponse residualEnergy residualResponse
   potentialEnergy_zero_couplings potentialResponse_zero_couplings
   growingEnergy_zero_couplings growingResponse_zero_couplings
   residualEnergy_zero_couplings residualResponse_zero_couplings
   fullEnergy_zero_couplings_eq_clockKinetic fullResponse_zero_couplings_eq_clockKinetic
   source_re_im)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (fullEnergy_eq_clockKinetic_add_potential fullResponse_eq_clockKinetic_add_potential
   fullEnergy_eq_three_channel fullResponse_eq_three_channel
   potential_response_lower_scalar_polynomial potential_response_lower_common_source
   growing_response_lower_common_source residual_response_lower_common_source
   full_bound_common_source hamiltonian_bound_common_source)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

/-! ### 1. Individual Potential Channel Energies and Responses (Mass, Quartic, Vacuum) -/

def massChannelEnergy : ℝ :=
  factorEnergy n ε h a w p C b P hε ha hh hw hb 5 / 2

def massChannelResponse : ℝ :=
  factorRate n ε h a w p C b P hε ha hh hw hb 5 / 2

def quarticChannelEnergy : ℝ :=
  factorEnergy n ε h a w p C b P hε ha hh hw hb 6 / 4

def quarticChannelResponse : ℝ :=
  factorRate n ε h a w p C b P hε ha hh hw hb 6 / 4

def vacuumChannelEnergy : ℝ :=
  factorEnergy n ε h a w p C b P hε ha hh hw hb 7

def vacuumChannelResponse : ℝ :=
  factorRate n ε h a w p C b P hε ha hh hw hb 7

theorem massChannelEnergy_nonnegative :
    0 ≤ massChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold massChannelEnergy factorEnergy
  positivity

theorem quarticChannelEnergy_nonnegative :
    0 ≤ quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold quarticChannelEnergy factorEnergy
  positivity

theorem vacuumChannelEnergy_nonnegative :
    0 ≤ vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold vacuumChannelEnergy factorEnergy
  positivity

theorem massChannelEnergy_scalar_polynomial_eq :
    massChannelEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      massChannelEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold massChannelEnergy
  rw [factorEnergy_constant_eq]

theorem massChannelResponse_scalar_polynomial_eq :
    massChannelResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      massChannelResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold massChannelResponse
  rw [factorRate_constant_eq]

theorem quarticChannelEnergy_scalar_polynomial_eq :
    quarticChannelEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      quarticChannelEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold quarticChannelEnergy
  rw [factorEnergy_constant_eq]

theorem quarticChannelResponse_scalar_polynomial_eq :
    quarticChannelResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      quarticChannelResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold quarticChannelResponse
  rw [factorRate_constant_eq]

theorem vacuumChannelEnergy_scalar_polynomial_eq :
    vacuumChannelEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      vacuumChannelEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold vacuumChannelEnergy
  rw [factorEnergy_constant_eq]

theorem vacuumChannelResponse_scalar_polynomial_eq :
    vacuumChannelResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      vacuumChannelResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold vacuumChannelResponse
  rw [factorRate_constant_eq]

/-! ### 2. Exact Three-Channel Decomposition of Potential Energy and Potential Response -/

theorem potentialEnergy_eq_three_channels (mass2 quartic vacuum : ℝ) :
    potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold potentialEnergy vacuumChannelEnergy massChannelEnergy quarticChannelEnergy factorEnergy
  ring

theorem potentialResponse_eq_three_channels (mass2 quartic vacuum : ℝ) :
    potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  unfold potentialResponse vacuumChannelResponse massChannelResponse quarticChannelResponse factorRate
  norm_num [Complex.add_im, Complex.div_im, Complex.mul_im]
  ring

theorem potentialEnergy_unit_mass :
    potentialEnergy 1 0 0 n ε h a w p C b P hε ha hh hw hb =
      massChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_unit_mass :
    potentialResponse 1 0 0 n ε h a w p C b P hε ha hh hw hb =
      massChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_unit_quartic :
    potentialEnergy 0 1 0 n ε h a w p C b P hε ha hh hw hb =
      quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_unit_quartic :
    potentialResponse 0 1 0 n ε h a w p C b P hε ha hh hw hb =
      quarticChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_unit_vacuum :
    potentialEnergy 0 0 1 n ε h a w p C b P hε ha hh hw hb =
      vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_unit_vacuum :
    potentialResponse 0 0 1 n ε h a w p C b P hε ha hh hw hb =
      vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_pure_mass (mass2 : ℝ) :
    potentialEnergy mass2 0 0 n ε h a w p C b P hε ha hh hw hb =
      mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_pure_mass (mass2 : ℝ) :
    potentialResponse mass2 0 0 n ε h a w p C b P hε ha hh hw hb =
      mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_pure_quartic (quartic : ℝ) :
    potentialEnergy 0 quartic 0 n ε h a w p C b P hε ha hh hw hb =
      quartic * quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_pure_quartic (quartic : ℝ) :
    potentialResponse 0 quartic 0 n ε h a w p C b P hε ha hh hw hb =
      quartic * quarticChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_pure_vacuum (vacuum : ℝ) :
    potentialEnergy 0 0 vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_pure_vacuum (vacuum : ℝ) :
    potentialResponse 0 0 vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

/-! ### 3. Zero-Quartic (`quartic = 0`), Zero-Vacuum (`vacuum = 0`), and Zero-Mass (`mass2 = 0`) Regimes -/

theorem potentialEnergy_zero_quartic (mass2 vacuum : ℝ) :
    potentialEnergy mass2 0 vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_zero_quartic (mass2 vacuum : ℝ) :
    potentialResponse mass2 0 vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_zero_vacuum (mass2 quartic : ℝ) :
    potentialEnergy mass2 quartic 0 n ε h a w p C b P hε ha hh hw hb =
      mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_zero_vacuum (mass2 quartic : ℝ) :
    potentialResponse mass2 quartic 0 n ε h a w p C b P hε ha hh hw hb =
      mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_zero_mass (quartic vacuum : ℝ) :
    potentialEnergy 0 quartic vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_zero_mass (quartic vacuum : ℝ) :
    potentialResponse 0 quartic vacuum n ε h a w p C b P hε ha hh hw hb =
      vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
        quartic * quarticChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [potentialResponse_eq_three_channels]
  ring

theorem growingEnergy_zero_quartic (mass2 vacuum : ℝ) :
    growingEnergy n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum =
      radialKineticEnergy n ε h a w p C b P hε ha hh hw hb +
        vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold growingEnergy
  rw [potentialEnergy_zero_quartic]
  ring

theorem growingResponse_zero_quartic (mass2 vacuum : ℝ) :
    growingResponse n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum =
      radialKineticResponse n ε h a w p C b P hε ha hh hw hb +
        vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
        mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb := by
  unfold growingResponse
  rw [potentialResponse_zero_quartic]
  ring

theorem residualEnergy_zero_quartic (mass2 vacuum t : ℝ) :
    residualEnergy n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          (vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
            mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb) := by
  unfold residualEnergy
  rw [potentialEnergy_zero_quartic]

theorem residualResponse_zero_quartic (mass2 vacuum t : ℝ) :
    residualResponse n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum t =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) *
          (vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
            mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb) := by
  unfold residualResponse
  rw [potentialResponse_zero_quartic]

theorem fullEnergy_zero_quartic (mass2 vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hvacuum : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          (vacuum * vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb +
            mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb) := by
  rw [fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 0 vacuum t hmass le_rfl hvacuum, potentialEnergy_zero_quartic]

theorem fullResponse_zero_quartic (mass2 vacuum t : ℝ)
    (hmass : 0 ≤ mass2) (hvacuum : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 0 vacuum t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          (vacuum * vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb +
            mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb) := by
  rw [fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 0 vacuum t hmass le_rfl hvacuum, potentialResponse_zero_quartic]

theorem fullEnergy_zero_vacuum (mass2 quartic t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic 0 t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          (mass2 * massChannelEnergy n ε h a w p C b P hε ha hh hw hb +
            quartic * quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb) := by
  rw [fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 quartic 0 t hmass hquartic le_rfl, potentialEnergy_zero_vacuum]

theorem fullResponse_zero_vacuum (mass2 quartic t : ℝ)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic 0 t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t +
        Real.exp (2 * t) *
          (mass2 * massChannelResponse n ε h a w p C b P hε ha hh hw hb +
            quartic * quarticChannelResponse n ε h a w p C b P hε ha hh hw hb) := by
  rw [fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
    mass2 quartic 0 t hmass hquartic le_rfl, potentialResponse_zero_vacuum]

/-! ### 4. Exact Coupling Linearity and Affine Additivity in `(mass2, quartic, vacuum)` -/

theorem potentialEnergy_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ : ℝ) :
    potentialEnergy (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) n ε h a w p C b P hε ha hh hw hb =
      potentialEnergy m₁ g₁ k₁ n ε h a w p C b P hε ha hh hw hb +
        potentialEnergy m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  simp only [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ : ℝ) :
    potentialResponse (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) n ε h a w p C b P hε ha hh hw hb =
      potentialResponse m₁ g₁ k₁ n ε h a w p C b P hε ha hh hw hb +
        potentialResponse m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  simp only [potentialResponse_eq_three_channels]
  ring

theorem potentialEnergy_smul_couplings (c m g k : ℝ) :
    potentialEnergy (c * m) (c * g) (c * k) n ε h a w p C b P hε ha hh hw hb =
      c * potentialEnergy m g k n ε h a w p C b P hε ha hh hw hb := by
  simp only [potentialEnergy_eq_three_channels]
  ring

theorem potentialResponse_smul_couplings (c m g k : ℝ) :
    potentialResponse (c * m) (c * g) (c * k) n ε h a w p C b P hε ha hh hw hb =
      c * potentialResponse m g k n ε h a w p C b P hε ha hh hw hb := by
  simp only [potentialResponse_eq_three_channels]
  ring

theorem growingEnergy_sub_zero_couplings (m g k : ℝ) :
    growingEnergy n ε h a w p C b P hε ha hh hw hb m g k -
      growingEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 =
      potentialEnergy m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [growingEnergy_zero_couplings]
  unfold growingEnergy
  ring

theorem growingResponse_sub_zero_couplings (m g k : ℝ) :
    growingResponse n ε h a w p C b P hε ha hh hw hb m g k -
      growingResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 =
      potentialResponse m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [growingResponse_zero_couplings]
  unfold growingResponse
  ring

theorem growingEnergy_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ : ℝ) :
    growingEnergy n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) =
      growingEnergy n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ +
        potentialEnergy m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  unfold growingEnergy
  rw [potentialEnergy_add_couplings]
  ring

theorem growingResponse_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ : ℝ) :
    growingResponse n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) =
      growingResponse n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ +
        potentialResponse m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  unfold growingResponse
  rw [potentialResponse_add_couplings]
  ring

theorem residualEnergy_sub_zero_couplings (m g k t : ℝ) :
    residualEnergy n ε h a w p C b P hε ha hh hw hb m g k t -
      residualEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      Real.exp (2 * t) * potentialEnergy m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [residualEnergy_zero_couplings]
  unfold residualEnergy
  ring

theorem residualResponse_sub_zero_couplings (m g k t : ℝ) :
    residualResponse n ε h a w p C b P hε ha hh hw hb m g k t -
      residualResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      Real.exp (2 * t) * potentialResponse m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [residualResponse_zero_couplings]
  unfold residualResponse
  ring

theorem residualEnergy_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ t : ℝ) :
    residualEnergy n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t =
      residualEnergy n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t +
        Real.exp (2 * t) * potentialEnergy m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  unfold residualEnergy
  rw [potentialEnergy_add_couplings]
  ring

theorem residualResponse_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ t : ℝ) :
    residualResponse n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t =
      residualResponse n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t +
        Real.exp (2 * t) * potentialResponse m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  unfold residualResponse
  rw [potentialResponse_add_couplings]
  ring

theorem fullEnergy_sub_zero_couplings (m g k t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb m g k t -
      fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      Real.exp (2 * t) * potentialEnergy m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk,
    fullEnergy_zero_couplings_eq_clockKinetic]
  ring

theorem fullResponse_sub_zero_couplings (m g k t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    fullResponse n ε h a w p C b P hε ha hh hw hb m g k t -
      fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      Real.exp (2 * t) * potentialResponse m g k n ε h a w p C b P hε ha hh hw hb := by
  rw [fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk,
    fullResponse_zero_couplings_eq_clockKinetic]
  ring

theorem fullEnergy_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ t : ℝ)
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t =
      fullEnergy n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t +
        Real.exp (2 * t) * potentialEnergy m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  rw [fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
      (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t (add_nonneg hm₁ hm₂) (add_nonneg hg₁ hg₂) (add_nonneg hk₁ hk₂),
    fullEnergy_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t hm₁ hg₁ hk₁,
    potentialEnergy_add_couplings]
  ring

theorem fullResponse_add_couplings (m₁ m₂ g₁ g₂ k₁ k₂ t : ℝ)
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) :
    fullResponse n ε h a w p C b P hε ha hh hw hb (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t =
      fullResponse n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t +
        Real.exp (2 * t) * potentialResponse m₂ g₂ k₂ n ε h a w p C b P hε ha hh hw hb := by
  rw [fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb
      (m₁ + m₂) (g₁ + g₂) (k₁ + k₂) t (add_nonneg hm₁ hm₂) (add_nonneg hg₁ hg₂) (add_nonneg hk₁ hk₂),
    fullResponse_eq_clockKinetic_add_potential n ε h a w p C b P hε ha hh hw hb m₁ g₁ k₁ t hm₁ hg₁ hk₁,
    potentialResponse_add_couplings]
  ring

/-! ### 5. Arbitrary-Source Clock-Integral Identities for Individual Channels -/

theorem massChannelEnergy_integral :
    massChannelEnergy n ε h a w p C b P hε ha hh hw hb =
      ∫ s, positiveSlice 1 0 0 n ε h a w p C b P s := by
  rw [← potentialEnergy_unit_mass]
  exact potentialEnergy_integral 1 0 0 n ε h a w p C b P hε ha hh hw hb

theorem massChannelResponse_weak_integral :
    massChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, weakResponse 1 0 0 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_mass]
  exact potentialResponse_weak_integral 1 0 0 n ε h a w p C b P hε ha hh hw hb

theorem massChannelResponse_reduced_integral :
    massChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, reducedResponse 1 0 0 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_mass]
  exact potentialResponse_reduced_integral 1 0 0 n ε h a w p C b P hε ha hh hw hb

theorem quarticChannelEnergy_integral :
    quarticChannelEnergy n ε h a w p C b P hε ha hh hw hb =
      ∫ s, positiveSlice 0 1 0 n ε h a w p C b P s := by
  rw [← potentialEnergy_unit_quartic]
  exact potentialEnergy_integral 0 1 0 n ε h a w p C b P hε ha hh hw hb

theorem quarticChannelResponse_weak_integral :
    quarticChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, weakResponse 0 1 0 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_quartic]
  exact potentialResponse_weak_integral 0 1 0 n ε h a w p C b P hε ha hh hw hb

theorem quarticChannelResponse_reduced_integral :
    quarticChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, reducedResponse 0 1 0 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_quartic]
  exact potentialResponse_reduced_integral 0 1 0 n ε h a w p C b P hε ha hh hw hb

theorem vacuumChannelEnergy_integral :
    vacuumChannelEnergy n ε h a w p C b P hε ha hh hw hb =
      ∫ s, positiveSlice 0 0 1 n ε h a w p C b P s := by
  rw [← potentialEnergy_unit_vacuum]
  exact potentialEnergy_integral 0 0 1 n ε h a w p C b P hε ha hh hw hb

theorem vacuumChannelResponse_weak_integral :
    vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, weakResponse 0 0 1 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_vacuum]
  exact potentialResponse_weak_integral 0 0 1 n ε h a w p C b P hε ha hh hw hb

theorem vacuumChannelResponse_reduced_integral :
    vacuumChannelResponse n ε h a w p C b P hε ha hh hw hb =
      ∫ s, reducedResponse 0 0 1 n ε h a w p C b P s := by
  rw [← potentialResponse_unit_vacuum]
  exact potentialResponse_reduced_integral 0 0 1 n ε h a w p C b P hε ha hh hw hb

/-! ### 6. Uniform Single-Channel and Zero-Quartic / Zero-Vacuum Response Bounds -/

theorem mass_channel_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * massChannelEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      massChannelResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_common_source
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro n ε h b₀ a w p C d hε ha hh hw hb
  rw [← potentialEnergy_unit_mass, ← potentialResponse_unit_mass]
  exact hM.2 1 0 0 zero_le_one le_rfl le_rfl n ε h b₀ a w p C d hε ha hh hw hb

theorem quartic_channel_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * quarticChannelEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      quarticChannelResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_common_source
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro n ε h b₀ a w p C d hε ha hh hw hb
  rw [← potentialEnergy_unit_quartic, ← potentialResponse_unit_quartic]
  exact hM.2 0 1 0 le_rfl zero_le_one le_rfl n ε h b₀ a w p C d hε ha hh hw hb

theorem vacuum_channel_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) * vacuumChannelEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      vacuumChannelResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_common_source
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro n ε h b₀ a w p C d hε ha hh hw hb
  rw [← potentialEnergy_unit_vacuum, ← potentialResponse_unit_vacuum]
  exact hM.2 0 0 1 le_rfl le_rfl zero_le_one n ε h b₀ a w p C d hε ha hh hw hb

theorem zero_quartic_potential_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) *
        (vacuum * vacuumChannelEnergy n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb +
         mass2 * massChannelEnergy n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb) ≤
      vacuum * vacuumChannelResponse n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        mass2 * massChannelResponse n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_common_source
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro mass2 vacuum hmass hvacuum n ε h b₀ a w p C d hε ha hh hw hb
  rw [← potentialEnergy_zero_quartic, ← potentialResponse_zero_quartic]
  exact hM.2 mass2 0 vacuum hmass le_rfl hvacuum n ε h b₀ a w p C d hε ha hh hw hb

theorem zero_vacuum_potential_response_lower_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic : ℝ),
      0 ≤ mass2 → 0 ≤ quartic →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3),
      -(M / ε) *
        (mass2 * massChannelEnergy n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb +
         quartic * quarticChannelEnergy n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb) ≤
      mass2 * massChannelResponse n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        quartic * quarticChannelResponse n ε h a w p C
          (fun _ => b₀) (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let hpot := potential_response_lower_common_source
  let M := Classical.choose hpot
  have hM := Classical.choose_spec hpot
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic hmass hquartic n ε h b₀ a w p C d hε ha hh hw hb
  rw [← potentialEnergy_zero_vacuum, ← potentialResponse_zero_vacuum]
  exact hM.2 mass2 quartic 0 hmass hquartic le_rfl n ε h b₀ a w p C d hε ha hh hw hb

theorem zero_quartic_full_bound_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * fullEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 0 vacuum t ≤
      fullResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 0 vacuum t := by
  let hfull := full_bound_common_source
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 vacuum hmass hvacuum n ε h b₀ a w p C d hε ha hh hw hb t
  exact hM.2 mass2 0 vacuum hmass le_rfl hvacuum n ε h b₀ a w p C d hε ha hh hw hb t

theorem zero_vacuum_full_bound_common_source :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic : ℝ),
      0 ≤ mass2 → 0 ≤ quartic →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C d : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * fullEnergy n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic 0 t ≤
      fullResponse n ε h a w p C
        (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb mass2 quartic 0 t := by
  let hfull := full_bound_common_source
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic hmass hquartic n ε h b₀ a w p C d hε ha hh hw hb t
  exact hM.2 mass2 quartic 0 hmass hquartic le_rfl n ε h b₀ a w p C d hε ha hh hw hb t

#print axioms massChannelEnergy_nonnegative
#print axioms quarticChannelEnergy_nonnegative
#print axioms vacuumChannelEnergy_nonnegative
#print axioms massChannelEnergy_scalar_polynomial_eq
#print axioms massChannelResponse_scalar_polynomial_eq
#print axioms quarticChannelEnergy_scalar_polynomial_eq
#print axioms quarticChannelResponse_scalar_polynomial_eq
#print axioms vacuumChannelEnergy_scalar_polynomial_eq
#print axioms vacuumChannelResponse_scalar_polynomial_eq
#print axioms potentialEnergy_eq_three_channels
#print axioms potentialResponse_eq_three_channels
#print axioms potentialEnergy_unit_mass
#print axioms potentialResponse_unit_mass
#print axioms potentialEnergy_unit_quartic
#print axioms potentialResponse_unit_quartic
#print axioms potentialEnergy_unit_vacuum
#print axioms potentialResponse_unit_vacuum
#print axioms potentialEnergy_pure_mass
#print axioms potentialResponse_pure_mass
#print axioms potentialEnergy_pure_quartic
#print axioms potentialResponse_pure_quartic
#print axioms potentialEnergy_pure_vacuum
#print axioms potentialResponse_pure_vacuum
#print axioms potentialEnergy_zero_quartic
#print axioms potentialResponse_zero_quartic
#print axioms potentialEnergy_zero_vacuum
#print axioms potentialResponse_zero_vacuum
#print axioms potentialEnergy_zero_mass
#print axioms potentialResponse_zero_mass
#print axioms growingEnergy_zero_quartic
#print axioms growingResponse_zero_quartic
#print axioms residualEnergy_zero_quartic
#print axioms residualResponse_zero_quartic
#print axioms fullEnergy_zero_quartic
#print axioms fullResponse_zero_quartic
#print axioms fullEnergy_zero_vacuum
#print axioms fullResponse_zero_vacuum
#print axioms potentialEnergy_add_couplings
#print axioms potentialResponse_add_couplings
#print axioms potentialEnergy_smul_couplings
#print axioms potentialResponse_smul_couplings
#print axioms growingEnergy_sub_zero_couplings
#print axioms growingResponse_sub_zero_couplings
#print axioms growingEnergy_add_couplings
#print axioms growingResponse_add_couplings
#print axioms residualEnergy_sub_zero_couplings
#print axioms residualResponse_sub_zero_couplings
#print axioms residualEnergy_add_couplings
#print axioms residualResponse_add_couplings
#print axioms fullEnergy_sub_zero_couplings
#print axioms fullResponse_sub_zero_couplings
#print axioms fullEnergy_add_couplings
#print axioms fullResponse_add_couplings
#print axioms massChannelEnergy_integral
#print axioms massChannelResponse_weak_integral
#print axioms massChannelResponse_reduced_integral
#print axioms quarticChannelEnergy_integral
#print axioms quarticChannelResponse_weak_integral
#print axioms quarticChannelResponse_reduced_integral
#print axioms vacuumChannelEnergy_integral
#print axioms vacuumChannelResponse_weak_integral
#print axioms vacuumChannelResponse_reduced_integral
#print axioms mass_channel_response_lower_common_source
#print axioms quartic_channel_response_lower_common_source
#print axioms vacuum_channel_response_lower_common_source
#print axioms zero_quartic_potential_response_lower_common_source
#print axioms zero_vacuum_potential_response_lower_common_source
#print axioms zero_quartic_full_bound_common_source
#print axioms zero_vacuum_full_bound_common_source
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceMassVacuumZeroResponse
