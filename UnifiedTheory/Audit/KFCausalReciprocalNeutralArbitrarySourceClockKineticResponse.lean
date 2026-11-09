/- Arbitrary-source and constant-neutral-polynomial clock, static, and radial-kinetic
response bounds for finite reciprocal neutral superpositions, together with the
zero-potential-coupling full Hamiltonian response, energy time derivative, and
common-complex-source bridge. -/
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianHamiltonianResponse
import UnifiedTheory.Audit.KFCausalCommonRealGaussianInitialResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
  (factorEnergy factorRate clockKineticEnergy clockKineticResponse
   kinetic_bounds physical_energy physical_response clockKinetic_nonnegative)
open KFCausalReciprocalNeutralConstantClockComposition (finite_clock_graph)
open KFCausalReciprocalNeutralConstantResponse (clock_response clock_energy_bounds clockKinetic_lower)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalCommonRealGaussianInitialResponse (expectation initialRate initial_derivative_tendsto)

/-! ### Packet and Superposition Constant-Polynomial Amplitude Absorption -/

def scaleAmplitude {n : ℕ} (C d : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C i * d i

def constantPolynomial {n : ℕ} (d : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  fun i => Polynomial.C (d i)

theorem packet_state_constant (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b (Polynomial.C c) =
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw (C * c) p b 1 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b (Polynomial.C c),
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw (C * c) p b 1] with x hx1 hx2
  rw [hx1, hx2]
  unfold KFCausalReciprocalNeutralPackets.profile
  simp only [Polynomial.eval_C, Polynomial.eval_one]
  ring

theorem packet_momentum_constant (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b (Polynomial.C c) =
      KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw (C * c) p b 1 :=
  (pureMomentum ε hε h).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b (Polynomial.C c))
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw (C * c) p b 1)
    (packet_state_constant ε a h w hε ha hh hw C p b c)

theorem packet_output_constant (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b (Polynomial.C c) hb j =
      KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw (C * c) p b 1 hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b (Polynomial.C c) hb j)
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw (C * c) p b 1 hb j)
    (packet_state_constant ε a h w hε ha hh hw C p b c)

theorem packet_momentumOutput_constant (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b (Polynomial.C c) hb j =
      KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw (C * c) p b 1 hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b (Polynomial.C c) hb j)
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw (C * c) p b 1 hb j)
    (packet_momentum_constant ε a h w hε ha hh hw C p b c)

theorem packet_second_constant (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (C : ℂ) (p : ℝ) (b c : ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b (Polynomial.C c) j =
      KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb (C * c) p b 1 j :=
  (reverseFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b (Polynomial.C c) j)
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb (C * c) p b 1 j)
    (packet_output_constant ε a h w hε ha hh hw C p b c (original_strip ε h hε hb) j)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem state_constant_eq :
    state n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw := by
  unfold state scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_state_constant ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i))

theorem momentum_constant_eq :
    momentum n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw := by
  unfold momentum scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentum_constant ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i))

theorem output_constant_eq (j : Fin 8) :
    output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j := by
  unfold output scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_output_constant ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) hb j)

theorem momentumOutput_constant_eq (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j := by
  unfold momentumOutput scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentumOutput_constant ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) hb j)

theorem factorEnergy_constant_eq (j : Fin 8) :
    factorEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      factorEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j := by
  unfold factorEnergy
  rw [output_constant_eq]

theorem factorRate_constant_eq (j : Fin 8) :
    factorRate n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb j =
      factorRate n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb j := by
  unfold factorRate
  rw [output_constant_eq, momentumOutput_constant_eq]

/-! ### Channel Energy and Response Functionals -/

local notation "E" => factorEnergy n ε h a w p C b P hε ha hh hw hb
local notation "R" => factorRate n ε h a w p C b P hε ha hh hw hb

def staticEnergy : ℝ := (E 0 + E 1 + E 2) / 2
def staticResponse : ℝ := (R 0 + R 1 + R 2) / 2
def radialKineticEnergy : ℝ := (E 3 + E 4) / 2
def radialKineticResponse : ℝ := (R 3 + R 4) / 2

def growingEnergy (mass2 quartic vacuum : ℝ) : ℝ :=
  radialKineticEnergy n ε h a w p C b P hε ha hh hw hb +
    potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb

def growingResponse (mass2 quartic vacuum : ℝ) : ℝ :=
  radialKineticResponse n ε h a w p C b P hε ha hh hw hb +
    potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb

def residualEnergy (mass2 quartic vacuum t : ℝ) : ℝ :=
  staticEnergy n ε h a w p C b P hε ha hh hw hb +
    Real.exp (2 * t) * potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb

def residualResponse (mass2 quartic vacuum t : ℝ) : ℝ :=
  staticResponse n ε h a w p C b P hε ha hh hw hb +
    Real.exp (2 * t) * potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb

theorem clockKineticEnergy_eq_static_add_radialKinetic (t : ℝ) :
    clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold clockKineticEnergy staticEnergy radialKineticEnergy
  ring

theorem clockKineticResponse_eq_static_add_radialKinetic (t : ℝ) :
    clockKineticResponse n ε h a w p C b P hε ha hh hw hb t =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticResponse n ε h a w p C b P hε ha hh hw hb := by
  unfold clockKineticResponse staticResponse radialKineticResponse
  ring

theorem clockKineticEnergy_zero_eq :
    clockKineticEnergy n ε h a w p C b P hε ha hh hw hb 0 =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [clockKineticEnergy_eq_static_add_radialKinetic, mul_zero, Real.exp_zero, one_mul]

theorem clockKineticResponse_zero_eq :
    clockKineticResponse n ε h a w p C b P hε ha hh hw hb 0 =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        radialKineticResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [clockKineticResponse_eq_static_add_radialKinetic, mul_zero, Real.exp_zero, one_mul]

theorem staticEnergy_nonnegative :
    0 ≤ staticEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold staticEnergy factorEnergy
  positivity

theorem radialKineticEnergy_nonnegative :
    0 ≤ radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold radialKineticEnergy factorEnergy
  positivity

theorem radialKineticResponse_bounds :
    0 ≤ radialKineticResponse n ε h a w p C b P hε ha hh hw hb ∧
      radialKineticResponse n ε h a w p C b P hε ha hh hw hb ≤
        (1 / (4 * ε)) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  have h3 := kinetic_bounds n ε h a w p C b P hε ha hh hw hb 2
  have h4 := kinetic_bounds n ε h a w p C b P hε ha hh hw hb 3
  change 0 ≤ R 3 ∧ R 3 ≤ (1 / (4 * ε)) * E 3 at h3
  change 0 ≤ R 4 ∧ R 4 ≤ (1 / (4 * ε)) * E 4 at h4
  unfold radialKineticResponse radialKineticEnergy
  exact ⟨by linarith, by linarith⟩

/-! ### Arbitrary-Source & Constant-Polynomial Clock and Kinetic Response Bounds -/

theorem finite_clock_graph_constant :
    (output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0,
      momentumOutput n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 -
        correction ε hε h (output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0)) ∈
      (pureMomentum ε hε h).graph := by
  rw [output_constant_eq, momentumOutput_constant_eq]
  exact finite_clock_graph n ε h a w p (scaleAmplitude C d) b hε ha hh hw hb

theorem finite_clock_domain_constant :
    output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 ∈
      (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (finite_clock_graph_constant n ε h a w p C b d hε ha hh hw hb)

theorem clock_response_constant :
    factorRate n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 =
      -KFCausalClockFloorPureClockKineticResponse.response ε hε
        (output n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0) := by
  rw [factorRate_constant_eq, output_constant_eq]
  exact clock_response n ε h a w p (scaleAmplitude C d) b hε ha hh hw hb

theorem clock_energy_bounds_constant :
    -(1 / (4 * ε)) * factorEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 ≤
        factorRate n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 ∧
      factorRate n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 ≤ 0 := by
  rw [factorEnergy_constant_eq, factorRate_constant_eq]
  exact clock_energy_bounds n ε h a w p (scaleAmplitude C d) b hε ha hh hw hb

theorem staticEnergy_constant_eq :
    staticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      staticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold staticEnergy
  simp only [factorEnergy_constant_eq]

theorem staticResponse_constant_eq :
    staticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      staticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold staticResponse
  simp only [factorRate_constant_eq]

theorem radialKineticEnergy_constant_eq :
    radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      radialKineticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold radialKineticEnergy
  simp only [factorEnergy_constant_eq]

theorem radialKineticResponse_constant_eq :
    radialKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb =
      radialKineticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb := by
  unfold radialKineticResponse
  simp only [factorRate_constant_eq]

theorem clockKineticEnergy_constant_eq (t : ℝ) :
    clockKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t =
      clockKineticEnergy n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb t := by
  unfold clockKineticEnergy
  simp only [factorEnergy_constant_eq]

theorem clockKineticResponse_constant_eq (t : ℝ) :
    clockKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t =
      clockKineticResponse n ε h a w p (scaleAmplitude C d) b (fun _ => 1) hε ha hh hw hb t := by
  unfold clockKineticResponse
  simp only [factorRate_constant_eq]

theorem staticResponse_lower_constant :
    -(1 / (4 * ε)) * staticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb ≤
      staticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  let P0 : Fin n → Polynomial ℂ := fun i => Polynomial.C (d i)
  have h0 := (clock_energy_bounds_constant n ε h a w p C b d hε ha hh hw hb).1
  have h1 := (kinetic_bounds n ε h a w p C b P0 hε ha hh hw hb 0).1
  have h2 := (kinetic_bounds n ε h a w p C b P0 hε ha hh hw hb 1).1
  change 0 ≤ factorRate n ε h a w p C b P0 hε ha hh hw hb 1 at h1
  change 0 ≤ factorRate n ε h a w p C b P0 hε ha hh hw hb 2 at h2
  have hc : 0 ≤ 1 / (4 * ε) := by positivity
  have he : factorEnergy n ε h a w p C b P0 hε ha hh hw hb 0 / 2 ≤
      staticEnergy n ε h a w p C b P0 hε ha hh hw hb := by
    have hs : 0 ≤ (factorEnergy n ε h a w p C b P0 hε ha hh hw hb 1 +
        factorEnergy n ε h a w p C b P0 hε ha hh hw hb 2) / 2 := by
      unfold factorEnergy; positivity
    unfold staticEnergy
    linarith
  have hr : -(1 / (4 * ε)) * (factorEnergy n ε h a w p C b P0 hε ha hh hw hb 0 / 2) ≤
      staticResponse n ε h a w p C b P0 hε ha hh hw hb := by
    unfold staticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

theorem clockKinetic_lower_constant (t : ℝ) :
    -(1 / (4 * ε)) * clockKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t ≤
      clockKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb t := by
  rw [clockKineticEnergy_constant_eq, clockKineticResponse_constant_eq]
  exact clockKinetic_lower n ε h a w p (scaleAmplitude C d) b hε ha hh hw hb t

theorem static_add_radialKinetic_response_lower (t : ℝ) :
    -(1 / (4 * ε)) *
        (staticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
          Real.exp (2 * t) *
            radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb) ≤
      staticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        Real.exp (2 * t) *
          radialKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  rw [← clockKineticEnergy_eq_static_add_radialKinetic,
    ← clockKineticResponse_eq_static_add_radialKinetic]
  exact clockKinetic_lower_constant n ε h a w p C b d hε ha hh hw hb t

theorem static_add_radialKinetic_response_lower_zero :
    -(1 / (4 * ε)) *
        (staticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
          radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb) ≤
      staticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        radialKineticResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb := by
  rw [← clockKineticEnergy_zero_eq, ← clockKineticResponse_zero_eq]
  exact clockKinetic_lower_constant n ε h a w p C b d hε ha hh hw hb 0

/-! ### Zero-Potential-Coupling Regime (`mass2 = 0, quartic = 0, vacuum = 0`) -/

theorem potentialEnergy_zero_couplings :
    potentialEnergy 0 0 0 n ε h a w p C b P hε ha hh hw hb = 0 := by
  unfold potentialEnergy
  ring

theorem potentialResponse_zero_couplings :
    potentialResponse 0 0 0 n ε h a w p C b P hε ha hh hw hb = 0 := by
  unfold potentialResponse
  simp

theorem growingEnergy_zero_couplings :
    growingEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 =
      radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold growingEnergy
  rw [potentialEnergy_zero_couplings, add_zero]

theorem growingResponse_zero_couplings :
    growingResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 =
      radialKineticResponse n ε h a w p C b P hε ha hh hw hb := by
  unfold growingResponse
  rw [potentialResponse_zero_couplings, add_zero]

theorem residualEnergy_zero_couplings (t : ℝ) :
    residualEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb := by
  unfold residualEnergy
  rw [potentialEnergy_zero_couplings, mul_zero, add_zero]

theorem residualResponse_zero_couplings (t : ℝ) :
    residualResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      staticResponse n ε h a w p C b P hε ha hh hw hb := by
  unfold residualResponse
  rw [potentialResponse_zero_couplings, mul_zero, add_zero]

theorem fullEnergy_zero_couplings_eq_clockKinetic (t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t := by
  rw [physical_energy n ε h a w p C b P hε ha hh hw hb 0 0 0 t le_rfl le_rfl le_rfl]
  unfold clockKineticEnergy
  ring

theorem fullEnergy_zero_couplings_eq_static_add_radialKinetic (t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [fullEnergy_zero_couplings_eq_clockKinetic, clockKineticEnergy_eq_static_add_radialKinetic]

theorem fullResponse_zero_couplings_eq_clockKinetic (t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t := by
  rw [physical_response n ε h a w p C b P hε ha hh hw hb 0 0 0 t le_rfl le_rfl le_rfl]
  unfold clockKineticResponse
  ring

theorem fullResponse_zero_couplings_eq_static_add_radialKinetic (t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t =
      staticResponse n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * t) * radialKineticResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [fullResponse_zero_couplings_eq_clockKinetic, clockKineticResponse_eq_static_add_radialKinetic]

theorem fullResponse_zero_couplings_lower (t : ℝ) :
    -(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 t ≤
      fullResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 t := by
  rw [fullEnergy_zero_couplings_eq_clockKinetic, fullResponse_zero_couplings_eq_clockKinetic]
  exact clockKinetic_lower_constant n ε h a w p C b d hε ha hh hw hb t

theorem fullResponse_zero_couplings_lower_zero :
    -(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 0 ≤
      fullResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 0 :=
  fullResponse_zero_couplings_lower n ε h a w p C b d hε ha hh hw hb 0

theorem fullEnergy_zero_couplings_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 s)
      (2 * Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb) t := by
  have he := (Real.hasDerivAt_exp (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he' : HasDerivAt (fun s : ℝ => Real.exp (2 * s)) (2 * Real.exp (2 * t)) t := by
    convert he using 1
    ring
  have hd := (he'.mul_const (radialKineticEnergy n ε h a w p C b P hε ha hh hw hb)).const_add
    (staticEnergy n ε h a w p C b P hε ha hh hw hb)
  have hfun : (fun s => fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 s) =
      fun s => staticEnergy n ε h a w p C b P hε ha hh hw hb +
        Real.exp (2 * s) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb :=
    funext (fullEnergy_zero_couplings_eq_static_add_radialKinetic n ε h a w p C b P hε ha hh hw hb)
  rwa [hfun]

theorem fullEnergy_plus_expectation_zero_couplings_hasDerivAt
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (s τ : ℝ) :
    HasDerivAt
      (fun t => fullEnergy n ε h a w p C b P hε ha hh hw (original_strip ε h hε hb_narrow) 0 0 0 t +
        expectation n ε h a w p C b P hε ha hh hw hb_narrow 0 0 0 s τ t)
      (2 * Real.exp (2 * s) *
          radialKineticEnergy n ε h a w p C b P hε ha hh hw (original_strip ε h hε hb_narrow) +
        initialRate n ε h a w p C b P hε ha hh hw hb_narrow 0 0 0 s τ) s :=
  (fullEnergy_zero_couplings_hasDerivAt n ε h a w p C b P hε ha hh hw
    (original_strip ε h hε hb_narrow) s).add
    (KFCausalCommonRealGaussianInitialResponse.expectation_initial_derivative
      n ε h a w p C b P hε ha hh hw hb_narrow 0 0 0 s τ)

theorem fullEnergy_plus_response_zero_couplings_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun s => fullEnergy n ε h a w p C b P hε ha hh hw hb 0 0 0 s +
        s * fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t)
      (2 * Real.exp (2 * t) * radialKineticEnergy n ε h a w p C b P hε ha hh hw hb +
        fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t) t := by
  have hr : HasDerivAt
      (fun s : ℝ => s * fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t)
      (fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t) t := by
    simpa only [one_mul] using
      (hasDerivAt_id t).mul_const (fullResponse n ε h a w p C b P hε ha hh hw hb 0 0 0 t)
  exact (fullEnergy_zero_couplings_hasDerivAt n ε h a w p C b P hε ha hh hw hb t).add hr

theorem fullEnergy_deriv_add_response_zero_couplings_lower (t : ℝ) :
    -(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 t ≤
      2 * Real.exp (2 * t) *
          radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        fullResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 t := by
  have hr := fullResponse_zero_couplings_lower n ε h a w p C b d hε ha hh hw hb t
  have hk : 0 ≤ 2 * Real.exp (2 * t) *
      radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos (2 * t)).le)
      (radialKineticEnergy_nonnegative n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb)
  linarith

theorem fullEnergy_deriv_add_response_zero_couplings_lower_zero :
    -(1 / (4 * ε)) *
        fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 0 ≤
      2 * radialKineticEnergy n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb +
        fullResponse n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb 0 0 0 0 := by
  have h0 := fullEnergy_deriv_add_response_zero_couplings_lower n ε h a w p C b d hε ha hh hw hb 0
  simpa only [mul_zero, Real.exp_zero, mul_one] using h0

theorem arbitrary_source_zero_couplings_hamiltonian_bound
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (t : ℝ) :
    let ψ := state n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw;
    let Bψ := momentum n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw;
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) 0 0 0 t;
    let ψH : H.domain := ⟨ψ, hamiltonian_domain n ε h a w p C b (fun i => Polynomial.C (d i))
      hε ha hh hw hb_narrow 0 0 0 t⟩;
    -(1 / (4 * ε)) * (inner ℂ (H ψH) ψ).re ≤ (-2 / h) * (inner ℂ (H ψH) Bψ).im := by
  dsimp only
  rw [hamiltonian_action n ε h a w p C b (fun i => Polynomial.C (d i))
      hε ha hh hw hb_narrow 0 0 0 t,
    ← KFCausalReciprocalNeutralStrongResponse.energy_identity
      n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb_narrow 0 0 0 t,
    ← KFCausalReciprocalNeutralStrongResponse.response_identity
      n ε h a w p C b (fun i => Polynomial.C (d i)) hε ha hh hw hb_narrow 0 0 0 t]
  exact fullResponse_zero_couplings_lower n ε h a w p C b d hε ha hh hw
    (original_strip ε h hε hb_narrow) t

theorem arbitrary_source_zero_couplings_limit_lower
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (s : ℝ) :
    ∃ R0 : ℝ,
      -(1 / (4 * ε)) *
          fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i))
            hε ha hh hw (original_strip ε h hε hb_narrow) 0 0 0 s ≤ R0 ∧
        Tendsto
          (fun τ => deriv (expectation n ε h a w p C b (fun i => Polynomial.C (d i))
            hε ha hh hw hb_narrow 0 0 0 s τ) s)
          (𝓝[≠] 0) (𝓝 R0) :=
  ⟨_, fullResponse_zero_couplings_lower n ε h a w p C b d hε ha hh hw
      (original_strip ε h hε hb_narrow) s,
    initial_derivative_tendsto n ε h a w p C b (fun i => Polynomial.C (d i))
      hε ha hh hw hb_narrow 0 0 0 s⟩

theorem arbitrary_source_zero_couplings_eventually_lower
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (s δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ τ in 𝓝[≠] (0 : ℝ),
      -(1 / (4 * ε)) *
          fullEnergy n ε h a w p C b (fun i => Polynomial.C (d i))
            hε ha hh hw (original_strip ε h hε hb_narrow) 0 0 0 s - δ <
        deriv (expectation n ε h a w p C b (fun i => Polynomial.C (d i))
          hε ha hh hw hb_narrow 0 0 0 s τ) s := by
  let hlim0 := arbitrary_source_zero_couplings_limit_lower n ε h a w p C b d hε ha hh hw hb_narrow s
  let R0 := Classical.choose hlim0
  have hR0 := Classical.choose_spec hlim0
  exact hR0.2.eventually (eventually_gt_nhds (by linarith [hR0.1]))

/-! ### Shifted Common-Complex-Source Specialization (`b = fun _ => b₀`) -/

theorem source_re_im (b₀ : ℂ) : source b₀.re b₀.im = b₀ :=
  Complex.re_add_im b₀

theorem common_complex_source_clockKinetic_lower (b₀ : ℂ) (t : ℝ) :
    -(1 / (4 * ε)) *
        clockKineticEnergy n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i))
          hε ha hh hw hb t ≤
      clockKineticResponse n ε h a w p C (fun _ => b₀) (fun i => Polynomial.C (d i))
        hε ha hh hw hb t :=
  clockKinetic_lower_constant n ε h a w p C (fun _ => b₀) d hε ha hh hw hb t

theorem common_complex_source_full_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2 * Real.pi * ε / 3) (t : ℝ),
      -(M / ε) * fullEnergy n ε h a w p C (fun _ => b₀) (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t ≤
      fullResponse n ε h a w p C (fun _ => b₀) (fun _ => 1)
        hε ha hh hw hb mass2 quartic vacuum t := by
  let hfull := KFCausalCommonComplexGaussianHamiltonianResponse.full_bound
  let M := Classical.choose hfull
  have hM := Classical.choose_spec hfull
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C hε ha hh hw hb t
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C hε ha hh hw hb t
  simpa only [source_re_im] using hb0

theorem common_complex_source_hamiltonian_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n : ℕ) (ε h : ℝ) (b₀ : ℂ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi * ε / 3) (t : ℝ),
      let ψ := state n ε h a w p C (fun _ => b₀) (fun _ => 1) hε ha hh hw;
      let Bψ := momentum n ε h a w p C (fun _ => b₀) (fun _ => 1) hε ha hh hw;
      let H := hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t;
      let ψH : H.domain := ⟨ψ, hamiltonian_domain n ε h a w p C
        (fun _ => b₀) (fun _ => 1) hε ha hh hw hb mass2 quartic vacuum t⟩;
      -(M / ε) * (inner ℂ (H ψH) ψ).re ≤ (-2 / h) * (inner ℂ (H ψH) Bψ).im := by
  let hham := KFCausalCommonComplexGaussianHamiltonianResponse.hamiltonian_bound
  let M := Classical.choose hham
  have hM := Classical.choose_spec hham
  refine ⟨M, hM.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀ a w p C hε ha hh hw hb t
  have hb0 := hM.2 mass2 quartic vacuum hmass hquartic hvacuum
    n ε h b₀.re b₀.im a w p C hε ha hh hw hb t
  simpa only [source_re_im] using hb0

#print axioms packet_state_constant
#print axioms packet_momentum_constant
#print axioms packet_output_constant
#print axioms packet_momentumOutput_constant
#print axioms packet_second_constant
#print axioms state_constant_eq
#print axioms momentum_constant_eq
#print axioms output_constant_eq
#print axioms momentumOutput_constant_eq
#print axioms factorEnergy_constant_eq
#print axioms factorRate_constant_eq
#print axioms clockKineticEnergy_eq_static_add_radialKinetic
#print axioms clockKineticResponse_eq_static_add_radialKinetic
#print axioms clockKineticEnergy_zero_eq
#print axioms clockKineticResponse_zero_eq
#print axioms staticEnergy_nonnegative
#print axioms radialKineticEnergy_nonnegative
#print axioms radialKineticResponse_bounds
#print axioms finite_clock_graph_constant
#print axioms finite_clock_domain_constant
#print axioms clock_response_constant
#print axioms clock_energy_bounds_constant
#print axioms staticEnergy_constant_eq
#print axioms staticResponse_constant_eq
#print axioms radialKineticEnergy_constant_eq
#print axioms radialKineticResponse_constant_eq
#print axioms clockKineticEnergy_constant_eq
#print axioms clockKineticResponse_constant_eq
#print axioms staticResponse_lower_constant
#print axioms clockKinetic_lower_constant
#print axioms static_add_radialKinetic_response_lower
#print axioms static_add_radialKinetic_response_lower_zero
#print axioms potentialEnergy_zero_couplings
#print axioms potentialResponse_zero_couplings
#print axioms growingEnergy_zero_couplings
#print axioms growingResponse_zero_couplings
#print axioms residualEnergy_zero_couplings
#print axioms residualResponse_zero_couplings
#print axioms fullEnergy_zero_couplings_eq_clockKinetic
#print axioms fullEnergy_zero_couplings_eq_static_add_radialKinetic
#print axioms fullResponse_zero_couplings_eq_clockKinetic
#print axioms fullResponse_zero_couplings_eq_static_add_radialKinetic
#print axioms fullResponse_zero_couplings_lower
#print axioms fullResponse_zero_couplings_lower_zero
#print axioms fullEnergy_zero_couplings_hasDerivAt
#print axioms fullEnergy_plus_expectation_zero_couplings_hasDerivAt
#print axioms fullEnergy_plus_response_zero_couplings_hasDerivAt
#print axioms fullEnergy_deriv_add_response_zero_couplings_lower
#print axioms fullEnergy_deriv_add_response_zero_couplings_lower_zero
#print axioms arbitrary_source_zero_couplings_hamiltonian_bound
#print axioms arbitrary_source_zero_couplings_limit_lower
#print axioms arbitrary_source_zero_couplings_eventually_lower
#print axioms source_re_im
#print axioms common_complex_source_clockKinetic_lower
#print axioms common_complex_source_full_bound
#print axioms common_complex_source_hamiltonian_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
