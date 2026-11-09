/- Factored-polynomial coherent amplitude summation, exact neutral higher-degree
mode cancellation across all 9 state, momentum, factor, lift, and strong
Hamiltonian maps, arbitrary-degree `M` neutral polynomial reduction to the
constant channel, universal Cauchy-Schwarz weight-factor lower bounds, and
uniform Hamiltonian response lower bounds. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
import UnifiedTheory.Audit.KFCausalCommonComplexAffineNeutralPolynomialDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift inputLift_embedding momentumLift_embedding
   fullEnergy fullResponse energy_decomposition response_decomposition)
open KFCausalReciprocalNeutralKineticResponse
  (clockKineticEnergy clockKineticResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport
  (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_graph hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (clockKinetic_lower_constant)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (full_bound_common_source)
open KFCausalCommonComplexAffineNeutralPolynomialDecomposition
  (packet_state_scale packet_state_smul
   packet_momentum_scale packet_momentum_smul
   packet_output_scale packet_output_smul
   packet_momentumOutput_scale packet_momentumOutput_smul
   packet_second_scale packet_second_smul
   state_poly_add momentum_poly_add output_poly_add momentumOutput_poly_add
   seconds_poly_add hamiltonianOutput_poly_add inputLift_poly_add momentumLift_poly_add)
open KFCausalReciprocalNeutralArbitrarySourceAffinePolynomialDecomposition
  (state_poly_zero momentum_poly_zero
   hamiltonianOutput_poly_zero inputLift_poly_zero momentumLift_poly_zero)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition
  (state_poly_finset_sum momentum_poly_finset_sum
   output_poly_finset_sum momentumOutput_poly_finset_sum
   seconds_poly_finset_sum hamiltonianOutput_poly_finset_sum
   inputLift_poly_finset_sum momentumLift_poly_finset_sum)

private lemma packet_state_amp_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (c : ℂ) (p : ℝ) (b : ℂ) (Q : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw c p b Q =
      c • KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw 1 p b Q := by
  rw [← packet_state_smul ε a h w hε ha hh hw 1 p b c Q, packet_state_scale, one_mul]

private lemma packet_momentum_amp_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (c : ℂ) (p : ℝ) (b : ℂ) (Q : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw c p b Q =
      c • KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw 1 p b Q := by
  rw [← packet_momentum_smul ε a h w hε ha hh hw 1 p b c Q, packet_momentum_scale, one_mul]

private lemma packet_output_amp_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (c : ℂ) (p : ℝ) (b : ℂ) (Q : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw c p b Q hb j =
      c • KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw 1 p b Q hb j := by
  rw [← packet_output_smul ε a h w hε ha hh hw 1 p b c Q hb j, packet_output_scale, one_mul]

private lemma packet_momentumOutput_amp_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (c : ℂ) (p : ℝ) (b : ℂ) (Q : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw c p b Q hb j =
      c • KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw 1 p b Q hb j := by
  rw [← packet_momentumOutput_smul ε a h w hε ha hh hw 1 p b c Q hb j,
    packet_momentumOutput_scale, one_mul]

private lemma packet_second_amp_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (c : ℂ) (p : ℝ) (b : ℂ)
    (Q : Polynomial ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb c p b Q j =
      c • KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb 1 p b Q j := by
  rw [← packet_second_smul ε a h w hε ha hh hw hb 1 p b c Q j, packet_second_scale, one_mul]

private lemma norm_smul_sq (s : ℂ) (x : Hilbert) :
    ‖s • x‖ ^ 2 = ‖s‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul]
  ring

private lemma rate_smul_sq (h : ℝ) (s : ℂ) (x y : Hilbert) :
    (-2 / h) * (inner ℂ (s • x) (s • y)).im =
      ‖s‖ ^ 2 * ((-2 / h) * (inner ℂ x y).im) := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.im_ofReal_mul]
  ring

private lemma re_sum_sq_le_norm_sum_sq {n : ℕ} (C : Fin n → ℂ) :
    (∑ i : Fin n, (C i).re) ^ 2 ≤ ‖∑ i : Fin n, C i‖ ^ 2 := by
  rw [← Complex.re_sum]
  have h1 : |(∑ i : Fin n, C i).re| ≤ ‖∑ i : Fin n, C i‖ :=
    Complex.abs_re_le_norm (∑ i : Fin n, C i)
  have h2 : |(∑ i : Fin n, C i).re| ^ 2 ≤ ‖∑ i : Fin n, C i‖ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [sq_abs] at h2

/-! ### 1. Factored Polynomial Profiles and Coherent Amplitude Summation -/

def factoredPolyProfile {n : ℕ} (c : Fin n → ℂ) (Q : Polynomial ℂ) (i : Fin n) :
    Polynomial ℂ :=
  Polynomial.C (c i) * Q

def degreeMPolyProfile {n : ℕ} (M : ℕ) (c₀ : Fin n → ℂ) (d : Fin M → Fin n → ℂ)
    (i : Fin n) : Polynomial ℂ :=
  Polynomial.C (c₀ i) + ∑ r : Fin M, Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1)

def cauchySchwarzWeightRatio {n : ℕ} (C : Fin n → ℂ) : ℝ :=
  (∑ i : Fin n, ‖C i‖ ^ 2)⁻¹ * (∑ i : Fin n, (C i).re) ^ 2

variable (n : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ : ℂ) (C c c₀ : Fin n → ℂ)
  (Q : Polynomial ℂ) (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0)
  (hw₀ : 1 ≤ w₀) (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem state_factored_eq_sum_smul :
    state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      (∑ i : Fin n, C i * c i) •
        state 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  unfold state factoredPolyProfile
  rw [Fin.sum_univ_one, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    (packet_state_scale ε a₀ h w₀ hε ha₀ hh hw₀ (C i) p₀ b₀ (c i) Q).trans
      (packet_state_amp_smul ε a₀ h w₀ hε ha₀ hh hw₀ (C i * c i) p₀ b₀ Q))

theorem momentum_factored_eq_sum_smul :
    momentum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      (∑ i : Fin n, C i * c i) •
        momentum 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  unfold momentum factoredPolyProfile
  rw [Fin.sum_univ_one, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    (packet_momentum_scale ε a₀ h w₀ hε ha₀ hh hw₀ (C i) p₀ b₀ (c i) Q).trans
      (packet_momentum_amp_smul ε a₀ h w₀ hε ha₀ hh hw₀ (C i * c i) p₀ b₀ Q))

theorem output_factored_eq_sum_smul (j : Fin 8) :
    output n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      (∑ i : Fin n, C i * c i) •
        output 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  unfold output factoredPolyProfile
  rw [Fin.sum_univ_one, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    (packet_output_scale ε a₀ h w₀ hε ha₀ hh hw₀ (C i) p₀ b₀ (c i) Q hb j).trans
      (packet_output_amp_smul ε a₀ h w₀ hε ha₀ hh hw₀ (C i * c i) p₀ b₀ Q hb j))

theorem momentumOutput_factored_eq_sum_smul (j : Fin 8) :
    momentumOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      (∑ i : Fin n, C i * c i) •
        momentumOutput 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  unfold momentumOutput factoredPolyProfile
  rw [Fin.sum_univ_one, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    (packet_momentumOutput_scale ε a₀ h w₀ hε ha₀ hh hw₀ (C i) p₀ b₀ (c i) Q hb j).trans
      (packet_momentumOutput_amp_smul ε a₀ h w₀ hε ha₀ hh hw₀ (C i * c i) p₀ b₀ Q hb j))

theorem seconds_factored_eq_sum_smul (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j =
      (∑ i : Fin n, C i * c i) •
        seconds 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j := by
  unfold seconds factoredPolyProfile
  rw [Fin.sum_univ_one, Finset.sum_smul]
  exact Finset.sum_congr rfl (fun i _ =>
    (packet_second_scale ε a₀ h w₀ hε ha₀ hh hw₀ hb_narrow (C i) p₀ b₀ (c i) Q j).trans
      (packet_second_amp_smul ε a₀ h w₀ hε ha₀ hh hw₀ hb_narrow (C i * c i) p₀ b₀ Q j))

/-! ### 2. Exact Neutral Cancellation (`∑ i, C i * c i = 0`) for Arbitrary Polynomial `Q` -/

theorem state_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0) :
    state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 := by
  rw [state_factored_eq_sum_smul, hneutral, zero_smul]

theorem momentum_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0) :
    momentum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 := by
  rw [momentum_factored_eq_sum_smul, hneutral, zero_smul]

theorem output_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0) (j : Fin 8) :
    output n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 := by
  rw [output_factored_eq_sum_smul, hneutral, zero_smul]

theorem momentumOutput_factored_neutral_zero
    (hneutral : ∑ i : Fin n, C i * c i = 0) (j : Fin 8) :
    momentumOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 := by
  rw [momentumOutput_factored_eq_sum_smul, hneutral, zero_smul]

theorem seconds_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j = 0 := by
  rw [seconds_factored_eq_sum_smul, hneutral, zero_smul]

theorem hamiltonianOutput_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t = 0 := by
  have h1 := (hamiltonian ε hε h hh (original_strip ε h hε hb_narrow)
    mass2 quartic vacuum t).mem_graph_snd_inj'
    (hamiltonian_graph n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb_narrow mass2 quartic vacuum t)
    (hamiltonian_graph n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun _ => 0) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb_narrow mass2 quartic vacuum t)
    ((state_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C c Q hε ha₀ hh hw₀ hneutral).trans
      (state_poly_zero n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        hε (fun _ => ha₀) hh (fun _ => hw₀)).symm)
  exact h1.trans (hamiltonianOutput_poly_zero n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
    C (fun _ => b₀) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow mass2 quartic vacuum t)

theorem inputLift_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 := by
  have h1 : inputLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb mass2 quartic vacuum t =
    inputLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun _ => 0) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
    apply KFCausalClockFloorAveragedFormTransport.embedding_injective
      ε hε h hh hb mass2 quartic vacuum t
    rw [inputLift_embedding, inputLift_embedding,
      state_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C c Q hε ha₀ hh hw₀ hneutral,
      state_poly_zero]
  exact h1.trans (inputLift_poly_zero n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
    C (fun _ => b₀) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t)

theorem momentumLift_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 := by
  have h1 : momentumLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb mass2 quartic vacuum t =
    momentumLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun _ => 0) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
    apply KFCausalClockFloorAveragedFormTransport.embedding_injective
      ε hε h hh hb mass2 quartic vacuum t
    rw [momentumLift_embedding, momentumLift_embedding,
      momentum_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C c Q hε ha₀ hh hw₀ hneutral,
      momentum_poly_zero]
  exact h1.trans (momentumLift_poly_zero n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
    C (fun _ => b₀) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t)

theorem hamiltonian_factored_neutral_zero_action (hneutral : ∑ i : Fin n, C i * c i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀);
    H ⟨ψ, hamiltonian_domain n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t⟩ = 0 := by
  dsimp only
  exact (hamiltonian_action n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
    (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
    hb_narrow mass2 quartic vacuum t).trans
    (hamiltonianOutput_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C c Q
      hε ha₀ hh hw₀ hneutral hb_narrow mass2 quartic vacuum t)

theorem fullEnergy_factored_eq_norm_sum_sq (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      ‖∑ i : Fin n, C i * c i‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  rw [energy_decomposition, energy_decomposition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [output_factored_eq_sum_smul, norm_smul_sq]
  ring

theorem fullResponse_factored_eq_norm_sum_sq (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      ‖∑ i : Fin n, C i * c i‖ ^ 2 *
        fullResponse 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  rw [response_decomposition, response_decomposition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [output_factored_eq_sum_smul, momentumOutput_factored_eq_sum_smul, rate_smul_sq]
  ring

theorem fullEnergy_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 := by
  rw [fullEnergy_factored_eq_norm_sum_sq, hneutral]
  simp

theorem fullResponse_factored_neutral_zero (hneutral : ∑ i : Fin n, C i * c i = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 := by
  rw [fullResponse_factored_eq_norm_sum_sq, hneutral]
  simp

/-! ### 3. Arbitrary-Degree `M` Neutral Polynomial Reduction to the Constant Channel -/

theorem state_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) :
    state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  unfold degreeMPolyProfile
  rw [state_poly_add, state_poly_finset_sum]
  have hsum : ∑ r : Fin M, state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
      hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      state_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ (hneutral r))
  rw [hsum, add_zero]

theorem momentum_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) :
    momentum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      momentum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  unfold degreeMPolyProfile
  rw [momentum_poly_add, momentum_poly_finset_sum]
  have hsum : ∑ r : Fin M, momentum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
      hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      momentum_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ (hneutral r))
  rw [hsum, add_zero]

theorem output_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (j : Fin 8) :
    output n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      output n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  unfold degreeMPolyProfile
  rw [output_poly_add, output_poly_finset_sum]
  have hsum : ∑ r : Fin M, output n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      output_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ hb (hneutral r) j)
  rw [hsum, add_zero]

theorem momentumOutput_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (j : Fin 8) :
    momentumOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      momentumOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  unfold degreeMPolyProfile
  rw [momentumOutput_poly_add, momentumOutput_poly_finset_sum]
  have hsum : ∑ r : Fin M,
      momentumOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      momentumOutput_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ hb (hneutral r) j)
  rw [hsum, add_zero]

theorem seconds_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j =
      seconds n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j := by
  unfold degreeMPolyProfile
  rw [seconds_poly_add, seconds_poly_finset_sum]
  have hsum : ∑ r : Fin M, seconds n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
      hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      seconds_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ (hneutral r) hb_narrow j)
  rw [hsum, add_zero]

theorem hamiltonianOutput_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t := by
  unfold degreeMPolyProfile
  rw [hamiltonianOutput_poly_add, hamiltonianOutput_poly_finset_sum]
  have hsum : ∑ r : Fin M,
      hamiltonianOutput n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (d r i) * Polynomial.X ^ ((r : ℕ) + 1))
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow mass2 quartic vacuum t = 0 :=
    Finset.sum_eq_zero (fun r _ =>
      hamiltonianOutput_factored_neutral_zero n ε h a₀ w₀ p₀ b₀ C (d r)
        (Polynomial.X ^ ((r : ℕ) + 1)) hε ha₀ hh hw₀ (hneutral r) hb_narrow mass2 quartic vacuum t)
  rw [hsum, add_zero]

theorem inputLift_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      inputLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective
    ε hε h hh hb mass2 quartic vacuum t
  exact state_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ M d hneutral

theorem momentumLift_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      momentumLift n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective
    ε hε h hh hb mass2 quartic vacuum t
  exact momentum_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ M d hneutral

theorem hamiltonian_degreeM_neutral_action_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψM := state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀);
    let ψ0 := state n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
      (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀);
    H ⟨ψM, hamiltonian_domain n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ0, hamiltonian_domain n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  exact (hamiltonian_action n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
    (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
    hb_narrow mass2 quartic vacuum t).trans
    ((hamiltonianOutput_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀
      hε ha₀ hh hw₀ M d hneutral hb_narrow mass2 quartic vacuum t).trans
      (hamiltonian_action n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t).symm)

/-! ### 4. Energy, Response, Cauchy-Schwarz Weight Factor, and Uniform Lower Bounds -/

theorem clockKineticEnergy_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (t : ℝ) :
    clockKineticEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t =
      clockKineticEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t := by
  unfold clockKineticEnergy KFCausalReciprocalNeutralKineticResponse.factorEnergy
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem clockKineticResponse_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (t : ℝ) :
    clockKineticResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t =
      clockKineticResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t := by
  unfold clockKineticResponse KFCausalReciprocalNeutralKineticResponse.factorRate
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral,
    momentumOutput_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem potentialEnergy_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (mass2 quartic vacuum : ℝ) :
    potentialEnergy mass2 quartic vacuum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        C (fun _ => b₀) (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb =
      potentialEnergy mass2 quartic vacuum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        C (fun _ => b₀) (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb := by
  unfold potentialEnergy
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem potentialResponse_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (mass2 quartic vacuum : ℝ) :
    potentialResponse mass2 quartic vacuum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        C (fun _ => b₀) (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb =
      potentialResponse mass2 quartic vacuum n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        C (fun _ => b₀) (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb := by
  unfold potentialResponse
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral,
    momentumOutput_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem fullEnergy_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  rw [energy_decomposition, energy_decomposition]
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem fullResponse_degreeM_neutral_eq_constant (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      fullResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (fun i => Polynomial.C (c₀ i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  rw [response_decomposition, response_decomposition]
  simp only [output_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral,
    momentumOutput_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀ hε ha₀ hh hw₀ hb M d hneutral]

theorem fullEnergy_degreeM_common_amp_eq (M : ℕ) (z : ℂ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      ‖∑ i : Fin n, C i‖ ^ 2 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  rw [fullEnergy_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C (fun _ => z)
    hε ha₀ hh hw₀ hb M d hneutral]
  have h1 : (fun _ : Fin n => Polynomial.C z) = factoredPolyProfile (fun _ : Fin n => z) 1 := by
    funext _
    simp [factoredPolyProfile]
  rw [h1, fullEnergy_factored_eq_norm_sum_sq, ← Finset.sum_mul, norm_mul, mul_pow, mul_assoc]

theorem cauchySchwarzWeightRatio_mul_incoherent_le_degreeM_fullEnergy
    (M : ℕ) (z : ℂ) (d : Fin M → Fin n → ℂ)
    (hC : ∑ i : Fin n, ‖C i‖ ^ 2 ≠ 0)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    cauchySchwarzWeightRatio C * ‖z‖ ^ 2 *
        ((∑ i : Fin n, ‖C i‖ ^ 2) *
          fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
            (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) ≤
      fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  rw [fullEnergy_degreeM_common_amp_eq n ε h a₀ w₀ p₀ b₀ C hε ha₀ hh hw₀ hb M z d hneutral]
  unfold cauchySchwarzWeightRatio
  have hcancel :
      (∑ i : Fin n, ‖C i‖ ^ 2)⁻¹ * (∑ i : Fin n, (C i).re) ^ 2 * ‖z‖ ^ 2 *
        ((∑ i : Fin n, ‖C i‖ ^ 2) *
          fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
            (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) =
      (∑ i : Fin n, (C i).re) ^ 2 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
    calc
      (∑ i : Fin n, ‖C i‖ ^ 2)⁻¹ * (∑ i : Fin n, (C i).re) ^ 2 * ‖z‖ ^ 2 *
          ((∑ i : Fin n, ‖C i‖ ^ 2) *
            fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
              (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t)
        = ((∑ i : Fin n, ‖C i‖ ^ 2)⁻¹ * (∑ i : Fin n, ‖C i‖ ^ 2)) *
            ((∑ i : Fin n, (C i).re) ^ 2 * ‖z‖ ^ 2 *
              fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
                (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) := by ring
      _ = (∑ i : Fin n, (C i).re) ^ 2 * ‖z‖ ^ 2 *
            fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
              (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
          rw [inv_mul_cancel₀ hC, one_mul]
  rw [hcancel]
  have hE : 0 ≤ fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1)
      (fun _ => b₀) (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb mass2 quartic vacuum t :=
    sq_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (re_sum_sq_le_norm_sum_sq C) (sq_nonneg ‖z‖)) hE

theorem cauchySchwarzWeightRatio_mul_unit_le_degreeM_fullEnergy
    (M : ℕ) (z : ℂ) (d : Fin M → Fin n → ℂ)
    (hC1 : 1 ≤ ∑ i : Fin n, ‖C i‖ ^ 2)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0)
    (mass2 quartic vacuum t : ℝ) :
    cauchySchwarzWeightRatio C * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  have hC0 : ∑ i : Fin n, ‖C i‖ ^ 2 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hinc := cauchySchwarzWeightRatio_mul_incoherent_le_degreeM_fullEnergy
    n ε h a₀ w₀ p₀ b₀ C hε ha₀ hh hw₀ hb M z d hC0 hneutral mass2 quartic vacuum t
  have hE : 0 ≤ fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1)
      (fun _ => b₀) (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀)
      hb mass2 quartic vacuum t :=
    sq_nonneg _
  have hcs : 0 ≤ cauchySchwarzWeightRatio C * ‖z‖ ^ 2 :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one hC1)) (sq_nonneg _))
      (sq_nonneg ‖z‖)
  have hle := le_mul_of_one_le_left hE hC1
  exact (mul_le_mul_of_nonneg_left hle hcs).trans hinc

theorem clockKinetic_lower_degreeM_neutral (M : ℕ) (d : Fin M → Fin n → ℂ)
    (hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (t : ℝ) :
    -(1 / (4 * ε)) *
        clockKineticEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
          (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t ≤
      clockKineticResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t := by
  rw [clockKineticEnergy_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀
      hε ha₀ hh hw₀ hb M d hneutral t,
    clockKineticResponse_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀
      hε ha₀ hh hw₀ hb M d hneutral t]
  exact clockKinetic_lower_constant n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
    C (fun _ => b₀) c₀ hε (fun _ => ha₀) hh (fun _ => hw₀) hb t

theorem full_bound_degreeM_neutral :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ : ℂ) (C c₀ : Fin n → ℂ)
      (d : Fin M → Fin n → ℂ)
      (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
      (hb : |h| ≤ 2 * Real.pi * ε / 3)
      (_hneutral : ∀ r : Fin M, ∑ i : Fin n, C i * d r i = 0) (t : ℝ),
      -(K / ε) * fullEnergy n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t ≤
      fullResponse n ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C (fun _ => b₀)
        (degreeMPolyProfile M c₀ d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  let hfull := full_bound_common_source
  let K := Classical.choose hfull
  have hK := Classical.choose_spec hfull
  refine ⟨K, hK.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n M ε h a₀ w₀ p₀ b₀ C c₀ d
    hε ha₀ hh hw₀ hb hneutral t
  rw [fullEnergy_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀
      hε ha₀ hh hw₀ hb M d hneutral mass2 quartic vacuum t,
    fullResponse_degreeM_neutral_eq_constant n ε h a₀ w₀ p₀ b₀ C c₀
      hε ha₀ hh hw₀ hb M d hneutral mass2 quartic vacuum t]
  exact hK.2 mass2 quartic vacuum hmass hquartic hvacuum n ε h b₀
    (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) C c₀ hε (fun _ => ha₀) hh (fun _ => hw₀) hb t

#print axioms state_factored_eq_sum_smul
#print axioms momentum_factored_eq_sum_smul
#print axioms output_factored_eq_sum_smul
#print axioms momentumOutput_factored_eq_sum_smul
#print axioms seconds_factored_eq_sum_smul
#print axioms state_factored_neutral_zero
#print axioms momentum_factored_neutral_zero
#print axioms output_factored_neutral_zero
#print axioms momentumOutput_factored_neutral_zero
#print axioms seconds_factored_neutral_zero
#print axioms hamiltonianOutput_factored_neutral_zero
#print axioms inputLift_factored_neutral_zero
#print axioms momentumLift_factored_neutral_zero
#print axioms hamiltonian_factored_neutral_zero_action
#print axioms fullEnergy_factored_eq_norm_sum_sq
#print axioms fullResponse_factored_eq_norm_sum_sq
#print axioms fullEnergy_factored_neutral_zero
#print axioms fullResponse_factored_neutral_zero
#print axioms state_degreeM_neutral_eq_constant
#print axioms momentum_degreeM_neutral_eq_constant
#print axioms output_degreeM_neutral_eq_constant
#print axioms momentumOutput_degreeM_neutral_eq_constant
#print axioms seconds_degreeM_neutral_eq_constant
#print axioms hamiltonianOutput_degreeM_neutral_eq_constant
#print axioms inputLift_degreeM_neutral_eq_constant
#print axioms momentumLift_degreeM_neutral_eq_constant
#print axioms hamiltonian_degreeM_neutral_action_eq_constant
#print axioms clockKineticEnergy_degreeM_neutral_eq_constant
#print axioms clockKineticResponse_degreeM_neutral_eq_constant
#print axioms potentialEnergy_degreeM_neutral_eq_constant
#print axioms potentialResponse_degreeM_neutral_eq_constant
#print axioms fullEnergy_degreeM_neutral_eq_constant
#print axioms fullResponse_degreeM_neutral_eq_constant
#print axioms fullEnergy_degreeM_common_amp_eq
#print axioms cauchySchwarzWeightRatio_mul_incoherent_le_degreeM_fullEnergy
#print axioms cauchySchwarzWeightRatio_mul_unit_le_degreeM_fullEnergy
#print axioms clockKinetic_lower_degreeM_neutral
#print axioms full_bound_degreeM_neutral
end
end UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
