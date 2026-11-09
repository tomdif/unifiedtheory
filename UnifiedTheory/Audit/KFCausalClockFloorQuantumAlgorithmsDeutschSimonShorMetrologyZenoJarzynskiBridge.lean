/-
  UnifiedTheory/Audit/KFCausalClockFloorQuantumAlgorithmsDeutschSimonShorMetrologyZenoJarzynskiBridge.lean

  Self-contained Tier-1 synthesis bridge connecting:
  1. The arbitrary-order `(r, s)` multi-power Yosida difference and composition-defect
     hierarchy across the five discrete clock-floor operators `T`, `P`, `G`, `S(t)`,
     and `H(t)` (`fiveOperator_arbitraryOrder_multiPower_yosida_composition_master_synthesis`),
  2. Deutsch's query algorithm (`deutsch_quantum_decides`, `classical_one_query_insufficient`),
     the Bernstein-Vazirani hidden-string algorithm (`bv_amplitude_correctness`,
     `bv_quantum_decides`), Simon's hidden-period algorithm (`simon_amplitude_iff`,
     `simon_recovery_2`), the unitary Quantum Fourier Transform (`qftMatrix_unitary`,
     `qft_master`), single-ancilla Kitaev Quantum Phase Estimation (`qpe_total_prob`,
     `qpe_distinguishes_pm_one_strong`), Shor's factoring reduction for `N = 15`
     (`shor_factoring_15_full`), Quantum Signal Processing (`signalOp_unitary`,
     `signalOp_sq_topLeft`, `qsp_master`), and Grover's unitary oracle, diffusion, and
     iteration operators (`groverOracle_unitary`, `groverDiffusion_unitary`,
     `groverIteration_unitary`),
  3. Quantum metrology SQL vs Heisenberg scaling (`crBound_sql`, `crBound_heisenberg`,
     `heisenberg_beats_sql`, `metrology_master`), the geometric Mandelstam-Tamm /
     Cramér-Rao speed-metrology duality (`buresAngleSpeed_eq_half_sqrt_fisher`,
     `speed_metrology_duality`, `geometric_speed_limit_master`), the Quantum Zeno effect
     (`zenoStep_norm_sq_le`, `zenoSurvival_antitone`, `zeno_survival_eq_one_of_commute`,
     `zeno_survival_lower_bound_of_step_bound`), and the Maassen-Uffink entropic
     uncertainty bound (`muBound_nonneg`, `muBound_mub`, `muBound_qubit`,
     `maassen_uffink_master`),
  4. The Quantum Jarzynski equality (`quantum_jarzynski_partition`, `quantum_jarzynski`),
     the Quantum Crooks fluctuation theorem and its summation to Jarzynski
     (`crooks_per_transition`, `forward_marginal_sum`, `reverse_marginal_sum`,
     `crooks_implies_jarzynski`), the Helstrom / single-copy Quantum Chernoff bound
     (`helstrom_lower_bound`, `helstrom_upper_bound`,
     `chernoff_single_copy_average_lower_bound`), and the Quantum Hoeffding rate
     antitonicity and cumulant boundary anchors (`hoeffdingRate_antitone_in_r`,
     `hoeffding_antitone_in_r`, `hoeffding_master`).

  Every theorem in this module is proved from first principles using only the standard
  Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`,
  zero `admit`, zero custom `axiom`, and zero `unsafe`.
-/
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect
import UnifiedTheory.LayerB.DeutschAlgorithm
import UnifiedTheory.LayerB.BernsteinVazirani
import UnifiedTheory.LayerB.SimonAlgorithm
import UnifiedTheory.LayerB.QuantumFourierTransform
import UnifiedTheory.LayerB.QuantumPhaseEstimation
import UnifiedTheory.LayerC.ShorFactoring15
import UnifiedTheory.LayerB.QuantumSignalProcessing
import UnifiedTheory.LayerB.QuantumWalk
import UnifiedTheory.LayerB.QuantumMetrology
import UnifiedTheory.LayerB.GeometricSpeedLimit
import UnifiedTheory.LayerB.QuantumZeno
import UnifiedTheory.LayerB.MaassenUffink
import UnifiedTheory.LayerB.QuantumJarzynski
import UnifiedTheory.LayerB.QuantumCrooks
import UnifiedTheory.LayerB.QuantumChernoff
import UnifiedTheory.LayerB.QuantumHoeffding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumAlgorithmsDeutschSimonShorMetrologyZenoJarzynskiBridge

open Matrix Complex
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderMultiPowerYosidaCompositionDefect
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorStaticResolventRadialCommutator (staticResolvent)
open KFCausalClockFloorHigherPowerOperatorCores
  (staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence (iteratedIdentityPower)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence (kthPowerGraphNormSq)
open UnifiedTheory.LayerB.DeutschAlgorithm
open UnifiedTheory.LayerB.BernsteinVazirani
open UnifiedTheory.LayerB.SimonAlgorithm
open UnifiedTheory.LayerB.QuantumFourierTransform
open UnifiedTheory.LayerB.QuantumPhaseEstimation
open UnifiedTheory.LayerC.ShorFactoring15
open UnifiedTheory.LayerB.QuantumSignalProcessing
open UnifiedTheory.LayerB.QuantumWalk
open UnifiedTheory.LayerB.QuantumMetrology
open UnifiedTheory.LayerB.GeometricSpeedLimit
open UnifiedTheory.LayerB.QuantumZeno
open UnifiedTheory.LayerB.MaassenUffink
open UnifiedTheory.LayerB.QuantumJarzynski
open UnifiedTheory.LayerB.QuantumCrooks
open UnifiedTheory.LayerB.QuantumChernoff
open UnifiedTheory.LayerB.QuantumHoeffding
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.QuantumStein

noncomputable section

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T_op" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "P_op" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G_op" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S_op" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H_op" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-- **Theorem 1 (Deutsch, Bernstein-Vazirani, Simon, QFT, QPE, Shor N=15, QSP, and Grover Unitary Package).**
    Bundles the quantum query separations (Deutsch, Bernstein-Vazirani, Simon),
    unitarity of the general `N × N` QFT matrix `Fᴴ * F = 1`, single-ancilla QPE
    eigenvalue discrimination (`P(0) + P(1) = 1`, `P_0(0) = 1`, `P_1(1/2) = 1`),
    Shor's factoring of `15 = 3 · 5` via period `r = 4`, unitarity and Chebyshev
    composition of the QSP signal operator `W(x)`, and unitarity of Grover's oracle,
    diffusion, and iteration operators. -/
theorem deutsch_bv_simon_qft_qpe_shor_qsp_and_grover_package
    (f_d : Fin 2 → Fin 2) (s_bv : Fin 2 → Fin 2)
    (s_sim : Fin 2 → Fin 2) (hs_sim : s_sim ≠ fun _ => 0)
    (N : ℕ) (hN : 0 < N) (t_g : Fin N) (φ x_qsp : ℝ) (hx_qsp : x_qsp ^ 2 ≤ 1) :
    ((IsConstant f_d → (deutschAmplitudeOnZero f_d) ^ 2 = 1) ∧
     (IsBalanced f_d → (deutschAmplitudeOnZero f_d) ^ 2 = 0)) ∧
    (bvAmplitudeOnY s_bv s_bv = 1 ∧ ∀ y, y ≠ s_bv → bvAmplitudeOnY s_bv y = 0) ∧
    (∃ y₁ y₂ : Fin 2 → Fin 2,
      simonAmplitudeOnY s_sim y₁ ≠ 0 ∧ simonAmplitudeOnY s_sim y₂ ≠ 0 ∧
      y₁ ≠ y₂ ∧ y₂ ≠ fun _ => 0) ∧
    (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    (qpeProbZero φ + qpeProbOne φ = 1 ∧ qpeProbZero 0 = 1 ∧ qpeProbOne (1 / 2) = 1) ∧
    (Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧ Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5 ∧
      (3 : ℕ) * 5 = 15 ∧ f15 4 = 1) ∧
    ((signalOp x_qsp)ᴴ * signalOp x_qsp = 1 ∧
      (signalOp x_qsp * signalOp x_qsp) 0 0 = (chebyshevT 2 x_qsp : ℂ)) ∧
    (groverOracle N t_g ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
     groverDiffusion N ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
     groverIteration N t_g ∈ Matrix.unitaryGroup (Fin N) ℂ) := by
  exact ⟨deutsch_quantum_decides f_d,
    bv_quantum_decides s_bv,
    simon_recovery_2 s_sim hs_sim,
    qftMatrix_unitary N hN,
    ⟨qpe_total_prob φ, qpe_zero_phase, qpe_half_phase⟩,
    ⟨shor_factor_minus, shor_factor_plus, shor_recovers_15, period_of_two_mod_15⟩,
    ⟨signalOp_unitary x_qsp hx_qsp, signalOp_sq_topLeft x_qsp hx_qsp⟩,
    ⟨groverOracle_unitary N t_g, groverDiffusion_unitary hN, groverIteration_unitary N t_g hN⟩⟩

/-- **Theorem 2 (Quantum Metrology, Geometric Speed-Metrology Duality, Quantum Zeno, and Maassen-Uffink Package).**
    The Heisenberg limit `1/N` strictly beats the SQL `1/√N` for `N > 1`; the Bures-angle
    speed `ΔH = (1/2)√F_Q` and single-shot Cramér-Rao bound `1/√F_Q` satisfy the universal
    duality `speed * crBound 1 F_Q = 1/2`; Zeno survival is antitone in `N` and equals `1`
    under commuting evolution; and the Maassen-Uffink bound equals `log₂ d` for MUBs (`1`
    bit for complementary qubit bases). -/
theorem metrology_geometric_speed_zeno_and_maassen_uffink_package
    (N_probe varH : ℝ) (hN_probe : 1 < N_probe) (hvarH : 0 < varH)
    {n_z : ℕ} (P_z U_z : Matrix (Fin n_z) (Fin n_z) ℂ)
    (hP_herm : star P_z = P_z) (hP_idem : P_z * P_z = P_z)
    (hU_z : (star U_z) * U_z = 1) (ψ_z : Fin n_z → ℂ) (N_z : ℕ)
    (d_mub : ℕ) (hd_mub : 0 < d_mub) :
    (crBound 1 N_probe = sqlBound N_probe ∧
     crBound 1 (N_probe ^ 2) = heisenbergBound N_probe ∧
     heisenbergBound N_probe < sqlBound N_probe) ∧
    (buresAngleSpeed varH = (1 / 2) * Real.sqrt (fisherInfo_time varH) ∧
     buresAngleSpeed varH * crBound 1 (fisherInfo_time varH) = 1 / 2) ∧
    (zenoSurvival P_z U_z (N_z + 1) ψ_z ≤ zenoSurvival P_z U_z N_z ψ_z ∧
     (P_z * U_z = U_z * P_z → P_z.mulVec ψ_z = ψ_z → vecNormSq ψ_z = 1 →
       zenoSurvival P_z U_z N_z ψ_z = 1)) ∧
    (muBound (1 / Real.sqrt d_mub) = Real.logb 2 d_mub ∧
     muBound (1 / Real.sqrt 2) = 1) := by
  refine ⟨⟨crBound_sql N_probe, crBound_heisenberg N_probe (by linarith),
      heisenberg_beats_sql N_probe hN_probe⟩,
    ⟨buresAngleSpeed_eq_half_sqrt_fisher varH (le_of_lt hvarH),
      (speed_metrology_duality varH hvarH).2.2⟩,
    ⟨zenoSurvival_antitone P_z U_z hP_herm hP_idem hU_z ψ_z N_z,
      fun hcomm hproj hunit =>
        zeno_survival_eq_one_of_commute P_z U_z hP_idem hcomm hU_z ψ_z hproj hunit N_z⟩,
    ⟨muBound_mub d_mub hd_mub, muBound_qubit⟩⟩

/-- **Theorem 3 (Quantum Jarzynski, Quantum Crooks, Helstrom/Chernoff, and Quantum Hoeffding Package).**
    The Jarzynski work average satisfies `⟨exp(-β W)⟩ = Z₁ / Z₀ = exp(-β ΔF)`; the
    Crooks per-transition fluctuation identity `P_F · exp(β ΔF) = P_R · exp(β W)` and
    marginal normalizations `∑ P_F = ∑ P_R = 1` imply Jarzynski upon summation; the
    Helstrom bound `1 - traceDistance ρ σ / 2 ≤ typeI + typeII ≤ 1 + traceDistance ρ σ / 2`
    governs single-copy hypothesis testing; and the Hoeffding rate is antitone in the
    type-II constraint `r` with vanishing cumulant boundary values. -/
theorem jarzynski_crooks_chernoff_and_hoeffding_package
    {n_j : ℕ} [Nonempty (Fin n_j)] (Prot : JarzynskiProtocol n_j) (i_j j_j : Fin n_j)
    (T_test : BinaryHypothesisTest n_j) (ρ σ : ComplexDensityMatrix n_j) (psi_s : ℝ) :
    (jarzynskiAverage Prot =
       UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction Prot.β Prot.H_1 /
         UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction Prot.β Prot.H_0 ∧
     jarzynskiAverage Prot =
       Real.exp (-Prot.β *
         (UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_1 -
          UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_0))) ∧
    (forwardTransitionProb Prot i_j j_j * Real.exp (Prot.β * deltaF Prot) =
       reverseTransitionProb Prot i_j j_j * Real.exp (Prot.β * work Prot i_j j_j) ∧
     ∑ m_idx, ∑ k_idx, forwardTransitionProb Prot m_idx k_idx = 1 ∧
     ∑ m_idx, ∑ k_idx, reverseTransitionProb Prot m_idx k_idx = 1) ∧
    (1 - traceDistance ρ σ / 2 ≤ typeI T_test ρ + typeII T_test σ ∧
     typeI T_test ρ + typeII T_test σ ≤ 1 + traceDistance ρ σ / 2) ∧
    (hoeffdingRate 0 0 0 = 0 ∧
     Real.log (Matrix.trace ρ.M).re = 0 ∧
     Real.log (Matrix.trace σ.M).re = 0 ∧
     (∀ r₁ r₂ : ℝ, r₁ ≤ r₂ →
       hoeffdingRate psi_s (1 / 2) r₂ ≤ hoeffdingRate psi_s (1 / 2) r₁)) := by
  exact ⟨⟨quantum_jarzynski_partition Prot, quantum_jarzynski Prot⟩,
    ⟨crooks_per_transition Prot i_j j_j,
     forward_marginal_sum Prot,
     reverse_marginal_sum Prot⟩,
    ⟨helstrom_lower_bound T_test ρ σ, helstrom_upper_bound T_test ρ σ⟩,
    hoeffding_master ρ σ psi_s⟩

/-- **Theorem 4 (Static and Potential Multi-Power Yosida Coupled to QFT, QPE, Shor, QSP, and Grover).**
    The arbitrary-order `(r, s)` multi-power Yosida difference and composition-defect
    bounds for `T` and `P` hold simultaneously with QFT unitarity, QPE ±1 eigenvalue
    discrimination, Shor's factoring of `15`, QSP unitarity, and Grover iteration unitarity. -/
theorem static_and_potential_multiPower_yosida_coupled_to_qft_qpe_shor_qsp_grover
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ)
    {xT xP : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (N : ℕ) (hN : 0 < N) (t_g : Fin N) (x_qsp : ℝ) (hx_qsp : x_qsp ^ 2 ≤ 1) :
    (kthPowerGraphNormSq T_op n
       (iteratedIdentityPower (RT a) a r xT - iteratedIdentityPower (RT b) b s xT) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T_op (n + 1) xT ∧
     kthPowerGraphNormSq T_op n
       (iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s xT) - xT) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T_op (n + 1) xT) ∧
    (kthPowerGraphNormSq P_op n
       (iteratedIdentityPower (RP a) a r xP - iteratedIdentityPower (RP b) b s xP) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P_op (n + 1) xP ∧
     kthPowerGraphNormSq P_op n
       (iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s xP) - xP) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P_op (n + 1) xP) ∧
    (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    (qpeProbZero 0 = 1 ∧ qpeProbOne (1 / 2) = 1) ∧
    (Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧ Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5) ∧
    (signalOp x_qsp)ᴴ * signalOp x_qsp = 1 ∧
    groverIteration N t_g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  exact ⟨static_arbitraryOrder_multiPower_yosida_package ε hε h hh hb a b ha hb_pos n r s hxT,
    potential_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k a b ha hb_pos n r s hxP,
    qftMatrix_unitary N hN,
    qpe_distinguishes_pm_one,
    ⟨shor_factor_minus, shor_factor_plus⟩,
    signalOp_unitary x_qsp hx_qsp,
    groverIteration_unitary N t_g hN⟩

/-- **Theorem 5 (Growing, Residual, and Hamiltonian Multi-Power Yosida Coupled to Metrology, Zeno, Jarzynski, Crooks, and Helstrom).**
    The arbitrary-order `(r, s)` multi-power Yosida difference and composition-defect
    bounds for `G`, `S(t)`, and `H(t)` hold simultaneously with Heisenberg metrological
    advantage, speed-metrology duality, the Quantum Jarzynski and Crooks fluctuation
    theorems, and the Helstrom lower bound. -/
theorem growing_residual_hamiltonian_multiPower_yosida_coupled_to_metrology_jarzynski_crooks_helstrom
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ)
    {xG xS xH : Hilbert}
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1))
    (N_probe varH : ℝ) (hN_probe : 1 < N_probe) (hvarH : 0 < varH)
    {n_j : ℕ} [Nonempty (Fin n_j)] (Prot : JarzynskiProtocol n_j) (i_j j_j : Fin n_j)
    (T_test : BinaryHypothesisTest n_j) (ρ σ : ComplexDensityMatrix n_j) :
    (kthPowerGraphNormSq G_op n
       (iteratedIdentityPower (RG a) a r xG - iteratedIdentityPower (RG b) b s xG) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G_op (n + 1) xG ∧
     kthPowerGraphNormSq G_op n
       (iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s xG) - xG) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G_op (n + 1) xG) ∧
    (kthPowerGraphNormSq (S_op t) n
       (iteratedIdentityPower (RS t a) a r xS - iteratedIdentityPower (RS t b) b s xS) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S_op t) (n + 1) xS ∧
     kthPowerGraphNormSq (S_op t) n
       (iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s xS) - xS) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S_op t) (n + 1) xS) ∧
    (kthPowerGraphNormSq (H_op t) n
       (iteratedIdentityPower (RH t a) a r xH - iteratedIdentityPower (RH t b) b s xH) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H_op t) (n + 1) xH ∧
     kthPowerGraphNormSq (H_op t) n
       (iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s xH) - xH) ≤
       ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H_op t) (n + 1) xH) ∧
    heisenbergBound N_probe < sqlBound N_probe ∧
    buresAngleSpeed varH * crBound 1 (fisherInfo_time varH) = 1 / 2 ∧
    jarzynskiAverage Prot =
      Real.exp (-Prot.β *
        (UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_1 -
         UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_0)) ∧
    forwardTransitionProb Prot i_j j_j * Real.exp (Prot.β * deltaF Prot) =
      reverseTransitionProb Prot i_j j_j * Real.exp (Prot.β * work Prot i_j j_j) ∧
    1 - traceDistance ρ σ / 2 ≤ typeI T_test ρ + typeII T_test σ := by
  exact ⟨growing_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k a b ha hb_pos n r s hxG,
    residual_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k t a b ha hb_pos n r s hxS,
    hamiltonian_arbitraryOrder_multiPower_yosida_package ε hε h hh hb m g k t a b ha hb_pos n r s hxH,
    heisenberg_beats_sql N_probe hN_probe,
    (speed_metrology_duality varH hvarH).2.2,
    quantum_jarzynski Prot,
    crooks_per_transition Prot i_j j_j,
    helstrom_lower_bound T_test ρ σ⟩

/-- **Theorem 6 (Grand Five-Operator Multi-Power Yosida, Quantum Algorithms, Metrology, Speed Limit, Zeno, Maassen-Uffink, Jarzynski, Crooks, Chernoff, and Hoeffding Bridge).**
    Complete synthesis uniting the five-operator arbitrary-order `(r, s)` multi-power
    Yosida difference and composition-defect hierarchy with Deutsch, Bernstein-Vazirani,
    Simon, QFT, QPE, Shor (`N = 15`), QSP, Grover, quantum metrology, speed-metrology
    duality, the Quantum Zeno effect, Maassen-Uffink entropic uncertainty, Quantum
    Jarzynski and Crooks fluctuation theorems, and the Quantum Chernoff and Hoeffding
    bounds. -/
theorem fiveOperator_multiPower_yosida_quantum_algorithms_metrology_zeno_jarzynski_bridge
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r s : ℕ)
    {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1))
    (N : ℕ) (hN : 0 < N) (t_g : Fin N) (N_probe varH : ℝ)
    (hN_probe : 1 < N_probe) (hvarH : 0 < varH)
    {n_j : ℕ} [Nonempty (Fin n_j)] (Prot : JarzynskiProtocol n_j) (i_j j_j : Fin n_j)
    (T_test : BinaryHypothesisTest n_j) (ρ σ : ComplexDensityMatrix n_j) :
    ((kthPowerGraphNormSq T_op n
        (iteratedIdentityPower (RT a) a r xT - iteratedIdentityPower (RT b) b s xT) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T_op (n + 1) xT ∧
      kthPowerGraphNormSq P_op n
        (iteratedIdentityPower (RP a) a r xP - iteratedIdentityPower (RP b) b s xP) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P_op (n + 1) xP ∧
      kthPowerGraphNormSq G_op n
        (iteratedIdentityPower (RG a) a r xG - iteratedIdentityPower (RG b) b s xG) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G_op (n + 1) xG ∧
      kthPowerGraphNormSq (S_op t) n
        (iteratedIdentityPower (RS t a) a r xS - iteratedIdentityPower (RS t b) b s xS) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S_op t) (n + 1) xS ∧
      kthPowerGraphNormSq (H_op t) n
        (iteratedIdentityPower (RH t a) a r xH - iteratedIdentityPower (RH t b) b s xH) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H_op t) (n + 1) xH) ∧
     (kthPowerGraphNormSq T_op n
        (iteratedIdentityPower (RT a) a r (iteratedIdentityPower (RT b) b s xT) - xT) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq T_op (n + 1) xT ∧
      kthPowerGraphNormSq P_op n
        (iteratedIdentityPower (RP a) a r (iteratedIdentityPower (RP b) b s xP) - xP) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq P_op (n + 1) xP ∧
      kthPowerGraphNormSq G_op n
        (iteratedIdentityPower (RG a) a r (iteratedIdentityPower (RG b) b s xG) - xG) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq G_op (n + 1) xG ∧
      kthPowerGraphNormSq (S_op t) n
        (iteratedIdentityPower (RS t a) a r (iteratedIdentityPower (RS t b) b s xS) - xS) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (S_op t) (n + 1) xS ∧
      kthPowerGraphNormSq (H_op t) n
        (iteratedIdentityPower (RH t a) a r (iteratedIdentityPower (RH t b) b s xH) - xH) ≤
        ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹) ^ 2 * kthPowerGraphNormSq (H_op t) (n + 1) xH)) ∧
    (qftMatrix N)ᴴ * qftMatrix N = (1 : Matrix (Fin N) (Fin N) ℂ) ∧
    (qpeProbZero 0 = 1 ∧ qpeProbOne (1 / 2) = 1) ∧
    (Nat.gcd (2 ^ (4 / 2) - 1) 15 = 3 ∧ Nat.gcd (2 ^ (4 / 2) + 1) 15 = 5) ∧
    groverIteration N t_g ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
    heisenbergBound N_probe < sqlBound N_probe ∧
    buresAngleSpeed varH * crBound 1 (fisherInfo_time varH) = 1 / 2 ∧
    muBound (1 / Real.sqrt 2) = 1 ∧
    jarzynskiAverage Prot =
      Real.exp (-Prot.β *
        (UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_1 -
         UnifiedTheory.LayerB.QuantumJarzynski.freeEnergy Prot.β Prot.H_0)) ∧
    forwardTransitionProb Prot i_j j_j * Real.exp (Prot.β * deltaF Prot) =
      reverseTransitionProb Prot i_j j_j * Real.exp (Prot.β * work Prot i_j j_j) ∧
    1 - traceDistance ρ σ / 2 ≤ typeI T_test ρ + typeII T_test σ := by
  refine ⟨fiveOperator_arbitraryOrder_multiPower_yosida_composition_master_synthesis
      ε hε h hh hb m g k t a b ha hb_pos n r s hxT hxP hxG hxS hxH,
    qftMatrix_unitary N hN,
    qpe_distinguishes_pm_one,
    ⟨shor_factor_minus, shor_factor_plus⟩,
    groverIteration_unitary N t_g hN,
    heisenberg_beats_sql N_probe hN_probe,
    (speed_metrology_duality varH hvarH).2.2,
    muBound_qubit,
    quantum_jarzynski Prot,
    crooks_per_transition Prot i_j j_j,
    helstrom_lower_bound T_test ρ σ⟩

#print axioms deutsch_bv_simon_qft_qpe_shor_qsp_and_grover_package
#print axioms metrology_geometric_speed_zeno_and_maassen_uffink_package
#print axioms jarzynski_crooks_chernoff_and_hoeffding_package
#print axioms static_and_potential_multiPower_yosida_coupled_to_qft_qpe_shor_qsp_grover
#print axioms growing_residual_hamiltonian_multiPower_yosida_coupled_to_metrology_jarzynski_crooks_helstrom
#print axioms fiveOperator_multiPower_yosida_quantum_algorithms_metrology_zeno_jarzynski_bridge

end

end UnifiedTheory.Audit.KFCausalClockFloorQuantumAlgorithmsDeutschSimonShorMetrologyZenoJarzynskiBridge
