/- Choi–Kraus Complete Positivity & Partial Trace Duality, Kraus CPTP Channel Representation,
Stinespring Isometric Dephasing Dilation, Holevo Accessible Information Bound, Quantum Cramér–Rao
Parameter Estimation Bound, and Helstrom Minimum-Error Discrimination & BB84 Security Bridged
with Arbitrary-Order Two-Parameter Yosida Cauchy Rate and `kthPowerGraphNormSq` Defect Convergence:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerB.ChoiKraus`,
   `UnifiedTheory.LayerB.KrausRepresentation`, and `UnifiedTheory.LayerB.StinespringDephasing`,
   certifying Hermitian symmetry and positive semidefiniteness of the Choi matrix `choi K`,
   the Choi–Kraus channel evaluation formula `krausChannel_eq_choi_apply`, left and right
   partial trace identities `partialTrace_left_choi` and `partialTrace_right_choi`,
   linearity, Hermiticity preservation, trace preservation, and positive semidefiniteness
   preservation of `KrausRepresentation.apply`, and the Stinespring isometric dilation
   `Vᵀ V = I` and `Tr_E(V ρ Vᵀ) = Φ_γ(ρ)` for qubit dephasing channels.
2. Bridges `UnifiedTheory.LayerB.HolevoBound`, `UnifiedTheory.LayerB.QuantumCramerRao`,
   and `UnifiedTheory.LayerB.HelstromBound`, certifying the Holevo accessible-information
   bound `postMeasurementMI ≤ holevoChi`, concavity nonnegativity `0 ≤ holevoChi`,
   vanishing on singleton/identical ensembles, pure-state and SLD Quantum Fisher Information
   nonnegativity (`0 ≤ pureFisher P θ`, `0 ≤ quantumFisherInformation S`), the pure and mixed
   Quantum Cramér–Rao bounds (`1 ≤ E.estVar * pureFisher P θ`, `QuantumCramerRaoBound F`),
   and the Helstrom trace-distance discrimination error bound (`helstromError ≤ 1 / 2`,
   `helstromError ≤ (typeI + typeII) / 2 ≤ 1 - helstromError`) and unconditional BB84 security.
3. Unites all six quantum channel, information, estimation, and discrimination packages with
   the arbitrary-order operator-power linearity, two-parameter Yosida Cauchy rate bounds,
   and `kthPowerGraphNormSq` sequential defect convergence across all five clock-floor
   Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)` from
   `KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate`. -/
import UnifiedTheory.LayerB.ChoiKraus
import UnifiedTheory.LayerB.KrausRepresentation
import UnifiedTheory.LayerB.HolevoBound
import UnifiedTheory.LayerB.StinespringDephasing
import UnifiedTheory.LayerB.QuantumCramerRao
import UnifiedTheory.LayerB.HelstromBound
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumChannelsChoiKrausHolevoCramerRaoHelstromBridge

noncomputable section

open Filter Matrix Complex
open scoped Topology InnerProduct BigOperators ComplexOrder MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.DensityMatrixHonest
open UnifiedTheory.LayerB.LindbladDephasing
open UnifiedTheory.LayerB.QuantumStein
open UnifiedTheory.LayerB.QuantumChernoff
open UnifiedTheory.LayerB.ChoiKraus
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.HolevoBound
open UnifiedTheory.LayerB.StinespringDephasing
open UnifiedTheory.LayerB.QuantumCramerRao
open UnifiedTheory.LayerB.HelstromBound
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorStaticResolventRadialCommutator (staticResolvent)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain staticPowerDomain potentialPowerDomain
   growingPowerDomain residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence (iteratedIdentityPower)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (iteratedOperatorPower kthPowerGraphNormSq)
open KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate
  (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
   static_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
   potential_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
   growing_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
   residual_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
   hamiltonian_arbitraryOrder_twoParam_cauchy_and_defect_on_succ
   fiveOperator_arbitraryOrder_twoParameter_yosida_cauchy_rate_master_synthesis)

/-! ### 1. Choi–Kraus Duality, Kraus CPTP Representation, and Stinespring Isometric Dilation -/

/-- Choi–Kraus complete positivity and partial trace duality package:
Hermiticity and positive semidefiniteness of `choi K`, channel recovery from `choi K`,
and left/right partial trace identities. -/
theorem choi_kraus_hermitian_posSemidef_and_partial_trace_package
    {m A : Type*} [Fintype m] [Fintype A]
    (K : A → Matrix m m ℂ) (ρ : Matrix m m ℂ) (i i' j j' : m) :
    (choi K).IsHermitian ∧
    (choi K).PosSemidef ∧
    (krausChannel K ρ) j j' = ∑ a, ∑ a', ρ a a' * choi K (a, j) (a', j') ∧
    UnifiedTheory.LayerB.PartialTrace.partialTrace_left (choi K) =
      ∑ α, K α * (K α).conjTranspose ∧
    UnifiedTheory.LayerB.PartialTrace.partialTrace_right (choi K) i i' =
      (∑ α, (K α).conjTranspose * K α) i' i :=
  ⟨choi_isHermitian K,
   choi_posSemidef K,
   krausChannel_eq_choi_apply K ρ j j',
   partialTrace_left_choi K,
   partialTrace_right_choi K i i'⟩

/-- Kraus CPTP representation package: linearity (`apply_add`, `apply_smul`, `apply_zero`),
Hermiticity preservation, trace preservation (`Tr(K(ρ)) = Tr(ρ)`), positive semidefiniteness
preservation, and identity channel action. -/
theorem kraus_representation_cptp_channel_package
    {m n k : ℕ} (K : KrausRepresentation m n k)
    (ρ σ : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (hHerm : ρ.IsHermitian) (hPSD : σ.PosSemidef) :
    K.apply (ρ + σ) = K.apply ρ + K.apply σ ∧
    K.apply (c • ρ) = c • K.apply ρ ∧
    K.apply 0 = 0 ∧
    (K.apply ρ).IsHermitian ∧
    Matrix.trace (K.apply ρ) = Matrix.trace ρ ∧
    (K.apply σ).PosSemidef ∧
    (KrausRepresentation.identity m).apply ρ = ρ :=
  ⟨K.apply_add ρ σ,
   K.apply_smul c ρ,
   K.apply_zero,
   K.apply_isHermitian hHerm,
   K.trace_apply ρ,
   K.apply_posSemidef hPSD,
   KrausRepresentation.identity_apply m ρ⟩

/-- Stinespring isometric dilation package for qubit dephasing:
Kraus normalization `α² + β² = 1` and difference `α² - β² = γ`, Pauli-`Z` involution
`σ_z² = I`, Stinespring isometry `Vᵀ V = I`, exact dilation identity `Tr_E(V ρ Vᵀ) = Φ_γ(ρ)`,
diagonal population preservation, coherence damping by `γ`, and trace preservation `= 1`. -/
theorem stinespring_dephasing_isometric_dilation_package
    (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w : KrausWeights γ) (ρ : DensityMatrix2Honest) (i j : Fin 2) :
    w.α ^ 2 + w.β ^ 2 = 1 ∧
    w.α ^ 2 - w.β ^ 2 = γ ∧
    (pauli_z i 0 * pauli_z 0 j + pauli_z i 1 * pauli_z 1 j) = id2 i j ∧
    vtv γ w i j = id2 i j ∧
    partialTraceE (vRhoVt γ w ρ) i j = dephasedRhoMatrix γ hγ_nn hγ_le_one ρ i j ∧
    partialTraceE (vRhoVt γ w ρ) 0 0 = ρ.p₁ ∧
    partialTraceE (vRhoVt γ w ρ) 1 1 = ρ.p₂ ∧
    partialTraceE (vRhoVt γ w ρ) 0 1 = γ * ρ.coh_re ∧
    partialTraceE (vRhoVt γ w ρ) 0 0 + partialTraceE (vRhoVt γ w ρ) 1 1 = 1 :=
  ⟨kraus_norm_unit γ w,
   kraus_diff_eq_gamma γ w,
   pauli_z_sq_eq_id i j,
   stinespringV_isIsometry γ w i j,
   stinespring_equation γ hγ_nn hγ_le_one w ρ i j,
   stinespring_p1 γ hγ_nn hγ_le_one w ρ,
   stinespring_p2 γ hγ_nn hγ_le_one w ρ,
   stinespring_coh γ hγ_nn hγ_le_one w ρ,
   stinespring_trace_one γ hγ_nn hγ_le_one w ρ⟩

/-- Boundary cases `γ = 1` (identity channel) and `γ = 0` (complete dephasing) alongside
the master Stinespring theorem. -/
theorem stinespring_boundary_and_master_package
    (w1 : KrausWeights 1) (w0 : KrausWeights 0) (ρ : DensityMatrix2Honest) :
    partialTraceE (vRhoVt 1 w1 ρ) 0 1 = ρ.coh_re ∧
    partialTraceE (vRhoVt 0 w0 ρ) 0 1 = 0 ∧
    (∀ γ : ℝ, ∀ w : KrausWeights γ, w.α ^ 2 + w.β ^ 2 = 1) ∧
    (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 → Nonempty (KrausWeights γ)) :=
  ⟨stinespring_identity_case w1 ρ,
   stinespring_full_dephasing_case w0 ρ,
   stinespring_master.1,
   stinespring_master.2.1⟩

/-! ### 2. Holevo Accessible Information Bound, Quantum Cramér–Rao, and Helstrom Discrimination -/

/-- Holevo accessible-information package: entropy-difference decomposition of `holevoChi`,
trace-1 convex-combination average state, vanishing on identical-state ensembles,
nonnegativity from von Neumann concavity, and the Holevo bound `postMeasurementMI ≤ holevoChi`. -/
theorem holevo_accessible_information_and_master_package
    {n N : ℕ} {β : Type*} [Fintype β]
    (p : Fin N → ℝ) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ρ : Fin N → ComplexDensityMatrix n) (σ : ComplexDensityMatrix n)
    (hConcave : VonNeumannConcavity n)
    (M : QuantumMeasurement n β)
    (hUmegaki : HolevoUmegakiForm (Fin N) n)
    (hMono : QuantumRelativeEntropyMonotonicity n β) :
    (holevoChi p hp_nn hp_sum ρ =
      vonNeumannEntropy (averageState p hp_nn hp_sum ρ) -
        ∑ i, p i * vonNeumannEntropy (ρ i) ∧
     (averageState p hp_nn hp_sum ρ).M = ∑ i, ((p i : ℂ)) • (ρ i).M ∧
     (averageState p hp_nn hp_sum ρ).M.trace = 1) ∧
    (averageState p hp_nn hp_sum (fun _ => σ)).M = σ.M ∧
    0 ≤ holevoChi p hp_nn hp_sum ρ ∧
    postMeasurementMI p hp_nn hp_sum ρ M ≤ holevoChi p hp_nn hp_sum ρ ∧
    Holevo_Theorem_Target :=
  ⟨holevo_master p hp_nn hp_sum ρ,
   averageState_M_of_identical p hp_nn hp_sum σ,
   holevoChi_nonneg_of_concave hConcave p hp_nn hp_sum ρ,
   postMeasurementMI_le_holevoChi p hp_nn hp_sum ρ M hUmegaki hMono,
   Holevo_Theorem_Target_holds⟩

/-- Pure-state Cauchy–Schwarz and Braunstein–Caves Quantum Fisher Information package:
sesquilinear norm identity, sharp complex Cauchy–Schwarz inequality, and pure-state QFI
nonnegativity `0 ≤ pureFisher P θ`. -/
theorem quantum_cramer_rao_pure_cauchy_schwarz_and_qfi_package
    {n : ℕ} (φ ψ : Fin n → ℂ) (P : ParametricPureState n) (θ : ℝ) :
    pureInner ψ ψ = ((pureNormSq ψ : ℝ) : ℂ) ∧
    0 ≤ pureNormSq ψ ∧
    Complex.normSq (pureInner φ ψ) ≤ pureNormSq φ * pureNormSq ψ ∧
    0 ≤ ParametricPureState.pureFisher P θ :=
  ⟨pureInner_self_eq_normSq ψ,
   pureNormSq_nonneg ψ,
   pureCauchySchwarz_sharp φ ψ,
   ParametricPureState.pureFisher_nonneg P θ⟩

/-- Pure-state and mixed-state SLD Quantum Cramér–Rao estimation bounds:
unconditional product bound `1 ≤ E.estVar * pureFisher P θ`, inverse bound
`1 / pureFisher P θ ≤ E.estVar` for `0 < pureFisher P θ`, SLD QFI nonnegativity
`0 ≤ quantumFisherInformation S`, `QuantumCramerRaoBound F`, and `BraunsteinCavesQFI F`. -/
theorem quantum_cramer_rao_pure_and_mixed_sld_master_package
    {n : ℕ} (P : ParametricPureState n) (F : ParametricDensityFamily n)
    (θ : ℝ) (E : UnbiasedEstimatorScore P θ)
    (S : SymmetricLogarithmicDerivative F θ) :
    1 ≤ E.estVar * ParametricPureState.pureFisher P θ ∧
    (0 < ParametricPureState.pureFisher P θ →
      1 / ParametricPureState.pureFisher P θ ≤ E.estVar) ∧
    0 ≤ quantumFisherInformation S ∧
    QuantumCramerRaoBound F ∧
    BraunsteinCavesQFI F :=
  ⟨quantum_cramer_rao_pure_product P θ E,
   quantum_cramer_rao_pure P θ E,
   quantumFisherInformation_nonneg S,
   quantum_cramer_rao_bound F,
   braunstein_caves_qfi_holds F⟩

/-- Helstrom minimum-error quantum state discrimination and unconditional BB84 security package:
trace distance nonnegativity, symmetry, and vanishing on identical states, Helstrom error
`helstromError ρ₀ ρ₁ = 1/2 - (1/2) * traceDistance ρ₀ ρ₁ ≤ 1/2`, two-sided POVM error bounds
`helstromError ≤ (typeI + typeII) / 2 ≤ 1 - helstromError`, and unconditional BB84 security. -/
theorem helstrom_discrimination_and_bb84_security_package
    {n : ℕ} (ρ₀ ρ₁ : ComplexDensityMatrix n) (T : BinaryHypothesisTest n) :
    0 ≤ UnifiedTheory.LayerB.HelstromBound.traceDistance ρ₀ ρ₁ ∧
    UnifiedTheory.LayerB.HelstromBound.traceDistance ρ₀ ρ₁ =
      UnifiedTheory.LayerB.HelstromBound.traceDistance ρ₁ ρ₀ ∧
    UnifiedTheory.LayerB.HelstromBound.traceDistance ρ₀ ρ₀ = 0 ∧
    helstromError ρ₀ ρ₁ ≤ 1 / 2 ∧
    helstromError ρ₀ ρ₀ = 1 / 2 ∧
    helstromError ρ₀ ρ₁ = helstromError ρ₁ ρ₀ ∧
    helstromError ρ₀ ρ₁ ≤ (typeI T ρ₀ + typeII T ρ₁) / 2 ∧
    (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁ ∧
    1 - (typeI T ρ₀ + typeII T ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁ ∧
    @BB84_Security_Target n :=
  ⟨ UnifiedTheory.LayerB.HelstromBound.traceDistance_nonneg ρ₀ ρ₁,
    UnifiedTheory.LayerB.HelstromBound.traceDistance_symm ρ₀ ρ₁,
    UnifiedTheory.LayerB.HelstromBound.traceDistance_self_eq_zero ρ₀,
    helstromError_le_half ρ₀ ρ₁,
    helstromError_identical ρ₀,
    helstromError_symm ρ₀ ρ₁,
    helstromError_lower_bound T ρ₀ ρ₁,
    average_error_le_one_sub_helstromError T ρ₀ ρ₁,
    BB84_security_unconditional ρ₀ ρ₁ T,
    BB84_Security_Target_holds ⟩

/-! ### 3. Synthesis with Arbitrary-Order Two-Parameter Yosida Cauchy Rates -/

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

/-- Master Quantum Channels, Choi–Kraus Duality, Stinespring Dephasing Dilation, Holevo Bound,
Quantum Cramér–Rao Bound, Helstrom State Discrimination & BB84 Security, and Five-Operator
Arbitrary-Order Two-Parameter Yosida Cauchy Rate Synthesis. -/
theorem clockFloor_quantum_channels_choi_kraus_holevo_cramer_rao_helstrom_master_synthesis
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n_pow r : ℕ)
    {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n_pow + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n_pow + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n_pow + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n_pow + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n_pow + 1))
    {m_ch A_ch : Type*} [Fintype m_ch] [Fintype A_ch]
    (K_choi : A_ch → Matrix m_ch m_ch ℂ)
    {m_kr n_kr k_kr : ℕ} (K_kr : KrausRepresentation m_kr n_kr k_kr)
    (ρ_kr : Matrix (Fin m_kr) (Fin m_kr) ℂ)
    (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (w_st : KrausWeights γ) (ρ_st : DensityMatrix2Honest)
    {n_q N_q : ℕ} (p_ens : Fin N_q → ℝ)
    (hp_nn : ∀ i, 0 ≤ p_ens i) (hp_sum : ∑ i, p_ens i = 1)
    (ρ_ens : Fin N_q → ComplexDensityMatrix n_q)
    (P_pure : ParametricPureState n_q) (F_mixed : ParametricDensityFamily n_q)
    (θ : ℝ) (E_est : UnbiasedEstimatorScore P_pure θ)
    (ρ₀ ρ₁ : ComplexDensityMatrix n_q) (T_test : BinaryHypothesisTest n_q) :
    ((kthPowerGraphNormSq T_op n_pow
        (iteratedIdentityPower (RT a) a r xT - iteratedIdentityPower (RT b) b r xT) ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq T_op (n_pow + 1) xT ∧
      kthPowerGraphNormSq P_op n_pow
        (iteratedIdentityPower (RP a) a r xP - iteratedIdentityPower (RP b) b r xP) ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq P_op (n_pow + 1) xP ∧
      kthPowerGraphNormSq G_op n_pow
        (iteratedIdentityPower (RG a) a r xG - iteratedIdentityPower (RG b) b r xG) ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq G_op (n_pow + 1) xG ∧
      kthPowerGraphNormSq (S_op t) n_pow
        (iteratedIdentityPower (RS t a) a r xS - iteratedIdentityPower (RS t b) b r xS) ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (S_op t) (n_pow + 1) xS ∧
      kthPowerGraphNormSq (H_op t) n_pow
        (iteratedIdentityPower (RH t a) a r xH - iteratedIdentityPower (RH t b) b r xH) ≤
        ((r : ℝ) * (a⁻¹ + b⁻¹)) ^ 2 * kthPowerGraphNormSq (H_op t) (n_pow + 1) xH) ∧
     Tendsto
       (fun m_seq : ℕ =>
         kthPowerGraphNormSq (H_op t) n_pow
           (iteratedIdentityPower (RH t ((m_seq : ℝ) + 1)) ((m_seq : ℝ) + 1) r xH - xH))
       atTop (𝓝 0)) ∧
    ((choi K_choi).IsHermitian ∧
     (choi K_choi).PosSemidef ∧
     Matrix.trace (K_kr.apply ρ_kr) = Matrix.trace ρ_kr ∧
     w_st.α ^ 2 + w_st.β ^ 2 = 1 ∧
     partialTraceE (vRhoVt γ w_st ρ_st) 0 0 + partialTraceE (vRhoVt γ w_st ρ_st) 1 1 = 1) ∧
    (holevoChi p_ens hp_nn hp_sum ρ_ens =
       vonNeumannEntropy (averageState p_ens hp_nn hp_sum ρ_ens) -
         ∑ i, p_ens i * vonNeumannEntropy (ρ_ens i) ∧
     Holevo_Theorem_Target ∧
     0 ≤ ParametricPureState.pureFisher P_pure θ ∧
     1 ≤ E_est.estVar * ParametricPureState.pureFisher P_pure θ ∧
     QuantumCramerRaoBound F_mixed ∧
     helstromError ρ₀ ρ₁ ≤ (typeI T_test ρ₀ + typeII T_test ρ₁) / 2 ∧
     1 - (typeI T_test ρ₀ + typeII T_test ρ₁) / 2 ≤ 1 - helstromError ρ₀ ρ₁) := by
  have hy := fiveOperator_arbitraryOrder_twoParameter_yosida_cauchy_rate_master_synthesis
    ε hε h hh hb m g k t a b ha hb_pos n_pow r hxT hxP hxG hxS hxH
  exact ⟨⟨hy.1, hy.2.2.2.2.2⟩,
    ⟨choi_isHermitian K_choi,
     choi_posSemidef K_choi,
     K_kr.trace_apply ρ_kr,
     kraus_norm_unit γ w_st,
     stinespring_trace_one γ hγ_nn hγ_le_one w_st ρ_st⟩,
    ⟨holevoChi_eq_entropy_difference p_ens hp_nn hp_sum ρ_ens,
     Holevo_Theorem_Target_holds,
     ParametricPureState.pureFisher_nonneg P_pure θ,
     quantum_cramer_rao_pure_product P_pure θ E_est,
     quantum_cramer_rao_bound F_mixed,
     helstromError_lower_bound T_test ρ₀ ρ₁,
     BB84_security_unconditional ρ₀ ρ₁ T_test⟩⟩

#print axioms choi_kraus_hermitian_posSemidef_and_partial_trace_package
#print axioms kraus_representation_cptp_channel_package
#print axioms stinespring_dephasing_isometric_dilation_package
#print axioms stinespring_boundary_and_master_package
#print axioms holevo_accessible_information_and_master_package
#print axioms quantum_cramer_rao_pure_cauchy_schwarz_and_qfi_package
#print axioms quantum_cramer_rao_pure_and_mixed_sld_master_package
#print axioms helstrom_discrimination_and_bb84_security_package
#print axioms clockFloor_quantum_channels_choi_kraus_holevo_cramer_rao_helstrom_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorQuantumChannelsChoiKrausHolevoCramerRaoHelstromBridge
