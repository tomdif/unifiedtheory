/- Open Quantum Systems, GKSL Lindblad Master Equation, Kraus-Lindblad Dephasing
CPTP Bridge, Kubo-Martin-Schwinger (KMS) Modular Thermal Equilibrium,
Decoherence-Temperature Correspondence, Zurek Pointer-State Einselection, and
Gelfand-Naimark-Segal (GNS) Cyclic Hilbert Representation Bridge:
1. Synthesizes the finite-dimensional GNS sesquilinear form `gnsForm ρ A B = Tr(ρ Aᴴ B)`,
   establishing positivity `0 ≤ Re ⟨A, A⟩_ω`, right-linearity, left conjugate-linearity,
   Hermitian symmetry, cyclic state recovery `stateFunctional ρ A = gnsForm ρ.M 1 A`,
   null-space invariance, and the Gelfand-Naimark faithfulness theorem.
2. Connects the spectral unitary Heisenberg evolution `unitaryEvolution H hH t` and
   modular automorphism group `modularFlow H hH t` with the Gibbs thermal state
   `gibbsState β H`, Boltzmann-unitary commutativity, unconditional Gibbs stationarity
   `gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A`, tracial
   `β = 0` KMS invariance, detailed-balance spectral ratios, Hawking KMS period
   `8 π M`, and the dephasing-temperature Lorentzian/Matsubara correspondence.
3. Unites the Kraus operator-sum CPTP representation (`KrausRepresentation`,
   `dephasingKraus`), the GKSL Lindblad master generator (`lindbladian`, trace
   preservation, Hermiticity preservation, linearity, and zero-jump von Neumann limit),
   dynamical Lindblad coherence decay (`gamma rate t = exp(-Γ t)`, arrow of time,
   and `t → ∞` classical limit), and Zurek pointer-basis einselection
   (`diagonalDephasing`, idempotence, fixed-point diagonal characterization, and
   pairwise distinguishable pointer states). -/
import UnifiedTheory.LayerB.GNSConstruction
import UnifiedTheory.LayerB.KMSCondition
import UnifiedTheory.LayerB.KMSFromDephasing
import UnifiedTheory.LayerB.KrausLindbladBridge
import UnifiedTheory.LayerB.LindbladEquation
import UnifiedTheory.LayerB.LindbladDecoherence
import UnifiedTheory.LayerB.ZurekEinselection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorOpenQuantumLindbladKMSDecoherenceGNSBridge

open Matrix Complex
open scoped BigOperators Matrix ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.GNSConstruction
open UnifiedTheory.LayerB.KMSCondition
open UnifiedTheory.LayerB.KMSFromDephasing
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.LindbladEquation
open UnifiedTheory.LayerB.DensityMatrix
open UnifiedTheory.LayerB.LindbladDecoherence
open UnifiedTheory.LayerB.ZurekEinselection

/-- Positivity (`0 ≤ Re ⟨A, A⟩_ω`), trace definition, and Hermitian symmetry of the
GNS sesquilinear form induced by any complex density matrix `ρ`. -/
theorem gns_sesquilinear_positivity_and_hermitian {n : ℕ}
    (ρ : ComplexDensityMatrix n) (A B : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ.M A B = Matrix.trace (ρ.M * Aᴴ * B) ∧
    0 ≤ (gnsForm ρ.M A A).re ∧
    gnsForm ρ.M A B = star (gnsForm ρ.M B A) :=
  ⟨gnsForm_def ρ.M A B,
   gnsForm_self_nonneg ρ A,
   gnsForm_hermitian ρ A B⟩

/-- Full sesquilinearity of `gnsForm`: additivity and `ℂ`-linearity in the right slot,
together with additivity and conjugate-linearity in the left slot. -/
theorem gns_sesquilinear_right_and_left_linearity {n : ℕ}
    (ρ A₁ A₂ B₁ B₂ : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    gnsForm ρ A₁ (B₁ + B₂) = gnsForm ρ A₁ B₁ + gnsForm ρ A₁ B₂ ∧
    gnsForm ρ A₁ (c • B₁) = c * gnsForm ρ A₁ B₁ ∧
    gnsForm ρ (A₁ + A₂) B₁ = gnsForm ρ A₁ B₁ + gnsForm ρ A₂ B₁ ∧
    gnsForm ρ (c • A₁) B₁ = (starRingEnd ℂ) c * gnsForm ρ A₁ B₁ :=
  ⟨gnsForm_add_right ρ A₁ B₁ B₂,
   gnsForm_smul_right ρ A₁ B₁ c,
   gnsForm_add_left ρ A₁ A₂ B₁,
   gnsForm_smul_left ρ A₁ B₁ c⟩

/-- Cyclicity of the identity vector `Ω = 1` in the GNS construction: normalization
`ω(1) = 1` and exact state recovery `ω(A) = ⟨1, A⟩_ω = Tr(ρ A)`. -/
theorem gns_cyclic_vector_and_state_recovery {n : ℕ}
    (ρ : ComplexDensityMatrix n) (A : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ.M 1 A = Matrix.trace (ρ.M * A) ∧
    stateFunctional ρ 1 = 1 ∧
    stateFunctional ρ A = gnsForm ρ.M 1 A :=
  ⟨gns_cyclic ρ.M A,
   stateFunctional_one ρ,
   stateFunctional_eq_gns ρ A⟩

/-- Null-space invariance under scalar multiplication and unconditional discharge of
both `@GelfandNaimark_Target n` and `@GNS_Representation_Target n` in the matrix model. -/
theorem gns_null_space_and_gelfand_naimark_bridge {n : ℕ}
    (ρ A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    InNullSpace ρ 0 ∧
    (InNullSpace ρ A → InNullSpace ρ (c • A)) ∧
    @GelfandNaimark_Target n ∧
    @GNS_Representation_Target n :=
  ⟨zero_inNullSpace ρ,
   smul_inNullSpace ρ A c,
   gelfandNaimark_matrix_model,
   fun σ => ⟨fun X => gnsForm_self_nonneg σ X,
             fun X Y => gnsForm_hermitian σ X Y,
             fun X => stateFunctional_eq_gns σ X⟩⟩

/-- Spectral phase-factor and diagonal-phase group identities for a Hermitian
Hamiltonian `H`. -/
theorem kms_phase_factor_and_diagonal_unitarity {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t lam : ℝ) :
    phaseFactor 0 lam = 1 ∧
    phaseFactor t lam * phaseFactor (-t) lam = 1 ∧
    star (phaseFactor t lam) = phaseFactor (-t) lam ∧
    phaseDiagonal H hH 0 = 1 ∧
    phaseDiagonal H hH t * phaseDiagonal H hH (-t) = 1 :=
  ⟨phaseFactor_zero lam,
   phaseFactor_mul_neg t lam,
   star_phaseFactor t lam,
   phaseDiagonal_zero H hH,
   phaseDiagonal_mul_neg H hH t⟩

/-- Unitary group membership and inversion identities for the spectral unitary time
evolution `unitaryEvolution H hH t = exp(i H t)`. -/
theorem kms_unitary_evolution_group_relations {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    unitaryEvolution H hH 0 = 1 ∧
    star (unitaryEvolution H hH t) = unitaryEvolution H hH (-t) ∧
    unitaryEvolution H hH t * star (unitaryEvolution H hH t) = 1 ∧
    star (unitaryEvolution H hH t) * unitaryEvolution H hH t = 1 ∧
    unitaryEvolution H hH t ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨unitaryEvolution_zero H hH,
   star_unitaryEvolution H hH t,
   unitaryEvolution_mul_star H hH t,
   star_mul_unitaryEvolution H hH t,
   unitaryEvolution_unitary H hH t⟩

/-- Algebra-automorphism laws for the Heisenberg modular flow
`modularFlow H hH t A = U_t A U_{-t}`: identity at `t = 0`, unit preservation,
linearity, scalar homogeneity, and multiplicativity. -/
theorem kms_modular_flow_automorphism_laws {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    modularFlow H hH 0 A = A ∧
    modularFlow H hH t 1 = 1 ∧
    modularFlow H hH t (A + B) = modularFlow H hH t A + modularFlow H hH t B ∧
    modularFlow H hH t (c • A) = c • modularFlow H hH t A ∧
    modularFlow H hH t (A * B) = modularFlow H hH t A * modularFlow H hH t B :=
  ⟨modularFlow_zero H hH A,
   modularFlow_one H hH t,
   modularFlow_add H hH t A B,
   modularFlow_smul H hH t c A,
   modularFlow_mul H hH t A B⟩

/-- Strict positivity of the thermal partition function `Z(β, H) > 0` and exact trace
identities for the Boltzmann operator `boltzmannOp β H = exp(-β H)`. -/
theorem kms_partition_function_and_boltzmann_trace {n : ℕ} [Nonempty (Fin n)]
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    0 < partitionFunction β H ∧
    (Matrix.trace (boltzmannOp β H)).re = partitionFunction β H ∧
    Matrix.trace (boltzmannOp β H) = ((partitionFunction β H : ℝ) : ℂ) :=
  ⟨partitionFunction_pos β H hH,
   trace_boltzmannOp β H,
   trace_boltzmannOp_eq_Z_cast β H hH⟩

/-- Normalization `ω_β(1) = 1`, additivity, and complex scalar homogeneity of the
Gibbs thermal expectation functional `gibbsExpectation β H`. -/
theorem kms_gibbs_expectation_normalization_and_linearity {n : ℕ} [Nonempty (Fin n)]
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    gibbsExpectation β H 1 = 1 ∧
    gibbsExpectation β H (A + B) = gibbsExpectation β H A + gibbsExpectation β H B ∧
    gibbsExpectation β H (c • A) = c * gibbsExpectation β H A :=
  ⟨gibbs_normalized β H hH,
   gibbsExpectation_add β H A B,
   gibbsExpectation_smul β H c A⟩

/-- Exact commutation of the Boltzmann weight operator `exp(-β H)` with the unitary
evolution `U_t` and unconditional stationarity of the Gibbs state under the modular
flow `σ_t`. -/
theorem kms_boltzmann_commutation_and_gibbs_stationarity {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    boltzmannOp β H * unitaryEvolution H hH t =
      unitaryEvolution H hH t * boltzmannOp β H ∧
    gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A :=
  ⟨boltzmannOp_unitaryEvolution_comm β H hH t,
   gibbs_is_stationary β H hH A t⟩

/-- The normalized trace satisfies the `β = 0` KMS condition for any Hermitian
Hamiltonian `H`, and its expectation is tracial (`τ(A B) = τ(B A)`). -/
theorem kms_real_stationarity_and_tracial_zero_temperature {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    KMSCondition normalizedTrace H hH 0 ∧
    normalizedTrace (A * B) = normalizedTrace (B * A) :=
  ⟨trace_is_kms_zero H hH,
   KMS_zero_is_tracial normalizedTrace H hH (trace_is_kms_zero H hH) A B⟩

/-- Spectral detailed-balance Boltzmann ratio `exp(-β E_b) / exp(-β E_a) =
exp(-β(E_b - E_a))`, infinite-temperature unit ratio at `β = 0`, and Hawking-KMS
inverse temperature `β_H(M) = 8 π M`. -/
theorem kms_detailed_balance_and_hawking_period
    (β E_a E_b M : ℝ) (hM : 0 < M) :
    Real.exp (-β * E_b) / Real.exp (-β * E_a) = Real.exp (-β * (E_b - E_a)) ∧
    Real.exp (-(0 : ℝ) * E_b) / Real.exp (-(0 : ℝ) * E_a) = 1 ∧
    UnifiedTheory.LayerB.BisognanoWichmann.bwInverseTemperature (1 / (4 * M)) =
      8 * Real.pi * M :=
  ⟨detailed_balance_ratio β E_a E_b,
   detailed_balance_zero_temperature E_a E_b,
   hawking_kms_period_substantive_holds M hM⟩

/-- Decoherence-temperature correspondence: factorization of `dephasedAmplitude k Γ s`
into exponential decay times oscillatory phase, identification of the dephasing
factor `exp(-Γ s)` with the Boltzmann weight `exp(-s / T)` at `T = 1 / Γ`, and unit
weight at zero dephasing. -/
theorem dephasing_kms_amplitude_and_boltzmann_weight
    (k Γ s : ℝ) (hΓ : 0 < Γ) :
    dephasedAmplitude k Γ s =
      (⟨Real.exp (-Γ * s), 0⟩ : ℂ) *
        UnifiedTheory.LayerB.PropagationRule.expAmplitude k s ∧
    Real.exp (-Γ * s) = Real.exp (-s / (1 / Γ)) ∧
    Real.exp (-(0 : ℝ) * s) = 1 :=
  ⟨dephased_decomposition k Γ s,
   dephasing_is_boltzmann Γ s hΓ,
   zero_dephasing s⟩

/-- Strict positivity, resonance peak `2 / Γ`, frequency-reversal symmetry of the
Lorentzian spectral function `lorentzian ω k Γ`, and Matsubara thermal frequency
quantization. -/
theorem dephasing_kms_lorentzian_and_matsubara
    (ω k Γ β : ℝ) (n : ℤ) (hΓ : 0 < Γ) (hβ : β ≠ 0) :
    0 < lorentzian ω k Γ ∧
    lorentzian k k Γ = 2 / Γ ∧
    lorentzian (-ω) k Γ = lorentzian ω (-k) Γ ∧
    2 * Real.pi * n / β * β = 2 * Real.pi * n :=
  ⟨lorentzian_pos ω k Γ hΓ,
   lorentzian_peak k Γ hΓ,
   lorentzian_neg_freq ω k Γ,
   matsubara β hβ n⟩

/-- Zero-preservation, additivity, and scalar homogeneity of the operator-sum map
induced by any Kraus representation `K : KrausRepresentation m n k`. -/
theorem kraus_operator_sum_linearity_and_zero {m n k : ℕ}
    (K : KrausRepresentation m n k) (c : ℂ) (ρ σ : Matrix (Fin m) (Fin m) ℂ) :
    K.apply 0 = 0 ∧
    K.apply (ρ + σ) = K.apply ρ + K.apply σ ∧
    K.apply (c • ρ) = c • K.apply ρ :=
  ⟨K.apply_zero,
   K.apply_add ρ σ,
   K.apply_smul c ρ⟩

/-- Every Kraus operator-sum map preserves trace (`Tr(K(ρ)) = Tr(ρ)`), Hermiticity,
and positive semidefiniteness. -/
theorem kraus_operator_sum_cptp_structural_preservation {m n k : ℕ}
    (K : KrausRepresentation m n k) (ρ : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace (K.apply ρ) = Matrix.trace ρ ∧
    (ρ.IsHermitian → (K.apply ρ).IsHermitian) ∧
    (ρ.PosSemidef → (K.apply ρ).PosSemidef) :=
  ⟨K.trace_apply ρ,
   fun hρ => K.apply_isHermitian hρ,
   fun hρ => K.apply_posSemidef hρ⟩

/-- Identity Kraus representation action `(identity m).apply ρ = ρ` and Hermiticity /
involutivity (`σ_z† = σ_z`, `σ_z² = I`) of the complex Pauli `σ_z` matrix. -/
theorem kraus_identity_and_pauli_z_involutive {m : ℕ}
    (ρ : Matrix (Fin m) (Fin m) ℂ) :
    (KrausRepresentation.identity m).apply ρ = ρ ∧
    pauliZ.conjTranspose = pauliZ ∧
    pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨KrausRepresentation.identity_apply m ρ,
   pauliZ_conjTranspose,
   pauliZ_mul_self⟩

/-- Explicit operator-sum action `((1 + γ)/2) ρ + ((1 - γ)/2) σ_z ρ σ_z` and CPTP
property of the 2-qubit Kraus dephasing channel `dephasingKraus γ` for `γ ∈ [-1, 1]`. -/
theorem kraus_dephasing_channel_formula_and_cptp
    (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingKraus γ hγ_le hγ_ge).apply ρ =
      (((1 + γ) / 2 : ℝ) : ℂ) • ρ +
        (((1 - γ) / 2 : ℝ) : ℂ) • (pauliZ * ρ * pauliZ) ∧
    IsCPTP (dephasingKraus γ hγ_le hγ_ge).toLinearMap :=
  ⟨dephasingKraus_apply_formula γ hγ_le hγ_ge ρ,
   dephasingKraus_isCPTP γ hγ_le hγ_ge⟩

/-- Boundary limits of the Kraus dephasing channel: identity channel at `γ = 1`
(no decoherence) and equal-weight Pauli-Z pinching `(ρ + σ_z ρ σ_z) / 2` at `γ = 0`
(full decoherence). -/
theorem kraus_dephasing_channel_boundary_cases
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingKraus 1 le_rfl (by norm_num)).apply ρ = ρ ∧
    (dephasingKraus 0 (by norm_num) (by norm_num)).apply ρ =
      ((1 / 2 : ℝ) : ℂ) • ρ + ((1 / 2 : ℝ) : ℂ) • (pauliZ * ρ * pauliZ) :=
  ⟨dephasingKraus_at_one ρ,
   dephasingKraus_at_zero ρ⟩

/-- Exact trace preservation of the GKSL Lindblad master generator: the von Neumann
commutator part, each single-jump dissipator, and the full Lindbladian all have
vanishing trace. -/
theorem lindblad_generator_trace_preservation {n m : ℕ}
    (H L₀ ρ : Matrix (Fin n) (Fin n) ℂ)
    (L : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (vonNeumannPart H ρ).trace = 0 ∧
    (dissipator L₀ ρ).trace = 0 ∧
    (lindbladian H L ρ).trace = 0 :=
  ⟨vonNeumannPart_traceless H ρ,
   dissipator_traceless L₀ ρ,
   lindbladian_traceless H L ρ⟩

/-- Dagger-commutation and Hermiticity preservation of the dissipator, von Neumann
commutator, and full GKSL Lindbladian when the Hamiltonian `H` is Hermitian. -/
theorem lindblad_generator_dagger_and_hermiticity_preservation {n m : ℕ}
    (H L₀ ρ : Matrix (Fin n) (Fin n) ℂ)
    (L : Fin m → Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (dissipator L₀ ρ)ᴴ = dissipator L₀ ρᴴ ∧
    (vonNeumannPart H ρ)ᴴ = vonNeumannPart H ρᴴ ∧
    (lindbladian H L ρ)ᴴ = lindbladian H L ρᴴ ∧
    (ρ.IsHermitian → (lindbladian H L ρ).IsHermitian) :=
  ⟨dissipator_conjTranspose L₀ ρ,
   vonNeumannPart_conjTranspose H ρ hH,
   lindbladian_preserves_hermitian H L ρ hH,
   fun hρ => lindbladian_isHermitian_of_isHermitian H L ρ hH hρ⟩

/-- Linearity (additivity and complex scalar homogeneity) of the von Neumann part,
dissipator, and full Lindbladian generator in the state `ρ`. -/
theorem lindblad_generator_linearity_in_state {n m : ℕ}
    (c : ℂ) (H L₀ ρ σ : Matrix (Fin n) (Fin n) ℂ)
    (L : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    vonNeumannPart H (ρ + σ) = vonNeumannPart H ρ + vonNeumannPart H σ ∧
    dissipator L₀ (ρ + σ) = dissipator L₀ ρ + dissipator L₀ σ ∧
    lindbladian H L (ρ + σ) = lindbladian H L ρ + lindbladian H L σ ∧
    lindbladian H L (c • ρ) = c • lindbladian H L ρ :=
  ⟨vonNeumannPart_add H ρ σ,
   dissipator_add L₀ ρ σ,
   lindbladian_add H L ρ σ,
   lindbladian_smul c H L ρ⟩

/-- Reduction of the GKSL Lindbladian to the unitary von Neumann commutator
`-i [H, ρ]` whenever the jump operators vanish or the jump index set is empty. -/
theorem lindblad_generator_no_jump_von_neumann_reduction {n m : ℕ}
    (H ρ : Matrix (Fin n) (Fin n) ℂ)
    (L₀ : Fin 0 → Matrix (Fin n) (Fin n) ℂ)
    (L : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    dissipator (0 : Matrix (Fin n) (Fin n) ℂ) ρ = 0 ∧
    lindbladian H L₀ ρ = vonNeumannPart H ρ ∧
    ((∀ k, L k = 0) → lindbladian H L ρ = vonNeumannPart H ρ) :=
  ⟨dissipator_zero ρ,
   lindbladian_eq_vonNeumann_of_no_jumps H L₀ ρ,
   lindbladian_eq_vonNeumann_of_jumps_zero H L ρ⟩

/-- Dynamical properties of the Lindblad dephasing factor `gamma rate t = exp(-Γ t)`:
unit value at `t = 0`, strict positivity, upper bound by `1` for `t ≥ 0`, antitone
exponential decay, and positive decoherence timescale `t_d = 1 / Γ > 0`. -/
theorem lindblad_decoherence_gamma_decay_laws
    (rate : DephasingRate) (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    gamma rate 0 = 1 ∧
    0 < gamma rate t₁ ∧
    gamma rate t₁ ≤ 1 ∧
    gamma rate t₂ ≤ gamma rate t₁ ∧
    0 < decoherenceTime rate :=
  ⟨gamma_at_zero rate,
   gamma_pos rate t₁,
   gamma_le_one rate t₁ ht₁,
   gamma_antitone rate t₁ t₂ h12,
   decoherence_time_pos rate⟩

/-- Under Lindblad dephasing evolution `lindbladEvolve rate t ρ`, diagonal
populations `(p₁, p₂)` are conserved, off-diagonal coherences contract by `gamma rate t`,
and the total observable equals `p₁ + p₂ + 2 · gamma rate t · coh_re`. -/
theorem lindblad_decoherence_population_and_coherence_evolution
    (rate : DephasingRate) (t : ℝ) (ρ : DensityMatrix2) :
    ((lindbladEvolve rate t ρ).p₁ = ρ.p₁ ∧
     (lindbladEvolve rate t ρ).p₂ = ρ.p₂) ∧
    ((lindbladEvolve rate t ρ).coh_re = gamma rate t * ρ.coh_re ∧
     (lindbladEvolve rate t ρ).coh_im = gamma rate t * ρ.coh_im) ∧
    totalObs (lindbladEvolve rate 0 ρ) = totalObs ρ ∧
    totalObs (lindbladEvolve rate t ρ) =
      ρ.p₁ + ρ.p₂ + 2 * gamma rate t * ρ.coh_re :=
  ⟨lindblad_preserves_populations rate t ρ,
   lindblad_contracts_coherence rate t ρ,
   lindblad_at_zero rate ρ,
   lindblad_observable rate t ρ⟩

/-- Arrow of time and asymptotic classicality under Lindblad dephasing: the distance
`|totalObs(t) - (p₁ + p₂)|` from the classical population sum decreases monotonically
with time and converges to `0` as `t → ∞`. -/
theorem lindblad_decoherence_arrow_of_time_and_classical_limit
    (rate : DephasingRate) (ρ : DensityMatrix2) (t₁ t₂ : ℝ) (h12 : t₁ ≤ t₂) :
    |totalObs (lindbladEvolve rate t₂ ρ) - (ρ.p₁ + ρ.p₂)| ≤
      |totalObs (lindbladEvolve rate t₁ ρ) - (ρ.p₁ + ρ.p₂)| ∧
    (ρ.coh_re ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T < t →
        |totalObs (lindbladEvolve rate t ρ) - (ρ.p₁ + ρ.p₂)| < ε) :=
  ⟨observable_approaches_classical rate ρ t₁ t₂ h12,
   fun hcoh ε hε => lindblad_classical_limit rate ρ hcoh ε hε⟩

/-- Matrix-level properties of the diagonal projection `diagProjMatrix`: diagonal
preservation, trace preservation, idempotence, and Hermiticity preservation. -/
theorem zurek_diagonal_projection_matrix_properties {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    diagProjMatrix M i i = M i i ∧
    (diagProjMatrix M).trace = M.trace ∧
    diagProjMatrix (diagProjMatrix M) = diagProjMatrix M ∧
    (M.IsHermitian → (diagProjMatrix M).IsHermitian) :=
  ⟨diagProjMatrix_apply_eq M i,
   diagProjMatrix_trace M,
   diagProjMatrix_idempotent M,
   fun hM => diagProjMatrix_isHermitian hM⟩

/-- Diagonal entries of any `ComplexDensityMatrix n` are real and non-negative, and
the Zurek einselection channel `diagonalDephasing n ρ` acts on the underlying matrix
as `diagProjMatrix ρ.M`. -/
theorem zurek_density_matrix_diagonal_populations {n : ℕ}
    (ρ : ComplexDensityMatrix n) (i : Fin n) :
    (ρ.M i i).im = 0 ∧
    0 ≤ (ρ.M i i).re ∧
    (diagonalDephasing n ρ).M = diagProjMatrix ρ.M :=
  ⟨diag_im_zero ρ i,
   diag_re_nonneg ρ i,
   diagonalDephasing_M ρ⟩

/-- Zurek einselection projector idempotence (`D(D(ρ)) = D(ρ)`) and exact
characterization of einselected fixed points as diagonal density matrices. -/
theorem zurek_einselection_idempotence_and_fixed_points {n : ℕ}
    (ρ : ComplexDensityMatrix n) :
    (diagonalDephasing n (diagonalDephasing n ρ)).M =
      (diagonalDephasing n ρ).M ∧
    ((diagonalDephasing n ρ).M = ρ.M ↔ ∀ i j, i ≠ j → ρ.M i j = 0) :=
  ⟨dephasing_idempotent ρ,
   dephasing_fixed_points ρ⟩

/-- Under Zurek einselection `diagonalDephasing n ρ`, diagonal populations survive
unchanged while all off-diagonal quantum coherences are annihilated. -/
theorem zurek_einselection_populations_survive_coherences_die {n : ℕ}
    (ρ : ComplexDensityMatrix n) (i j : Fin n) :
    (diagonalDephasing n ρ).M i i = ρ.M i i ∧
    (i ≠ j → (diagonalDephasing n ρ).M i j = 0) :=
  ⟨dephasing_preserves_diagonal ρ i,
   fun hij => dephasing_kills_offdiagonal ρ hij⟩

/-- Each rank-1 pointer state `pointerStates n i` has Kronecker-delta diagonal entries,
is a fixed point of `diagonalDephasing n`, and is distinguishable from `pointerStates n j`
for `i ≠ j`. -/
theorem zurek_pointer_states_einselected_and_distinguishable {n : ℕ} [NeZero n]
    (i j : Fin n) :
    (pointerStates n i).M j j = (if j = i then 1 else 0 : ℂ) ∧
    (diagonalDephasing n (pointerStates n i)).M = (pointerStates n i).M ∧
    (i ≠ j → (pointerStates n i).M ≠ (pointerStates n j).M) :=
  ⟨pointerStates_diag i j,
   pointer_states_einselected i,
   fun hij => pointer_states_pairwise_distinguishable hij⟩

/-- Master synthesis bridge uniting GNS sesquilinear positivity and cyclic state
recovery, KMS modular automorphism and Gibbs thermal stationarity, Boltzmann-dephasing
correspondence, Kraus-Lindblad CPTP dephasing, GKSL trace preservation, Lindblad
exponential decoherence, and Zurek pointer-state einselection. -/
theorem open_quantum_lindblad_kms_decoherence_gns_master_bridge :
    (∀ {n : ℕ} (ρ : ComplexDensityMatrix n) (A : Matrix (Fin n) (Fin n) ℂ),
      0 ≤ (gnsForm ρ.M A A).re ∧ stateFunctional ρ A = gnsForm ρ.M 1 A) ∧
    (∀ {n : ℕ} (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      boltzmannOp β H * unitaryEvolution H hH t =
        unitaryEvolution H hH t * boltzmannOp β H ∧
      gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A) ∧
    (∀ (Γ s : ℝ), 0 < Γ → Real.exp (-Γ * s) = Real.exp (-s / (1 / Γ))) ∧
    (∀ (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ),
      IsCPTP (dephasingKraus γ hγ_le hγ_ge).toLinearMap) ∧
    (∀ {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
      (L : Fin m → Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ),
      (lindbladian H L ρ).trace = 0) ∧
    (∀ (rate : DephasingRate) (ρ : DensityMatrix2) (t₁ t₂ : ℝ), t₁ ≤ t₂ →
      |totalObs (lindbladEvolve rate t₂ ρ) - (ρ.p₁ + ρ.p₂)| ≤
        |totalObs (lindbladEvolve rate t₁ ρ) - (ρ.p₁ + ρ.p₂)|) ∧
    (∀ {n : ℕ} (ρ : ComplexDensityMatrix n),
      (diagonalDephasing n (diagonalDephasing n ρ)).M = (diagonalDephasing n ρ).M ∧
      ((diagonalDephasing n ρ).M = ρ.M ↔ ∀ i j, i ≠ j → ρ.M i j = 0)) :=
  ⟨fun ρ A => ⟨gnsForm_self_nonneg ρ A, stateFunctional_eq_gns ρ A⟩,
   fun β H hH A t => ⟨boltzmannOp_unitaryEvolution_comm β H hH t,
                      gibbs_is_stationary β H hH A t⟩,
   dephasing_is_boltzmann,
   dephasingKraus_isCPTP,
   lindbladian_traceless,
   observable_approaches_classical,
   fun ρ => ⟨dephasing_idempotent ρ, dephasing_fixed_points ρ⟩⟩

#print axioms gns_sesquilinear_positivity_and_hermitian
#print axioms gns_sesquilinear_right_and_left_linearity
#print axioms gns_cyclic_vector_and_state_recovery
#print axioms gns_null_space_and_gelfand_naimark_bridge
#print axioms kms_phase_factor_and_diagonal_unitarity
#print axioms kms_unitary_evolution_group_relations
#print axioms kms_modular_flow_automorphism_laws
#print axioms kms_partition_function_and_boltzmann_trace
#print axioms kms_gibbs_expectation_normalization_and_linearity
#print axioms kms_boltzmann_commutation_and_gibbs_stationarity
#print axioms kms_real_stationarity_and_tracial_zero_temperature
#print axioms kms_detailed_balance_and_hawking_period
#print axioms dephasing_kms_amplitude_and_boltzmann_weight
#print axioms dephasing_kms_lorentzian_and_matsubara
#print axioms kraus_operator_sum_linearity_and_zero
#print axioms kraus_operator_sum_cptp_structural_preservation
#print axioms kraus_identity_and_pauli_z_involutive
#print axioms kraus_dephasing_channel_formula_and_cptp
#print axioms kraus_dephasing_channel_boundary_cases
#print axioms lindblad_generator_trace_preservation
#print axioms lindblad_generator_dagger_and_hermiticity_preservation
#print axioms lindblad_generator_linearity_in_state
#print axioms lindblad_generator_no_jump_von_neumann_reduction
#print axioms lindblad_decoherence_gamma_decay_laws
#print axioms lindblad_decoherence_population_and_coherence_evolution
#print axioms lindblad_decoherence_arrow_of_time_and_classical_limit
#print axioms zurek_diagonal_projection_matrix_properties
#print axioms zurek_density_matrix_diagonal_populations
#print axioms zurek_einselection_idempotence_and_fixed_points
#print axioms zurek_einselection_populations_survive_coherences_die
#print axioms zurek_pointer_states_einselected_and_distinguishable
#print axioms open_quantum_lindblad_kms_decoherence_gns_master_bridge

end UnifiedTheory.Audit.KFCausalClockFloorOpenQuantumLindbladKMSDecoherenceGNSBridge
