/- Quantum Information, Entropy, Strong Subadditivity, Araki-Lieb, Petz Recovery,
and Clock-Floor Arbitrary-Order Yosida Graph Convergence Bridge:
1. Establishes Umegaki quantum relative entropy Hermitian trace reality,
   vanishing self-divergence, unitary and adjoint channel matrix actions, and
   Petz recovery channel idempotence and relative entropy invariance.
2. Establishes the Lindblad dephasing data processing inequality (DPI) for
   Hilbert-Schmidt distance: metric invariants, population preservation,
   coherence damping, strict contraction on coherent states, boundary regimes,
   and iterated semigroup contraction.
3. Establishes tripartite marginal consistency, Markov chain reconstruction
   normalization, KL-divergence decomposition, and Shannon strong subadditivity,
   together with the Araki-Lieb triangle inequality and diagonal product bounds.
4. Establishes Pinsker total-variation lower bounds, Alicki-Fannes-Winter
   conditional entropy continuity, the quantum Holevo chi capacity bound, and
   the Golden-Thompson trace exponential inequality.
5. Synthesizes the complete quantum information and entropy hierarchy with
   Wigner-Gleason-Bell-Tsirelson quantum foundations and arbitrary-order
   higher-power Yosida graph convergence of the time-dependent Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorQuantumFoundationsWignerGleasonBellTsirelsonBridge
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.DataProcessingInequality
import UnifiedTheory.LayerB.StrongSubadditivity
import UnifiedTheory.LayerB.ArakiLieb
import UnifiedTheory.LayerB.Pinsker
import UnifiedTheory.LayerB.PetzRecovery
import UnifiedTheory.LayerB.AlickiFannesWinter
import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.GoldenThompsonInequality

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumInformationEntropySSAArakiLiebPetzBridge
noncomputable section
open scoped Topology BigOperators
open Matrix
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open UnifiedTheory.LayerA.BornRuleUnique (QuadForm normSqForm)
open UnifiedTheory.LayerB.RobertsonSchrodinger (ComplexDensityMatrix)
open UnifiedTheory.LayerB.DensityMatrixHonest (DensityMatrix2Honest)
open UnifiedTheory.LayerB.LindbladDephasing (dephasingChannel)
open UnifiedTheory.LayerB.ClassicalEntropy (ProbabilityVector)
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
  (shannonEntropy productDistribution)
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
  (klTerm klDivergence IsAbsolutelyContinuous)
open UnifiedTheory.LayerB.OperatorEntropy (vonNeumannEntropy)
open UnifiedTheory.LayerB.DiagonalVonNeumannEntropy (vonNeumannEntropyDiagonal)
open UnifiedTheory.LayerB.FannesAudenaert (binaryEntropy faBound)
open UnifiedTheory.LayerB.LiebGoldenThompson
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.LiebCorrectedCommutingFull
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
  (trace_rho_hermitian_im_zero umegakiRelativeEntropy
   umegakiRelativeEntropy_self_eq_zero)
open UnifiedTheory.LayerB.PetzRecovery
  (unitaryChannel unitaryChannel_M unitaryAdjointChannel unitaryAdjointChannel_M
   petzRecoveryUnitary petzRecoveryUnitary_M petzRecovery_unitary_idem
   petzRecovery_unitary_property petz_equality_easy_unitary
   petz_equality_easy_from_recovery PetzEqualityHard_Unitary)
open UnifiedTheory.LayerB.DataProcessingInequality
  (hsDistance hsDistance_nonneg hsDistance_self_zero hsDistance_symm
   dephasing_p1_unchanged dephasing_p2_unchanged
   dephasing_coh_re_scaled dephasing_coh_im_scaled
   gamma_sq_le_one gamma_sq_lt_one hsDistance_after_dephasing
   dephasing_data_processing dephasing_dpi_strict_re dephasing_dpi_strict_im
   dpi_no_dephasing dpi_full_dephasing dpi_diagonal_part_preserved
   dephasing_dpi_iterated dpi_master)
open UnifiedTheory.LayerB.StrongSubadditivity
  (marginalAB marginalBC marginalB
   sum_marginalAB_eq_marginalB sum_marginalBC_eq_marginalB
   qABC qABC_nonneg qABC_sum_eq_one
   jointProductComparison joint_AC_comparison
   klDivergence_jointProductComparison_eq
   shannon_strong_subadditivity_via_KL_identity
   shannon_strong_subadditivity
   tripartite_traceA tripartite_traceC tripartite_traceAC
   tripartite_traceA_traceC tripartite_traceC_traceA)
open UnifiedTheory.LayerB.ArakiLieb
  (EntropyData araki_lieb_master productEntropyData
   productEntropyData_subadditivity araki_lieb_diagonal_product)
open UnifiedTheory.LayerB.Pinsker
  (tvDistance tvDistance_nonneg separator tvDistance_eq_separator_diff
   binaryKL log_sum_finset klDivergence_ge_binaryKL_at_separator
   BinaryPinsker pinsker_of_binaryPinsker)
open UnifiedTheory.LayerB.AlickiFannesWinter
  (conditionalEntropy conditionalEntropy_eq conditionalEntropy_swap
   conditionalEntropy_product conditionalEntropy_le_logdimA
   afwBound afw_arg_nonneg afw_arg_le_half afw_arg_le_one
   afwBound_at_zero afwBound_nonneg afwBound_mono_dim
   log_perturbation_bound binaryEntropy_le_scaled afwBound_ge_faBound
   AFW_Target Capacity_Continuity_Target afw_master afw_continuity_at_zero)
open UnifiedTheory.LayerB.HolevoBoundQuantum
  (QuantumEnsemble ensembleAverageQuantum ensembleAverageQuantum_M
   holevoChiQuantum holevoChiQuantum_def QuantumMeasurement
   QuantumRelativeEntropyMonotonicity HolevoUmegakiForm
   holevo_bound_of_monotonicity postMeasurementMutualInformation
   postMeasurementMutualInformation_le_holevoChiQuantum)
open UnifiedTheory.LayerB.GoldenThompsonInequality
  (cfc_exp_add_eq_mul_of_commute golden_thompson_commuting_le
   golden_thompson_commuting_eq
   GoldenThompson_Commuting_Target goldenThompson_commuting_target_holds
   GoldenThompson_NonCommuting_Subgate goldenThompson_nonCommuting_subgate_holds
   goldenThompson_target_from_subgate goldenThompson_target_from_commuting_and_subgate
   lieb_tracial_subgate_from_GT_nonCommuting_subgate)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence (iteratedIdentityPower)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (iteratedOperatorPower kthPowerGraphNormSq
   hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
   hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ)
open KFCausalClockFloorSMElectroweakHiggsPotentialBridge (evolutionFamily)
open KFCausalClockFloorSMFineStructureBornRuleResolventBridge
  (born_normalized_hilbert_conserved_under_evolution)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumFoundationsWignerGleasonBellTsirelsonBridge
  (quantum_foundations_born_unitary_evolution_conservation)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-! ## Section 1: Umegaki Relative Entropy and Petz Recovery -/

theorem umegaki_trace_hermitian_im_zero_and_self_zero
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ρ : ComplexDensityMatrix n) :
    (Matrix.trace (A * B)).im = 0 ∧ umegakiRelativeEntropy ρ ρ = 0 :=
  ⟨trace_rho_hermitian_im_zero hA hB, umegakiRelativeEntropy_self_eq_zero ρ⟩

theorem unitary_and_adjoint_channel_matrix_identities
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (unitaryChannel U ρ).M = U.val * ρ.M * star U.val ∧
    (unitaryAdjointChannel U ρ).M = star U.val * ρ.M * U.val :=
  ⟨unitaryChannel_M U ρ, unitaryAdjointChannel_M U ρ⟩

theorem petz_recovery_unitary_matrix_and_idempotence
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n) :
    (petzRecoveryUnitary U σ ρ).M = star U.val * ρ.M * U.val ∧
    petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ ∧
    petzRecoveryUnitary U σ (unitaryChannel U σ) = σ :=
  ⟨petzRecoveryUnitary_M U σ ρ,
   petzRecovery_unitary_idem U σ ρ,
   petzRecovery_unitary_property U σ⟩

theorem petz_unitary_relative_entropy_invariance_and_recovery
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy ρ σ =
      umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) ∧
    (petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ →
      umegakiRelativeEntropy ρ σ =
        umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ)) ∧
    (umegakiRelativeEntropy ρ σ =
        umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) →
      petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ) :=
  ⟨petz_equality_easy_unitary U ρ σ,
   petz_equality_easy_from_recovery U ρ σ,
   PetzEqualityHard_Unitary U ρ σ⟩

/-! ## Section 2: Lindblad Dephasing Data Processing Inequality -/

theorem hsDistance_metric_invariants (ρ σ : DensityMatrix2Honest) :
    0 ≤ hsDistance ρ σ ∧ hsDistance ρ ρ = 0 ∧ hsDistance ρ σ = hsDistance σ ρ :=
  ⟨hsDistance_nonneg ρ σ, hsDistance_self_zero ρ, hsDistance_symm ρ σ⟩

theorem dephasing_population_and_coherence_scaling
    (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ h0 h1 ρ).p₁ = ρ.p₁ ∧
    (dephasingChannel γ h0 h1 ρ).p₂ = ρ.p₂ ∧
    (dephasingChannel γ h0 h1 ρ).coh_re = γ * ρ.coh_re ∧
    (dephasingChannel γ h0 h1 ρ).coh_im = γ * ρ.coh_im :=
  ⟨dephasing_p1_unchanged γ h0 h1 ρ,
   dephasing_p2_unchanged γ h0 h1 ρ,
   dephasing_coh_re_scaled γ h0 h1 ρ,
   dephasing_coh_im_scaled γ h0 h1 ρ⟩

theorem dephasing_gamma_sq_bounds_and_hsDistance_expansion
    (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ σ : DensityMatrix2Honest) :
    γ ^ 2 ≤ 1 ∧
    (γ < 1 → γ ^ 2 < 1) ∧
    hsDistance (dephasingChannel γ h0 h1 ρ) (dephasingChannel γ h0 h1 σ) =
      (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2 +
      2 * γ ^ 2 * ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2) :=
  ⟨gamma_sq_le_one γ h0 h1,
   gamma_sq_lt_one γ h0,
   hsDistance_after_dephasing γ h0 h1 ρ σ⟩

theorem dephasing_data_processing_and_strict_contraction
    (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel γ h0 h1 ρ) (dephasingChannel γ h0 h1 σ) ≤ hsDistance ρ σ ∧
    (∀ hlt : γ < 1, ρ.coh_re ≠ σ.coh_re →
      hsDistance (dephasingChannel γ h0 (le_of_lt hlt) ρ)
        (dephasingChannel γ h0 (le_of_lt hlt) σ) < hsDistance ρ σ) ∧
    (∀ hlt : γ < 1, ρ.coh_im ≠ σ.coh_im →
      hsDistance (dephasingChannel γ h0 (le_of_lt hlt) ρ)
        (dephasingChannel γ h0 (le_of_lt hlt) σ) < hsDistance ρ σ) :=
  ⟨dephasing_data_processing γ h0 h1 ρ σ,
   fun hlt hne => dephasing_dpi_strict_re γ h0 hlt ρ σ hne,
   fun hlt hne => dephasing_dpi_strict_im γ h0 hlt ρ σ hne⟩

theorem dephasing_boundary_regimes_and_diagonal_preservation
    (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel 1 (by norm_num) le_rfl ρ)
      (dephasingChannel 1 (by norm_num) le_rfl σ) = hsDistance ρ σ ∧
    hsDistance (dephasingChannel 0 le_rfl (by norm_num) ρ)
      (dephasingChannel 0 le_rfl (by norm_num) σ) =
        (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2 ∧
    ((dephasingChannel γ h0 h1 ρ).p₁ - (dephasingChannel γ h0 h1 σ).p₁) ^ 2 +
      ((dephasingChannel γ h0 h1 ρ).p₂ - (dephasingChannel γ h0 h1 σ).p₂) ^ 2 =
        (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2 :=
  ⟨dpi_no_dephasing ρ σ,
   dpi_full_dephasing ρ σ,
   dpi_diagonal_part_preserved γ h0 h1 ρ σ⟩

theorem dephasing_iterated_contraction_and_dpi_master
    (γ₁ γ₂ : ℝ) (h0₁ : 0 ≤ γ₁) (h1₁ : γ₁ ≤ 1) (h0₂ : 0 ≤ γ₂) (h1₂ : γ₂ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    hsDistance
      (dephasingChannel γ₁ h0₁ h1₁ (dephasingChannel γ₂ h0₂ h1₂ ρ))
      (dephasingChannel γ₁ h0₁ h1₁ (dephasingChannel γ₂ h0₂ h1₂ σ)) ≤ hsDistance ρ σ ∧
    hsDistance (dephasingChannel γ₁ h0₁ h1₁ ρ) (dephasingChannel γ₁ h0₁ h1₁ σ) ≤ hsDistance ρ σ :=
  ⟨dephasing_dpi_iterated γ₁ γ₂ h0₁ h1₁ h0₂ h1₂ ρ σ,
   dpi_master.2.2.2.1 γ₁ h0₁ h1₁ ρ σ⟩

/-! ## Section 3: Strong Subadditivity -/

theorem tripartite_marginal_consistency_identities
    {n_A n_B n_C : ℕ}
    (P : ProbabilityVector (Fin n_A × Fin n_B × Fin n_C)) (b : Fin n_B) :
    (∑ a : Fin n_A, (marginalAB P).p (a, b)) = (marginalB P).p b ∧
    (∑ c : Fin n_C, (marginalBC P).p (b, c)) = (marginalB P).p b :=
  ⟨sum_marginalAB_eq_marginalB P b, sum_marginalBC_eq_marginalB P b⟩

theorem markov_reconstruction_qABC_nonneg_and_normalized
    {n_A n_B n_C : ℕ}
    (P : ProbabilityVector (Fin n_A × Fin n_B × Fin n_C))
    (x : Fin n_A × Fin n_B × Fin n_C) :
    0 ≤ qABC P x ∧ (∑ y : Fin n_A × Fin n_B × Fin n_C, qABC P y) = 1 ∧
    IsAbsolutelyContinuous P (jointProductComparison P) :=
  ⟨qABC_nonneg P x, qABC_sum_eq_one P, joint_AC_comparison P⟩

theorem klDivergence_jointProductComparison_and_ssa_identity
    {n_A n_B n_C : ℕ}
    (P : ProbabilityVector (Fin n_A × Fin n_B × Fin n_C)) :
    klDivergence P (jointProductComparison P) =
      shannonEntropy (marginalAB P) + shannonEntropy (marginalBC P) -
        shannonEntropy P - shannonEntropy (marginalB P) ∧
    shannonEntropy P + shannonEntropy (marginalB P) ≤
      shannonEntropy (marginalAB P) + shannonEntropy (marginalBC P) :=
  ⟨klDivergence_jointProductComparison_eq P,
   shannon_strong_subadditivity_via_KL_identity P
     (klDivergence_jointProductComparison_eq P)⟩

theorem shannon_strong_subadditivity_inequality
    {n_A n_B n_C : ℕ}
    (P : ProbabilityVector (Fin n_A × Fin n_B × Fin n_C))
    (M : Matrix (Fin n_A × Fin n_B × Fin n_C) (Fin n_A × Fin n_B × Fin n_C) ℂ) :
    shannonEntropy P + shannonEntropy (marginalB P) ≤
      shannonEntropy (marginalAB P) + shannonEntropy (marginalBC P) ∧
    (fun b b' : Fin n_B => ∑ a, (tripartite_traceC M) (a, b) (a, b')) =
      tripartite_traceAC M ∧
    (fun b b' : Fin n_B => ∑ c, (tripartite_traceA M) (b, c) (b', c)) =
      tripartite_traceAC M :=
  ⟨shannon_strong_subadditivity P,
   tripartite_traceA_traceC M,
   tripartite_traceC_traceA M⟩

/-! ## Section 4: Araki-Lieb Triangle Inequality -/

theorem araki_lieb_lower_bounds_and_abs (d : EntropyData) :
    d.SA - d.SB ≤ d.SAB ∧ d.SB - d.SA ≤ d.SAB ∧ |d.SA - d.SB| ≤ d.SAB :=
  ⟨d.arakiLieb_lower, d.arakiLieb_lower', d.arakiLieb_abs⟩

theorem araki_lieb_sandwich_and_master
    (d : EntropyData) (hsub : d.Subadditivity_Target) :
    (|d.SA - d.SB| ≤ d.SAB ∧ d.SAB ≤ d.SA + d.SB) ∧
    (|d.SA - d.SB| ≤ d.SAB ∧ d.SAB ≤ d.SA + d.SB) :=
  ⟨d.arakiLieb_sandwich hsub, araki_lieb_master d hsub⟩

theorem araki_lieb_product_subadditivity_and_diagonal_bounds
    {d_m d_n : ℕ} (P : ProbabilityVector (Fin d_m)) (Q : ProbabilityVector (Fin d_n)) :
    (productEntropyData P Q).Subadditivity_Target ∧
    (|vonNeumannEntropyDiagonal P - vonNeumannEntropyDiagonal Q| ≤
       vonNeumannEntropyDiagonal (productDistribution P Q) ∧
     vonNeumannEntropyDiagonal (productDistribution P Q) ≤
       vonNeumannEntropyDiagonal P + vonNeumannEntropyDiagonal Q) :=
  ⟨productEntropyData_subadditivity P Q, araki_lieb_diagonal_product P Q⟩

/-! ## Section 5: Pinsker Inequality -/

theorem tvDistance_nonneg_and_separator_characterization
    {α : Type*} [Fintype α] [DecidableEq α] (P Q : ProbabilityVector α) :
    0 ≤ tvDistance P Q ∧
    tvDistance P Q = (∑ x ∈ separator P Q, P.p x) - (∑ x ∈ separator P Q, Q.p x) :=
  ⟨tvDistance_nonneg P Q, tvDistance_eq_separator_diff P Q⟩

theorem log_sum_finset_and_klDivergence_ge_binaryKL
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (a b : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hb : ∀ x ∈ s, 0 ≤ b x)
    (hab : ∀ x ∈ s, a x ≠ 0 → b x ≠ 0)
    (P Q : ProbabilityVector α) (hAC : IsAbsolutelyContinuous P Q) :
    klTerm (∑ x ∈ s, a x) (∑ x ∈ s, b x) ≤ ∑ x ∈ s, klTerm (a x) (b x) ∧
    binaryKL (∑ x ∈ separator P Q, P.p x) (∑ x ∈ separator P Q, Q.p x) ≤
      klDivergence P Q :=
  ⟨log_sum_finset s a b ha hb hab,
   klDivergence_ge_binaryKL_at_separator P Q hAC⟩

theorem pinsker_from_binaryPinsker_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (hrec : BinaryPinsker) (P Q : ProbabilityVector α) (hAC : IsAbsolutelyContinuous P Q) :
    2 * tvDistance P Q ^ 2 ≤ klDivergence P Q :=
  pinsker_of_binaryPinsker hrec P Q hAC

/-! ## Section 6: Alicki-Fannes-Winter Continuity -/

theorem conditionalEntropy_identities_and_product_bound
    (SAB SA SB logdimA : ℝ)
    (hlo : -logdimA ≤ conditionalEntropy SAB SB)
    (hhi : conditionalEntropy SAB SB ≤ logdimA) :
    conditionalEntropy SAB SB = SAB - SB ∧
    conditionalEntropy SAB SB = - conditionalEntropy SB SAB ∧
    conditionalEntropy (SA + SB) SB = SA ∧
    |conditionalEntropy SAB SB| ≤ logdimA :=
  ⟨conditionalEntropy_eq SAB SB,
   conditionalEntropy_swap SAB SB,
   conditionalEntropy_product SA SB,
   conditionalEntropy_le_logdimA SAB SB logdimA hlo hhi⟩

theorem afw_argument_bounds_and_zero_evaluation
    (dA delta : ℝ) (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    0 ≤ delta / (1 + delta) ∧
    delta / (1 + delta) ≤ 1 / 2 ∧
    delta / (1 + delta) ≤ 1 ∧
    afwBound dA 0 = 0 :=
  ⟨afw_arg_nonneg delta h0,
   afw_arg_le_half delta h0 h1,
   afw_arg_le_one delta h0,
   afwBound_at_zero dA⟩

theorem afwBound_nonneg_monotone_and_dominates_faBound
    (d : ℕ) (hd : 2 ≤ d)
    {d₁ d₂ : ℝ} (h1 : 1 ≤ d₁) (h12 : d₁ ≤ d₂)
    (delta : ℝ) (h0 : 0 ≤ delta) (hle1 : delta ≤ 1) :
    0 ≤ afwBound d₁ delta ∧
    2 * delta * Real.log d₁ ≤ 2 * delta * Real.log d₂ ∧
    faBound d delta ≤ afwBound d delta :=
  ⟨afwBound_nonneg d₁ delta h1 h0 hle1,
   afwBound_mono_dim h1 h12 h0,
   afwBound_ge_faBound d delta hd h0 hle1⟩

theorem afw_perturbation_and_scaled_binaryEntropy_bounds
    (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    -(1 - T) * Real.log (1 - T) ≤ (1 + T) * Real.log (1 + T) ∧
    binaryEntropy T ≤ (1 + T) * binaryEntropy (T / (1 + T)) :=
  ⟨log_perturbation_bound T hT0 hT1, binaryEntropy_le_scaled T hT0 hT1⟩

theorem afw_master_and_zero_limit_continuity
    (hAFW : AFW_Target) (dA condGap : ℝ) (hd : 1 ≤ dA) (hgap : |condGap| ≤ 0) :
    Capacity_Continuity_Target ∧ condGap = 0 :=
  ⟨afw_master hAFW, afw_continuity_at_zero hAFW dA condGap hd hgap⟩

/-! ## Section 7: Quantum Holevo Bound -/

theorem quantum_ensemble_avgMatrix_hermitian_trace_psd
    {α : Type*} [Fintype α] {n : ℕ}
    (E : QuantumEnsemble α n) (X : Matrix (Fin n) (Fin n) ℂ) :
    E.avgMatrix.IsHermitian ∧
    E.avgMatrix.trace = 1 ∧
    0 ≤ (Matrix.trace (E.avgMatrix * X.conjTranspose * X)).re :=
  ⟨E.avgMatrix_isHermitian, E.avgMatrix_trace_eq_one, E.avgMatrix_tracePSD X⟩

theorem holevoChiQuantum_and_ensembleAverage_characterization
    {α : Type*} [Fintype α] {n : ℕ} (E : QuantumEnsemble α n) :
    (ensembleAverageQuantum E).M = ∑ a : α, (E.weight.p a : ℂ) • (E.state a).M ∧
    holevoChiQuantum E =
      vonNeumannEntropy (ensembleAverageQuantum E) -
        ∑ a : α, E.weight.p a * vonNeumannEntropy (E.state a) :=
  ⟨ensembleAverageQuantum_M E, holevoChiQuantum_def E⟩

theorem holevo_bound_and_postMeasurement_mutual_information
    {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (E : QuantumEnsemble α n) (M : QuantumMeasurement n β)
    (hform : HolevoUmegakiForm α n)
    (hmono : QuantumRelativeEntropyMonotonicity n β) :
    postMeasurementMutualInformation E M ≤ holevoChiQuantum E ∧
    postMeasurementMutualInformation E M ≤ holevoChiQuantum E :=
  ⟨holevo_bound_of_monotonicity E M hform hmono,
   postMeasurementMutualInformation_le_holevoChiQuantum E M hform hmono⟩

/-! ## Section 8: Golden-Thompson Inequality -/

theorem golden_thompson_commuting_cfc_and_trace_equality
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcomm : Commute A B) :
    cfc Real.exp (A + B) = cfc Real.exp A * cfc Real.exp B ∧
    (Matrix.trace (cfc Real.exp (A + B))).re ≤
      (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re ∧
    (Matrix.trace (cfc Real.exp (A + B))).re =
      (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re :=
  ⟨cfc_exp_add_eq_mul_of_commute A B hA hB hcomm,
   golden_thompson_commuting_le A B hA hB hcomm,
   golden_thompson_commuting_eq A B hA hB hcomm⟩

theorem golden_thompson_commuting_and_noncommuting_subgates
    (hSub : GoldenThompson_NonCommuting_Subgate)
    (hCL : CarlenLieb_Integral_Reduction_Target) :
    GoldenThompson_Commuting_Target ∧
    GoldenThompson_NonCommuting_Subgate ∧
    GoldenThompson_Target ∧
    Lieb1973_Tracial_NonCommuting_Subgate :=
  ⟨goldenThompson_commuting_target_holds,
   goldenThompson_nonCommuting_subgate_holds hSub,
   goldenThompson_target_from_subgate hSub,
   lieb_tracial_subgate_from_GT_nonCommuting_subgate hSub hCL⟩

/-! ## Section 9: Clock-Floor Arbitrary-Order Higher-Power Synthesis -/

theorem quantum_information_born_unitary_and_dephasing_dpi_synthesis
    {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : ComplexDensityMatrix n)
    (ρ₂ σ₂ : DensityMatrix2Honest) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    (qform : QuadForm) (hinv : qform.IsSO2Invariant) (s : ℝ) (f : Hilbert) :
    (qform.eval ‖evolutionFamily ε hε h hh hb m g k s t f‖ 0 = qform.a * ‖f‖ ^ 2 ∧
     normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t f‖ 0 = ‖f‖ ^ 2) ∧
    umegakiRelativeEntropy ρ σ =
      umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) ∧
    petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ ∧
    hsDistance (dephasingChannel γ h0 h1 ρ₂) (dephasingChannel γ h0 h1 σ₂) ≤
      hsDistance ρ₂ σ₂ :=
  ⟨quantum_foundations_born_unitary_evolution_conservation ε hε h hh hb m g k t qform hinv s f,
   petz_equality_easy_unitary U ρ σ,
   petzRecovery_unitary_idem U σ ρ,
   dephasing_data_processing γ h0 h1 ρ₂ σ₂⟩

theorem quantum_information_arbitraryOrder_hamiltonian_yosida_convergence
    (a : ℝ) (ha : 0 < a) (n r : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    iteratedIdentityPower (RH t a) a r x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1) ∧
    kthPowerGraphNormSq (H t) (n + 1) (iteratedIdentityPower (RH t a) a r x) ≤
      kthPowerGraphNormSq (H t) (n + 1) x ∧
    ‖iteratedOperatorPower (H t) n (iteratedIdentityPower (RH t a) a r x) -
        iteratedOperatorPower (H t) n x‖ ≤
      (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (H t) (n + 1) x‖ ∧
    Filter.Tendsto (fun j : ℕ =>
      iteratedOperatorPower (H t) n
        (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
      Filter.atTop (nhds (iteratedOperatorPower (H t) n x)) :=
  ⟨(hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
      ε hε h hh hb m g k t a ha (n + 1) r hx).1,
   (hamiltonian_arbitraryOrder_comm_and_graphNorm_contraction
      ε hε h hh hb m g k t a ha (n + 1) r hx).2.2.2,
   (hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t a ha n r hx).1,
   (hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t a ha n r hx).2⟩

theorem quantum_information_entropy_ssa_araki_lieb_petz_clock_floor_master_bridge
    {n_A n_B n_C d_m d_n : ℕ} (n_dim : ℕ)
    (U : Matrix.unitaryGroup (Fin n_dim) ℂ) (ρ σ : ComplexDensityMatrix n_dim)
    (ρ₂ σ₂ : DensityMatrix2Honest) (γ_d : ℝ) (h0 : 0 ≤ γ_d) (h1 : γ_d ≤ 1)
    (P_abc : ProbabilityVector (Fin n_A × Fin n_B × Fin n_C))
    (P_diag : ProbabilityVector (Fin d_m)) (Q_diag : ProbabilityVector (Fin d_n))
    (A B : Matrix (Fin n_dim) (Fin n_dim) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcomm : Commute A B)
    (s a : ℝ) (ha : 0 < a) (ord r : ℕ) (f : Hilbert) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (ord + 1)) :
    (umegakiRelativeEntropy ρ ρ = 0 ∧
     umegakiRelativeEntropy ρ σ =
       umegakiRelativeEntropy (unitaryChannel U ρ) (unitaryChannel U σ) ∧
     petzRecoveryUnitary U σ (unitaryChannel U ρ) = ρ) ∧
    (hsDistance (dephasingChannel γ_d h0 h1 ρ₂) (dephasingChannel γ_d h0 h1 σ₂) ≤
       hsDistance ρ₂ σ₂) ∧
    (shannonEntropy P_abc + shannonEntropy (marginalB P_abc) ≤
       shannonEntropy (marginalAB P_abc) + shannonEntropy (marginalBC P_abc)) ∧
    (|vonNeumannEntropyDiagonal P_diag - vonNeumannEntropyDiagonal Q_diag| ≤
       vonNeumannEntropyDiagonal (productDistribution P_diag Q_diag) ∧
     vonNeumannEntropyDiagonal (productDistribution P_diag Q_diag) ≤
       vonNeumannEntropyDiagonal P_diag + vonNeumannEntropyDiagonal Q_diag) ∧
    ((Matrix.trace (cfc Real.exp (A + B))).re =
       (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re) ∧
    (normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t f‖ 0 = ‖f‖ ^ 2 ∧
     ‖iteratedOperatorPower (H t) ord (iteratedIdentityPower (RH t a) a r x) -
         iteratedOperatorPower (H t) ord x‖ ≤
       (r : ℝ) * a⁻¹ * ‖iteratedOperatorPower (H t) (ord + 1) x‖ ∧
     Filter.Tendsto (fun j : ℕ =>
       iteratedOperatorPower (H t) ord
         (iteratedIdentityPower (RH t ((j : ℝ) + 1)) ((j : ℝ) + 1) r x))
       Filter.atTop (nhds (iteratedOperatorPower (H t) ord x))) :=
  ⟨⟨umegakiRelativeEntropy_self_eq_zero ρ,
    petz_equality_easy_unitary U ρ σ,
    petzRecovery_unitary_idem U σ ρ⟩,
   dephasing_data_processing γ_d h0 h1 ρ₂ σ₂,
   shannon_strong_subadditivity P_abc,
   araki_lieb_diagonal_product P_diag Q_diag,
   golden_thompson_commuting_eq A B hA hB hcomm,
   ⟨born_normalized_hilbert_conserved_under_evolution ε hε h hh hb m g k t s f,
    (hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t a ha ord r hx).1,
    (hamiltonian_arbitraryOrder_rate_and_tendsto_on_succ
      ε hε h hh hb m g k t a ha ord r hx).2⟩⟩

#print axioms umegaki_trace_hermitian_im_zero_and_self_zero
#print axioms unitary_and_adjoint_channel_matrix_identities
#print axioms petz_recovery_unitary_matrix_and_idempotence
#print axioms petz_unitary_relative_entropy_invariance_and_recovery
#print axioms hsDistance_metric_invariants
#print axioms dephasing_population_and_coherence_scaling
#print axioms dephasing_gamma_sq_bounds_and_hsDistance_expansion
#print axioms dephasing_data_processing_and_strict_contraction
#print axioms dephasing_boundary_regimes_and_diagonal_preservation
#print axioms dephasing_iterated_contraction_and_dpi_master
#print axioms tripartite_marginal_consistency_identities
#print axioms markov_reconstruction_qABC_nonneg_and_normalized
#print axioms klDivergence_jointProductComparison_and_ssa_identity
#print axioms shannon_strong_subadditivity_inequality
#print axioms araki_lieb_lower_bounds_and_abs
#print axioms araki_lieb_sandwich_and_master
#print axioms araki_lieb_product_subadditivity_and_diagonal_bounds
#print axioms tvDistance_nonneg_and_separator_characterization
#print axioms log_sum_finset_and_klDivergence_ge_binaryKL
#print axioms pinsker_from_binaryPinsker_bound
#print axioms conditionalEntropy_identities_and_product_bound
#print axioms afw_argument_bounds_and_zero_evaluation
#print axioms afwBound_nonneg_monotone_and_dominates_faBound
#print axioms afw_perturbation_and_scaled_binaryEntropy_bounds
#print axioms afw_master_and_zero_limit_continuity
#print axioms quantum_ensemble_avgMatrix_hermitian_trace_psd
#print axioms holevoChiQuantum_and_ensembleAverage_characterization
#print axioms holevo_bound_and_postMeasurement_mutual_information
#print axioms golden_thompson_commuting_cfc_and_trace_equality
#print axioms golden_thompson_commuting_and_noncommuting_subgates
#print axioms quantum_information_born_unitary_and_dephasing_dpi_synthesis
#print axioms quantum_information_arbitraryOrder_hamiltonian_yosida_convergence
#print axioms quantum_information_entropy_ssa_araki_lieb_petz_clock_floor_master_bridge

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumInformationEntropySSAArakiLiebPetzBridge
