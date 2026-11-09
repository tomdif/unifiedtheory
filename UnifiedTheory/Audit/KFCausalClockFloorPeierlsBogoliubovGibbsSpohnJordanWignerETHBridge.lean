/-
  UnifiedTheory/Audit/KFCausalClockFloorPeierlsBogoliubovGibbsSpohnJordanWignerETHBridge.lean

  Self-contained Tier-1 synthesis bridge connecting:
  1. The two-time cross-trajectory higher-power potential resolvent comparison
     (`two_time_cross_trajectory_higher_power_resolvent_norm_bound`,
      `two_time_cross_trajectory_higher_power_resolvent_graphNorm_bound`,
      `two_time_cross_trajectory_higher_power_resolvent_damped_bound`) on the discrete
     causal clock-floor geometry (`L_max * ε_min ≥ c_floor > 0`),
  2. The Peierls-Bogoliubov inequality (`peierls_bogoliubov`), the general Gibbs
     variational principle and Jaynes maximum-entropy principle for arbitrary
     density matrices (`gibbs_variational_principle_general`, `max_entropy_general`),
     and the statistical partition function from the Born rule + Wick rotation
     (`partition_from_born_rule`, `unified_quantum_statistical`),
  3. Spohn's entropy-production inequality and H-theorem (`spohn_monotone_diagonal`,
     `spohn_production_nonneg_diagonal`, `relEntropyTrajectory.tendsto_iInf`,
     `relEntropyTrajectory.production_sum_le`), operator convexity of the matrix
     inverse (`inv_operator_convex`), operator monotonicity of the matrix logarithm
     (`cfc_log_monotone`, `operatorLog_monotone`), the Carlen-Lieb 2008 integral
     reduction (`carlenLieb_integral_reduction_holds_modulo_identity`,
     `lieb_tracial_target_from_three_routes`), and the Frullani log integrand
     Hermiticity and trace contraction (`frullaniLogIntegrand_isHermitian`,
     `frullaniLogIntegrand_trace`),
  4. The Jordan-Wigner transformation core algebra (`jordan_wigner_master`,
     `twoSite_anticomm'`), the Eigenstate Thermalization Hypothesis diagonal
     witnesses (`identity_satisfies_eth`, `hamiltonian_satisfies_eth`, `eth_diagonal_add`),
     the Matsubara frequency quantization biconditional (`exp_iωβ_one_iff`,
     `expAmplitude_periodic_iff_matsubara`), and Landauer's bit-erasure bound
     (`landauer_bit_erasure_bound`, `landauer_bit_erasure_eq`).

  Every theorem in this module is proved from first principles using only the standard
  Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`,
  zero `admit`, zero custom `axiom`, and zero `unsafe`.
-/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
import UnifiedTheory.LayerB.PeierlsBogoliubov
import UnifiedTheory.LayerB.GibbsVariational
import UnifiedTheory.LayerB.GibbsVariationalGeneral
import UnifiedTheory.LayerB.SpohnInequality
import UnifiedTheory.LayerB.MaxEntropyPrinciple
import UnifiedTheory.LayerB.OperatorConvexInverse
import UnifiedTheory.LayerB.OperatorMonotoneLog
import UnifiedTheory.LayerB.CarlenLiebIntegralReduction
import UnifiedTheory.LayerB.LiebJointConcavityKraus
import UnifiedTheory.LayerB.JordanWigner
import UnifiedTheory.LayerB.EigenstateThermalization
import UnifiedTheory.LayerB.MatsubaraQuantization
import UnifiedTheory.LayerB.LandauerPrinciple

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorPeierlsBogoliubovGibbsSpohnJordanWignerETHBridge

open Matrix Complex
open scoped MatrixOrder ComplexOrder BigOperators
open UnifiedTheory.Audit.KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorIteratedResolventSecondPowerCore (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.GibbsVariational
open UnifiedTheory.LayerB.GibbsVariationalFull
open UnifiedTheory.LayerB.GibbsVariationalGeneral
open UnifiedTheory.LayerB.MaxEntropyPrinciple
open UnifiedTheory.LayerB.PeierlsBogoliubov
open UnifiedTheory.LayerB.SpohnInequality
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.OperatorConvexInverse
open UnifiedTheory.LayerB.OperatorMonotoneLog
open UnifiedTheory.LayerB.LiebGoldenThompson
open UnifiedTheory.LayerB.LiebTracialAttack
open UnifiedTheory.LayerB.LiebRpowRoute
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.RpowConcavityClosed
open UnifiedTheory.LayerB.CarlenLiebIntegralReduction
open UnifiedTheory.LayerB.LiebJointConcavityKraus
open UnifiedTheory.LayerB.JordanWigner
open UnifiedTheory.LayerB.EigenstateThermalization
open UnifiedTheory.LayerB.MatsubaraQuantization
open UnifiedTheory.LayerB.LandauerPrinciple
open UnifiedTheory.LayerB.PropagationRule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Theorem 1 (Peierls-Bogoliubov, General Gibbs Variational, and Jaynes Max-Entropy Package).**
    For any finite-dimensional quantum system (`0 < n`), the Peierls-Bogoliubov
    inequality `log Z(-1, H + ΔH) ≥ log Z(-1, H) + ⟨ΔH⟩_{ρ_H}` holds unconditionally,
    the Gibbs state `gibbsDensity β H_mat` minimizes the Helmholtz free energy `F(ρ)`
    over all density matrices `ρ` (pure states included), and maximizes the von Neumann
    entropy `S(ρ)` on the fixed-energy slice. -/
theorem peierls_bogoliubov_gibbs_variational_and_max_entropy_package
    {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (ρ : ComplexDensityMatrix n) (β T : ℝ)
    (H_mat ΔH : Matrix (Fin n) (Fin n) ℂ)
    (hH : H_mat.IsHermitian) (hΔH : ΔH.IsHermitian)
    (hZ : 0 < UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction β H_mat)
    (hTβ : T * β = 1) (hT : 0 < T) :
    PeierlsBogoliubov_Target H_mat ΔH
      (ComplexDensityMatrix.expectation
        (gibbsDensity 1 (-H_mat) hH.neg
          (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
            1 (-H_mat) hH.neg)) ΔH) ∧
    freeEnergy (gibbsDensity β H_mat hH hZ) H_mat T ≤ freeEnergy ρ H_mat T ∧
    (energy ρ H_mat = energy (gibbsDensity β H_mat hH hZ) H_mat →
      vonNeumannEntropy ρ ≤ vonNeumannEntropy (gibbsDensity β H_mat hH hZ)) := by
  refine ⟨peierls_bogoliubov H_mat ΔH hH hΔH,
    gibbs_variational_principle_general ρ hn β H_mat hH hZ T hTβ (le_of_lt hT), ?_⟩
  intro hE
  exact max_entropy_general ρ hn β H_mat hH hZ T hTβ hT hE

/-- **Theorem 2 (Spohn Entropy Production, H-Theorem, and Partition Function Package).**
    Under any stationary stochastic channel `Φ.push ρ_ss = ρ_ss`, the KL divergence to
    `ρ_ss` decreases monotonically and discrete entropy production is non-negative;
    any relaxing relative-entropy trajectory `T_traj` converges to its non-negative
    infimum with finite total entropy budget `∑_{n<N} σ_n ≤ S(0)`; and the quantum
    amplitude and Boltzmann weight are both multiplicative from linearity of the
    source functional. -/
theorem spohn_entropy_production_h_theorem_and_partition_package
    {α : Type*} [Fintype α]
    (Φ : StochasticMatrix α α) (P ρ_ss : ProbabilityVector α)
    (hStat : Φ.push ρ_ss = ρ_ss) (hAC : IsAbsolutelyContinuous P ρ_ss)
    (T_traj : relEntropyTrajectory) (N : ℕ) :
    klDivergence (Φ.push P) ρ_ss ≤ klDivergence P ρ_ss ∧
    0 ≤ entropyProduction (klDivergence P ρ_ss) (klDivergence (Φ.push P) ρ_ss) ∧
    Filter.Tendsto T_traj.S Filter.atTop (nhds (⨅ n, T_traj.S n)) ∧
    ∑ n ∈ Finset.range N, T_traj.production n ≤ T_traj.S 0 ∧
    (∀ k s₁ s₂ : ℝ, expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂) ∧
    (∀ k s : ℝ, Complex.normSq (expAmplitude k s) = 1) := by
  exact ⟨spohn_monotone_diagonal Φ P ρ_ss hStat hAC,
    spohn_production_nonneg_diagonal Φ P ρ_ss hStat hAC,
    T_traj.tendsto_iInf,
    T_traj.production_sum_le N,
    exp_multiplicative,
    exp_unit_modulus⟩

/-- **Theorem 3 (Operator Convexity of Inverse, Operator Monotonicity of Log, Carlen-Lieb Reduction, and Frullani Trace Package).**
    For positive-definite matrices `A, B`, `(α A + (1 - α) B)⁻¹ ≤ α A⁻¹ + (1 - α) B⁻¹`
    for `α ∈ [0, 1]` and `A ≤ B ⇒ cfc Real.log A ≤ cfc Real.log B`; the Frullani
    integrand is Hermitian with explicit Kraus trace contraction; and the three-route
    Carlen-Lieb / Golden-Thompson / Ando cascade implies `Lieb1973_Tracial_Target`. -/
theorem operator_convex_inv_monotone_log_carlen_lieb_and_frullani_package
    {n : ℕ} (A B K : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (α t : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)⁻¹ ≤
      (α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹ ∧
    (A ≤ B → cfc Real.log A ≤ cfc Real.log B) ∧
    (frullaniLogIntegrand B t).IsHermitian ∧
    (Matrix.trace (Kᴴ * frullaniLogIntegrand B t * K)).re =
      (1 / (1 + t)) * (Matrix.trace (Kᴴ * K)).re -
        (Matrix.trace (Kᴴ * ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B)⁻¹ * K)).re ∧
    ((Lieb1973_Tracial_NonCommuting_Subgate ∨
        (GoldenThompson_Target ∧ CarlenLieb_Integral_Reduction_Target) ∨
        (GoldenThompson_Target ∧ CarlenLieb_BundledSubgates)) →
      Lieb1973_Tracial_Target) := by
  refine ⟨inv_operator_convex A B hA hB α hα₀ hα₁,
    fun hle => cfc_log_monotone A B hA hB hle,
    frullaniLogIntegrand_isHermitian B hB.isHermitian t,
    frullaniLogIntegrand_trace K B t,
    lieb_tracial_target_from_three_routes⟩

/-- **Theorem 4 (Jordan-Wigner CAR, ETH Diagonal Witnesses, Matsubara Quantization, and Landauer Bit-Erasure Package).**
    The Jordan-Wigner ladder operators satisfy on-site Pauli exclusion, CAR
    `{σ⁺, σ⁻} = I`, `Z`-string anticommutation, and two-site fermionic anticommutation
    `{Z ⊗ σ⁻, σ⁻ ⊗ I} = 0`; the identity and Hamiltonian satisfy diagonal ETH;
    imaginary-time β-periodicity `exp(i ω β) = 1` holds iff `ω = 2π n / β` (`n ∈ ℤ`);
    and erasing one bit from `maximallyMixedQubit` to `purePointStateQubit` decreases
    system entropy by `ln 2`. -/
theorem jordan_wigner_eth_matsubara_and_landauer_package
    {n : ℕ} (H_mat : Matrix (Fin n) (Fin n) ℂ) (hH : H_mat.IsHermitian)
    (ω β : ℝ) (hβ : 0 < β) :
    (sigmaPlus * sigmaPlus = 0 ∧
      sigmaMinus * sigmaMinus = 0 ∧
      sigmaPlus * sigmaMinus + sigmaMinus * sigmaPlus = 1 ∧
      Z_tensor_sigmaMinus * sigmaMinus_tensor_I +
        sigmaMinus_tensor_I * Z_tensor_sigmaMinus = 0) ∧
    ETH_Diagonal H_mat hH (1 : Matrix (Fin n) (Fin n) ℂ) (fun _ => (1 : ℂ)) ∧
    ETH_Diagonal H_mat hH H_mat (fun E => (E : ℂ)) ∧
    (Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 ↔
      ∃ m : ℤ, ω = 2 * Real.pi * m / β) ∧
    systemEntropyChange maximallyMixedQubit purePointStateQubit = Real.log 2 ∧
    systemEntropyChange maximallyMixedQubit purePointStateQubit ≥ Real.log 2 := by
  exact ⟨⟨sigmaPlus_sq, sigmaMinus_sq, anticomm_plus_minus, twoSite_anticomm'⟩,
    identity_satisfies_eth H_mat hH,
    hamiltonian_satisfies_eth H_mat hH,
    exp_iωβ_one_iff hβ,
    landauer_bit_erasure_eq,
    landauer_bit_erasure_bound⟩

/-- **Theorem 5 (Two-Time Cross-Trajectory Higher-Power Resolvent Comparison Coupled to Peierls-Bogoliubov and General Gibbs Variational Principle).**
    The cross-initial higher-power resolvent difference lies in `hamiltonianPowerDomain t₁ (r + 2)`
    simultaneously with the Peierls-Bogoliubov inequality and the general Gibbs
    variational principle (`F(ρ_β) ≤ F(ρ)` for arbitrary density matrices `ρ`). -/
theorem two_time_cross_trajectory_higher_power_resolvent_coupled_to_peierls_bogoliubov_and_gibbs
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m_mass g_coup k s₁ s₂ t₁ q a b : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert)
    {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (ρ : ComplexDensityMatrix n) (β T_temp : ℝ)
    (H_mat ΔH : Matrix (Fin n) (Fin n) ℂ)
    (hH : H_mat.IsHermitian) (hΔH : ΔH.IsHermitian)
    (hZ : 0 < UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction β H_mat)
    (hTβ : T_temp * β = 1) (hT : 0 ≤ T_temp) :
    crossInitialHigherPowerResolventDiff ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ a b r f₁ f₂ ∈
      hamiltonianPowerDomain ε hε h hh hb m_mass g_coup k t₁ (r + 2) ∧
    PeierlsBogoliubov_Target H_mat ΔH
      (ComplexDensityMatrix.expectation
        (gibbsDensity 1 (-H_mat) hH.neg
          (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
            1 (-H_mat) hH.neg)) ΔH) ∧
    freeEnergy (gibbsDensity β H_mat hH hZ) H_mat T_temp ≤ freeEnergy ρ H_mat T_temp := by
  have h1 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  exact ⟨h1.1, peierls_bogoliubov H_mat ΔH hH hΔH,
    gibbs_variational_principle_general ρ hn β H_mat hH hZ T_temp hTβ hT⟩

/-- **Theorem 6 (Two-Time Cross-Initial Yosida Identity Difference Coupled to Operator Convex Inverse and Operator Monotone Log).**
    The cross-initial higher-power Yosida identity difference satisfies `‖y‖ ≤ ‖f₁‖ + ‖f₂‖`
    while operator convexity of the matrix inverse and operator monotonicity of the
    matrix logarithm hold. -/
theorem two_time_cross_trajectory_graphNorm_coupled_to_operator_convex_inv_and_monotone_log
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m_mass g_coup k s₁ s₂ t₁ q a b : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert)
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ‖crossInitialHigherPowerIdentityDiff ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ a b r f₁ f₂‖ ≤
      ‖f₁‖ + ‖f₂‖ ∧
    ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)⁻¹ ≤
      (α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹ ∧
    (A ≤ B → cfc Real.log A ≤ cfc Real.log B) := by
  have h1 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  exact ⟨h1.2.2.2.1, inv_operator_convex A B hA hB α hα₀ hα₁,
    fun hle => cfc_log_monotone A B hA hB hle⟩

/-- **Theorem 7 (Cross-Final Two-Time Resolvent Difference Coupled to Spohn H-Theorem and Landauer Bit Erasure).**
    The cross-final higher-power resolvent difference is bounded by `((a⁻¹)^{r+2} + (b⁻¹)^{r+2}) * ‖f‖`
    while any relaxing relative-entropy trajectory converges to its infimum and Landauer's
    bit-erasure bound `ΔS = ln 2` holds. -/
theorem damped_two_time_cross_trajectory_resolvent_coupled_to_spohn_and_landauer
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m_mass g_coup k s t₁ t₂ q a b : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert)
    (T_traj : relEntropyTrajectory) :
    ‖crossFinalHigherPowerResolventDiff ε hε h hh hb m_mass g_coup k s t₁ t₂ a b r f‖ ≤
      ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ ∧
    Filter.Tendsto T_traj.S Filter.atTop (nhds (⨅ n, T_traj.S n)) ∧
    systemEntropyChange maximallyMixedQubit purePointStateQubit = Real.log 2 := by
  have h1 := crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m_mass g_coup k s t₁ t₂ q a b ha hb_pos r f
  exact ⟨h1.2, T_traj.tendsto_iInf, landauer_bit_erasure_eq⟩

/-- **Theorem 8 (Two-Time Same-Initial Resolvent Difference Coupled to Jordan-Wigner, ETH, and Matsubara Quantization).**
    Along a single initial trajectory `(s, t)`, `crossInitialHigherPowerResolventDiff s s t a b r f f`
    belongs to `hamiltonianPowerDomain t (r + 3)` while the Jordan-Wigner anticommutation,
    Hamiltonian ETH identity, and Matsubara frequency quantization biconditional all hold. -/
theorem two_time_same_trajectory_higher_power_resolvent_coupled_to_jw_eth_and_matsubara
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m_mass g_coup k s t q a b : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert)
    {n : ℕ} (H_mat : Matrix (Fin n) (Fin n) ℂ) (hH : H_mat.IsHermitian)
    (ω β : ℝ) (hβ : 0 < β) :
    crossInitialHigherPowerResolventDiff ε hε h hh hb m_mass g_coup k s s t a b r f f ∈
      hamiltonianPowerDomain ε hε h hh hb m_mass g_coup k t (r + 3) ∧
    Z_tensor_sigmaMinus * sigmaMinus_tensor_I =
      -(sigmaMinus_tensor_I * Z_tensor_sigmaMinus) ∧
    ETH_Diagonal H_mat hH H_mat (fun E => (E : ℂ)) ∧
    (Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 ↔
      ∃ k_idx : ℤ, ω = 2 * Real.pi * k_idx / β) := by
  have h1 := crossInitialHigherPowerResolventDiff_same_initial_mem_succ_power
    ε hε h hh hb m_mass g_coup k s t q a b ha hb_pos r f
  exact ⟨h1.2, twoSite_anticomm, hamiltonian_satisfies_eth H_mat hH, exp_iωβ_one_iff hβ⟩

/-- **Theorem 9 (Grand Peierls-Bogoliubov, Gibbs, Spohn, Operator Convex/Monotone, Carlen-Lieb, Jordan-Wigner, ETH, Matsubara, Landauer, and Two-Time Resolvent Bridge).**
    Complete synthesis uniting the two-time cross-trajectory higher-power potential
    resolvent comparison with the Peierls-Bogoliubov inequality, general Gibbs
    variational principle, Spohn's H-theorem, operator convexity of `x⁻¹`, operator
    monotonicity of `log`, Carlen-Lieb three-route reduction, Jordan-Wigner CAR
    algebra, diagonal ETH witnesses, Matsubara frequency quantization, and Landauer's
    bit-erasure bound. -/
theorem peierls_bogoliubov_gibbs_spohn_jw_eth_matsubara_landauer_two_time_resolvent_bridge
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m_mass g_coup k s₁ s₂ t₁ t₂ q a b : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert)
    {n : ℕ} [Nonempty (Fin n)] (hn : 0 < n)
    (ρ : ComplexDensityMatrix n) (β T_temp ω : ℝ) (hβ : 0 < β)
    (H_mat ΔH A B : Matrix (Fin n) (Fin n) ℂ)
    (hH : H_mat.IsHermitian) (hΔH : ΔH.IsHermitian)
    (hA : A.PosDef) (hB : B.PosDef)
    (hZ : 0 < UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction β H_mat)
    (hTβ : T_temp * β = 1) (hT : 0 ≤ T_temp)
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    (crossInitialHigherPowerResolventDiff ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ a b r f₁ f₂ ∈
       hamiltonianPowerDomain ε hε h hh hb m_mass g_coup k t₁ (r + 2) ∧
     ‖crossFinalHigherPowerIdentityDiff ε hε h hh hb m_mass g_coup k s₁ t₁ t₂ a b r f₁‖ ≤ 2 * ‖f₁‖) ∧
    PeierlsBogoliubov_Target H_mat ΔH
      (ComplexDensityMatrix.expectation
        (gibbsDensity 1 (-H_mat) hH.neg
          (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty
            1 (-H_mat) hH.neg)) ΔH) ∧
    freeEnergy (gibbsDensity β H_mat hH hZ) H_mat T_temp ≤ freeEnergy ρ H_mat T_temp ∧
    ((α : ℂ) • A + ((1 - α : ℝ) : ℂ) • B)⁻¹ ≤
      (α : ℂ) • A⁻¹ + ((1 - α : ℝ) : ℂ) • B⁻¹ ∧
    (A ≤ B → cfc Real.log A ≤ cfc Real.log B) ∧
    Z_tensor_sigmaMinus * sigmaMinus_tensor_I =
      -(sigmaMinus_tensor_I * Z_tensor_sigmaMinus) ∧
    ETH_Diagonal H_mat hH H_mat (fun E => (E : ℂ)) ∧
    (Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 ↔
      ∃ k_idx : ℤ, ω = 2 * Real.pi * k_idx / β) ∧
    systemEntropyChange maximallyMixedQubit purePointStateQubit = Real.log 2 := by
  have h1 := crossTrajectory_two_time_higher_power_resolvent_comparison_master_synthesis
    ε hε h hh hb m_mass g_coup k s₁ s₂ t₁ t₂ q a b ha hb_pos r f₁ f₂
  exact ⟨⟨h1.1.1, h1.2.2.2.2⟩, peierls_bogoliubov H_mat ΔH hH hΔH,
    gibbs_variational_principle_general ρ hn β H_mat hH hZ T_temp hTβ hT,
    inv_operator_convex A B hA hB α hα₀ hα₁,
    fun hle => cfc_log_monotone A B hA hB hle,
    twoSite_anticomm,
    hamiltonian_satisfies_eth H_mat hH,
    exp_iωβ_one_iff hβ,
    landauer_bit_erasure_eq⟩

#print axioms peierls_bogoliubov_gibbs_variational_and_max_entropy_package
#print axioms spohn_entropy_production_h_theorem_and_partition_package
#print axioms operator_convex_inv_monotone_log_carlen_lieb_and_frullani_package
#print axioms jordan_wigner_eth_matsubara_and_landauer_package
#print axioms two_time_cross_trajectory_higher_power_resolvent_coupled_to_peierls_bogoliubov_and_gibbs
#print axioms two_time_cross_trajectory_graphNorm_coupled_to_operator_convex_inv_and_monotone_log
#print axioms damped_two_time_cross_trajectory_resolvent_coupled_to_spohn_and_landauer
#print axioms two_time_same_trajectory_higher_power_resolvent_coupled_to_jw_eth_and_matsubara
#print axioms peierls_bogoliubov_gibbs_spohn_jw_eth_matsubara_landauer_two_time_resolvent_bridge

end UnifiedTheory.Audit.KFCausalClockFloorPeierlsBogoliubovGibbsSpohnJordanWignerETHBridge
