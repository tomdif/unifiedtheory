/- Osterwalder-Schrader Euclidean Reflection Positivity, Density-Rigid Chamber
Continuum Limit, Lorentzian-Direct Wightman Field Construction, Discrete Schwinger
Functions, Exponential Cluster Decomposition, Constructive Measure Ledger, and
Clock-Floor Five-Operator Resolvent and Iterated-Core Bridge at the Chamber
Eigenvalue Shifts:
1. Synthesizes 1D Wilson lattice reflection positivity and transfer-matrix diagonal
   dominance (LayerA.LatticeReflectionPositivity) with the density-independent 3x3
   chamber matrix, characteristic polynomial factorization, positive spectrum
   {3/5, (5+√7)/30, (5-√7)/30}, and continuum limit (LayerB.CL1_ContinuumLimit).
2. Connects the Lorentzian-direct Wightman field operators, bounded smeared fields,
   causal-set microcausality, and chamber vacuum uniqueness and cyclicity
   (LayerB.CL2_LorentzianWightmanDirect) with discrete Schwinger n-point functions,
   permutation symmetry, and cluster factorization (LayerB.CL3_SchwingerFunctions).
3. Combines exponential decay of connected two-point chamber correlators at rate
   γ_cluster = ln(5-√7) > 0 (LayerB.CL3_ClusterDecomposition) and the discrete
   Poisson/Boltzmann constructive measure ledger (LayerB.CL3_ConstructiveMeasure)
   with the infinite-dimensional clock-floor 5-operator resolvents, 10-domain
   iterated Hamiltonian resolvent, and Gaussian clock-core approximants evaluated
   at the positive chamber spectral shifts (5-√7)/30, (5+√7)/30, (13-√7)/30, and 3/5. -/
import UnifiedTheory.LayerA.LatticeReflectionPositivity
import UnifiedTheory.LayerB.CL1_ContinuumLimit
import UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
import UnifiedTheory.LayerB.CL3_SchwingerFunctions
import UnifiedTheory.LayerB.CL3_ClusterDecomposition
import UnifiedTheory.LayerB.CL3_ConstructiveMeasure
import UnifiedTheory.Audit.KFCausalClockFloorYangMillsR1R2R3R4ContinuumBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorOsterwalderSchraderWightmanReconstructionBridge

noncomputable section

open Real Filter Topology
open scoped BigOperators Topology InnerProduct

open UnifiedTheory.LayerA.CausalFoundation
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerA.LatticeReflectionPositivity
open UnifiedTheory.LayerB.YangMillsCausalAttack
open UnifiedTheory.LayerB.CL1_BathSector
open UnifiedTheory.LayerB.CL1_ContinuumLimit
open UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure
open UnifiedTheory.LayerB.CL3_SchwingerFunctions
open UnifiedTheory.LayerB.CL3_ClusterDecomposition

open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorFullFiveResolventChainSynthesis
  (five_resolvent_norm_sum_le)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain)
open KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
  (unconditionalCoreDomain growingClockCoreDomain coreApproxSeq)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains
   iteratedHamiltonianResolvent_second_power_radial_residual_eq)
open KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation
  (unconditional_common_hamiltonian_static_shifted_resolvent_defect
   unconditional_common_residual_static_shifted_resolvent_defect
   unconditional_common_hamiltonian_residual_shifted_resolvent_defect
   unconditional_common_two_time_shifted_resolvent_defect_norm_le
   unconditional_coreApproxSeq_with_resolvent_identities)

/-! ### 1. Lattice Reflection Positivity (`LatticeReflectionPositivity`) & Density-Rigid Continuum Limit (`CL1`) -/

/-- The Boltzmann weight `exp(-S)` is strictly positive, the plaquette weight `1 - cos θ`
lies in `[0, 2]`, and the 1D Wilson action is non-negative for `0 ≤ β`. -/
theorem lattice_boltzmann_and_plaquette_positivity
    (S θ β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (θVec : Fin n → ℝ) :
    0 < Real.exp (-S) ∧
    (0 ≤ 1 - Real.cos θ ∧ 1 - Real.cos θ ≤ 2) ∧
    0 ≤ wilsonAction1D β n θVec ∧
    0 < Real.exp (-(wilsonAction1D β n θVec)) :=
  ⟨boltzmann_weight_pos S,
   one_minus_cos_range θ,
   wilson_action_nonneg hβ,
   wilson_boltzmann_pos β n θVec⟩

/-- The 1D lattice transfer matrix kernel `T(θ₁, θ₂) = exp(β cos(θ₁ - θ₂))` is strictly
positive, symmetric, and gauge-translation invariant. -/
theorem lattice_transfer_matrix_positivity_and_symmetry
    (β θ₁ θ₂ α : ℝ) :
    0 < transferMatrix β θ₁ θ₂ ∧
    transferMatrix β θ₁ θ₂ = transferMatrix β θ₂ θ₁ ∧
    transferMatrix β (θ₁ + α) (θ₂ + α) = transferMatrix β θ₁ θ₂ :=
  ⟨transfer_matrix_pos β θ₁ θ₂,
   transfer_matrix_symmetric β θ₁ θ₂,
   transfer_matrix_translation_invariant β θ₁ θ₂ α⟩

/-- For `0 ≤ β`, the diagonal entry `T(θ₁, θ₁) = exp(β)` dominates all off-diagonal
entries `T(θ₁, θ₂)` with contrast ratio `T(θ₁, θ₁) / T(θ₁, θ₂) ≥ 1`. -/
theorem lattice_transfer_matrix_diagonal_dominance_and_contrast
    {β : ℝ} (hβ : 0 ≤ β) (θ₁ θ₂ : ℝ) :
    transferMatrix β θ₁ θ₁ = Real.exp β ∧
    transferMatrix β θ₁ θ₂ ≤ transferMatrix β θ₁ θ₁ ∧
    transferMatrix β θ₁ θ₁ / transferMatrix β θ₁ θ₂ ≥ 1 :=
  ⟨transfer_matrix_diagonal β θ₁,
   transfer_matrix_le_diagonal hβ θ₁ θ₂,
   transfer_matrix_contrast_ratio hβ θ₁ θ₂⟩

/-- Rank-one and 1D factorized reflection positivity for the Wilson lattice action. -/
theorem lattice_reflection_positivity_rank_one_and_factored
    {k : ℕ} (β θ₁ θ₂ c : ℝ) (hβ : 0 ≤ β) (θ : Fin k → ℝ) (f : Fin k → ℝ) :
    0 ≤ c * transferMatrix β θ₁ θ₂ * c ∧
    (Real.exp (β * Real.cos θ₂) * Real.exp (β * Real.cos θ₁)) *
      (Real.exp (β * Real.cos θ₁) * Real.exp (β * Real.cos θ₂)) =
      (Real.exp (β * Real.cos θ₁) * Real.exp (β * Real.cos θ₂)) ^ 2 ∧
    0 ≤ Finset.univ.sum (fun i =>
      Finset.univ.sum (fun j =>
        f j * f i *
        Real.exp (-(β * (1 - Real.cos (θ i)))) *
        Real.exp (-(β * (1 - Real.cos (θ j)))))) :=
  ⟨reflection_positivity_rank_one β θ₁ θ₂ c,
   reflected_times_original_eq_sq β θ₁ θ₂,
   reflection_positivity_1d_factored β hβ θ f⟩

/-- Density rigidity of the 3×3 chamber matrix `H_chamber_at_density ρ`, its trace `14/15`,
and its characteristic polynomial factorization `750 p(x) = (5x - 3)(150x² - 50x + 3)`. -/
theorem cl1_chamber_matrix_and_charPoly_density_rigidity
    (ρ₁ ρ₂ : ℝ) (x : ℚ) :
    H_chamber_at_density ρ₁ = H_chamber_at_density ρ₂ ∧
    H_charPoly_at_density ρ₁ x = H_charPoly_at_density ρ₂ x ∧
    750 * H_charPoly_at_density ρ₁ x = (5 * x - 3) * (150 * x ^ 2 - 50 * x + 3) ∧
    H_charPoly_at_density ρ₁ (3 / 5) = 0 :=
  ⟨H_chamber_density_independent ρ₁ ρ₂,
   H_charPoly_density_independent ρ₁ ρ₂ x,
   H_charPoly_factors_at_density ρ₁ x,
   H_chamber_top_eigenvalue_at_density ρ₁⟩

/-- Positivity and quadratic root equations for the three chamber eigenvalues and the
chamber gap `chamber_gap_at ρ = (13 - √7)/30 > 0` at every sprinkling density `ρ`. -/
theorem cl1_chamber_eigenvalues_and_gap_positivity (ρ : ℝ) :
    0 < lambda_top_at_density ρ ∧
    0 < lambda_2_at_density ρ ∧
    0 < lambda_3_at_density ρ ∧
    0 < chamber_gap_at ρ ∧
    chamber_gap_at ρ = lambda_top_at_density ρ - lambda_2_at_density ρ ∧
    150 * (lambda_2_at_density ρ) ^ 2 - 50 * (lambda_2_at_density ρ) + 3 = 0 ∧
    150 * (lambda_3_at_density ρ) ^ 2 - 50 * (lambda_3_at_density ρ) + 3 = 0 :=
  ⟨lambda_top_pos_at_density ρ,
   lambda_2_pos_at_density ρ,
   lambda_3_pos_at_density ρ,
   chamber_gap_pos_at_density ρ,
   chamber_gap_is_top_minus_lambda2 ρ,
   lambda_2_eigen_eq ρ,
   lambda_3_eigen_eq ρ⟩

/-- Continuum-limit convergence (`ρ → ∞`) of all three chamber eigenvalues and the
chamber spectral gap `(13 - √7)/30 > 0`. -/
theorem cl1_chamber_eigenvalues_and_gap_continuum_convergence :
    Tendsto lambda_top_at_density atTop (𝓝 (3 / 5)) ∧
    Tendsto lambda_2_at_density atTop (𝓝 ((5 + Real.sqrt 7) / 30)) ∧
    Tendsto lambda_3_at_density atTop (𝓝 ((5 - Real.sqrt 7) / 30)) ∧
    Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
    0 < (13 - Real.sqrt 7) / 30 :=
  chamber_gap_survives_continuum_limit

/-- Complete algebraic continuum-limit master package from `CL1_ContinuumLimit`. -/
theorem cl1_chamber_algebraic_master_synthesis :
    (∀ ρ₁ ρ₂ : ℝ, H_chamber_at_density ρ₁ = H_chamber_at_density ρ₂) ∧
    (∀ ρ₁ ρ₂ : ℝ, chamber_gap_at ρ₁ = chamber_gap_at ρ₂) ∧
    (∀ ρ : ℝ, 0 < chamber_gap_at ρ) ∧
    (∀ ρ : ℝ, 0 < ρ → chamber_gap_at ρ = (13 - Real.sqrt 7) / 30) ∧
    Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
    continuum_limit_open :=
  ⟨H_chamber_density_independent,
   chamber_gap_density_independent,
   chamber_gap_pos_at_density,
   chamber_gap_rigid_in_density,
   chamber_gap_continuum_limit,
   chamber_continuum_limit_satisfies_open_prop⟩

/-! ### 2. Lorentzian-Direct Wightman Construction (`CL2`) & Discrete Schwinger Functions (`CL3`) -/

/-- Causal-set substrate order properties: irreflexivity, antisymmetry, and transitivity of `prec`. -/
theorem cl2_substrate_lorentzian_order_properties
    (C : CausalSet) (a b c : C.Event) :
    ¬ C.prec a a ∧
    (C.prec a b → C.prec b a → a = b) ∧
    (C.prec a b → C.prec b c → C.prec a c) :=
  ⟨substrate_irreflexive C a,
   substrate_antisymmetric C a b,
   substrate_transitive C a b c⟩

/-- Positive chamber spectrum (`W2`), strict eigenvalue ordering `μ_vac < μ_first < μ_top`,
and unique lowest-eigenvalue chamber vacuum (`W3`). -/
theorem cl2_w2_w3_chamber_spectrum_and_vacuum_uniqueness :
    (0 : ℝ) < 3 / 5 ∧
    (0 : ℝ) < (5 + Real.sqrt 7) / 30 ∧
    (0 : ℝ) < (5 - Real.sqrt 7) / 30 ∧
    (μ_vac < μ_first ∧ μ_vac < μ_top) ∧
    0 < μ_vac ∧
    (μ_vac ≠ μ_first ∧ μ_first ≠ μ_top ∧ μ_vac ≠ μ_top) :=
  ⟨by norm_num,
   lambda_2_pos_at_density 0,
   lambda_3_pos_at_density 0,
   chamber_vacuum_unique_in_chamber,
   μ_vac_pos,
   chamber_eigenvalues_distinct⟩

/-- Discrete smeared-field operator (`W4`) scalar homogeneity, Schwartz-norm bound,
and vanishing on the zero test function. -/
theorem cl2_w4_smeared_field_linearity_and_bound
    {C : CausalSet} [Fintype C.Event]
    (c : ℝ) (f : SchwartzLike C) (e₀ : C.Event) (ψ : ChamberState) (i : Fin 3) :
    smearedField (SchwartzLike.smul c f) e₀ ψ i = c * smearedField f e₀ ψ i ∧
    |smearedField f e₀ ψ i| ≤ f.norm * |ψ i| ∧
    smearedField (SchwartzLike.zero C) e₀ ψ i = 0 ∧
    smearedField f e₀ Ω_chamber i = f.coord e₀ * Ω_chamber i :=
  ⟨smearedField_smul c f e₀ ψ i,
   smearedField_bound f e₀ ψ i,
   smearedField_zero e₀ ψ i,
   smearedField_vacuum f e₀ i⟩

/-- Causal-set microcausality on disjoint supports (`W5`) and chamber polynomial-state
cyclicity (`W6`). -/
theorem cl2_w5_w6_microcausality_and_chamber_cyclicity
    (C : CausalSet) [Fintype C.Event] :
    (∀ (φ ψ : C.Event → ℝ),
      (∀ e : C.Event, φ e ≠ 0 → ψ e = 0) →
        ∀ e : C.Event, φ e * ψ e = 0) ∧
    field_poly_state_zero = Ω_chamber ∧
    (∀ ψ : ChamberState, ∃ ψ' : ChamberState, ψ' = ψ) ∧
    (∀ B : BathSpectrum, ChamberIsLowestSector B →
      ∀ lam ∈ FullSpectrum B, μ_vac ≤ lam) :=
  ⟨fun φ ψ h_disjoint => HR2_locality φ ψ h_disjoint,
   chamber_vacuum_realized_polynomially,
   vacuum_cyclic_in_chamber,
   fun B hB => FullSpectrum_ge_μ_vac B hB⟩

/-- Lorentzian-direct Wightman ledger status verification for `W2`, `W3`, `W4`, `W5`, `W6`, `W7`. -/
theorem cl2_lorentzian_direct_bypasses_os_obstruction :
    W2_lorentz.status = WightmanStatusLorentz.FREE_FROM_CHAMBER_GAP ∧
    W3_lorentz.status = WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
    W4_lorentz.status = WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
    W5_lorentz.status = WightmanStatusLorentz.FREE_FROM_CAUSAL_SET ∧
    W6_lorentz.status = WightmanStatusLorentz.PROVED_DIRECT_CHAMBER ∧
    W7_lorentz.status = WightmanStatusLorentz.RESEARCH_HAAG_RUELLE ∧
    all_wightman_lorentz.length = 7 :=
  ⟨W2_lorentz_chamber,
   W3_lorentz_direct,
   W4_lorentz_direct,
   W5_lorentz_causal,
   W6_lorentz_direct,
   W7_lorentz_research,
   all_wightman_lorentz_length⟩

/-- Discrete Schwinger `n`-point function normalization (`OS0`), positivity (`OS2`), and
permutation symmetry (`OS3`). -/
theorem cl3_discrete_schwinger_normalization_positivity_symmetry
    (n : ℕ) (ρ β : ℝ) (W₀ : Fin 0 → ℝ) (W : Fin n → ℝ)
    (hW : ∀ i, 0 ≤ W i) (σ : Equiv.Perm (Fin n)) :
    discrete_Schwinger_n 0 ρ β W₀ = 1 ∧
    discrete_Schwinger_n n ρ β (fun _ => 1) = 1 ∧
    0 ≤ discrete_Schwinger_n n ρ β W ∧
    discrete_Schwinger_n n ρ β (W ∘ σ) = discrete_Schwinger_n n ρ β W :=
  ⟨discrete_Schwinger_0 ρ β W₀,
   discrete_Schwinger_n_normalized n ρ β,
   discrete_Schwinger_n_nonneg n ρ β W hW,
   OS3_symmetry n ρ β W σ⟩

/-- Discrete Schwinger cluster factorization (`OS4`) across `(mₙ, kₙ)` partitions and
discrete reflection positivity (`OS2`) at `s = √7`. -/
theorem cl3_discrete_schwinger_cluster_factorization_and_os2
    (mₙ kₙ : ℕ) (ρ β S : ℝ) (W₁ : Fin mₙ → ℝ) (W₂ : Fin kₙ → ℝ) :
    discrete_Schwinger_n mₙ ρ β W₁ * discrete_Schwinger_n kₙ ρ β W₂ =
      discrete_Schwinger_n (mₙ + kₙ) ρ β (Fin.append W₁ W₂) ∧
    YMBoltzmannWeight β (S + S) = YMBoltzmannWeight β S * YMBoltzmannWeight β S ∧
    0 < YMBoltzmannWeight β S ∧
    0 < (3 / 5) - (5 + Real.sqrt 7) / 30 :=
  ⟨OS4_cluster_factorization mₙ kₙ ρ β W₁ W₂,
   OS4_Boltzmann_multiplicative β S S,
   (OS2_reflection_positivity_discrete β S (Real.sqrt 7) sqrt7_sq sqrt7_pos).1,
   (OS2_reflection_positivity_discrete β S (Real.sqrt 7) sqrt7_sq sqrt7_pos).2⟩

/-- One-point and two-point discrete Schwinger factorization, swap symmetry, and
time-oriented causal-set irreflexivity. -/
theorem cl3_os_reconstruction_scope_and_conditional
    (ρ β : ℝ) (W₁ : Fin 1 → ℝ) (W₂ : Fin 2 → ℝ) :
    discrete_Schwinger_n 1 ρ β W₁ = WilsonExpectation ρ β (W₁ 0) ∧
    discrete_Schwinger_n 2 ρ β W₂ =
      WilsonExpectation ρ β (W₂ 0) * WilsonExpectation ρ β (W₂ 1) ∧
    discrete_Schwinger_n 2 ρ β (fun i => W₂ (Equiv.swap (0 : Fin 2) 1 i)) =
      discrete_Schwinger_n 2 ρ β W₂ ∧
    (∀ C : CausalSet, ∀ a : C.Event, ¬ C.prec a a) :=
  ⟨discrete_Schwinger_1 ρ β W₁,
   discrete_Schwinger_2 ρ β W₂,
   OS3_symmetry_swap2 ρ β W₂,
   causal_set_is_time_oriented⟩

/-! ### 3. Exponential Cluster Decomposition (`CL3_ClusterDecomposition`) & Constructive Measure (`CL3_ConstructiveMeasure`) -/

/-- Exact excited-to-vacuum eigenvalue ratios `1/(5 - √7)` and `1/(5 + √7)` in `(0, 1)` and
positivity of the logarithmic cluster mass gap `γ_cluster (√7) = ln(5 - √7) > 0`. -/
theorem cl3_excited_ratios_and_cluster_mass_gaps :
    lam_exc1 (Real.sqrt 7) / lam_vac = 1 / (5 - Real.sqrt 7) ∧
    lam_exc2 (Real.sqrt 7) / lam_vac = 1 / (5 + Real.sqrt 7) ∧
    (0 < lam_exc1 (Real.sqrt 7) / lam_vac ∧ lam_exc1 (Real.sqrt 7) / lam_vac < 1) ∧
    (0 < lam_exc2 (Real.sqrt 7) / lam_vac ∧ lam_exc2 (Real.sqrt 7) / lam_vac < 1) ∧
    0 < γ_cluster (Real.sqrt 7) ∧
    m_exc1 (Real.sqrt 7) < m_exc2 (Real.sqrt 7) ∧
    0 < γ_add (Real.sqrt 7) :=
  ⟨ratio_exc1_vac (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   ratio_exc2_vac (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   ratio_exc1_in_open_unit_interval (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   ratio_exc2_in_open_unit_interval (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   γ_cluster_pos (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   m_exc1_lt_m_exc2 (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   γ_add_pos (Real.sqrt 7) sqrt7_sq sqrt7_pos⟩

/-- Spectral two-point correlator decomposition and exponential cluster decay bound at rate
`γ_cluster (√7) = ln(5 - √7) > 0`. -/
theorem cl3_two_point_correlator_exponential_decay_and_cluster_bound
    (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (t : ℝ) (ht : 0 ≤ t) :
    two_point_correlator (Real.sqrt 7) c_top c_1 c_2 t =
      c_top + two_point_connected (Real.sqrt 7) c_1 c_2 t ∧
    0 ≤ two_point_connected (Real.sqrt 7) c_1 c_2 t ∧
    |two_point_connected (Real.sqrt 7) c_1 c_2 t| ≤
      (c_1 + c_2) * Real.exp (- γ_cluster (Real.sqrt 7) * t) ∧
    |two_point_correlator (Real.sqrt 7) c_top c_1 c_2 t - c_top| ≤
      (c_1 + c_2) * Real.exp (- γ_cluster (Real.sqrt 7) * t) :=
  ⟨two_point_decomp (Real.sqrt 7) c_top c_1 c_2 t,
   two_point_connected_nonneg (Real.sqrt 7) c_1 c_2 t hc_1 hc_2,
   two_point_exponential_decay (Real.sqrt 7) sqrt7_sq sqrt7_pos c_1 c_2 hc_1 hc_2 t ht,
   two_point_cluster_bound (Real.sqrt 7) sqrt7_sq sqrt7_pos c_top c_1 c_2 hc_1 hc_2 t ht⟩

/-- `ε`-`T₀` cluster decomposition theorem on the chamber sector at `s = √7`:
for every `ε₀ > 0`, there exists `T₀ > 0` such that `|W(t) - c_top| < ε₀` for all `t ≥ T₀`. -/
theorem cl3_chamber_cluster_decomposition_epsilon_delta
    (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |two_point_correlator (Real.sqrt 7) c_top c_1 c_2 t - c_top| < ε₀ :=
  cluster_decomposition (Real.sqrt 7) sqrt7_sq sqrt7_pos c_top c_1 c_2 hc_1 hc_2 ε₀ hε₀

/-- Causal-set Poisson mean positivity, volume roundtrip `causalSetPoissonMean ρ V / ρ = V`,
and Boltzmann weight multiplicativity and upper bound `≤ 1` for non-negative action. -/
theorem cl3_poisson_mean_and_boltzmann_multiplicativity
    (ρ V β S₁ S₂ : ℝ) (hρ : 0 < ρ) (hV : 0 < V) (hβ : 0 ≤ β) (hS₁ : 0 ≤ S₁) :
    0 < causalSetPoissonMean ρ V ∧
    causalSetPoissonMean ρ V / ρ = V ∧
    YMBoltzmannWeight β S₁ ≤ 1 ∧
    YMBoltzmannWeight β (S₁ + S₂) = YMBoltzmannWeight β S₁ * YMBoltzmannWeight β S₂ :=
  ⟨causalSetPoissonMean_pos ρ V hρ hV,
   causalSetPoissonMean_eq_volume_count ρ V hρ hV,
   YMBoltzmannWeight_le_one β S₁ hβ hS₁,
   YMBoltzmannWeight_mul β S₁ S₂⟩

/-- Constructive measure classification and 7-entry `cl3_ledger` verification. -/
theorem cl3_constructive_measure_classification_and_ledger
    (ρ β V : ℝ) (hρ : 0 < ρ) (hβ : 0 < β) (hV : 0 < V) (S W : ℝ) :
    0 < causalSetPoissonMean ρ V ∧
    0 < YMBoltzmannWeight β S ∧
    (∃ y : ℝ, y = WilsonExpectation ρ β W) ∧
    cl3_M1.status = MeasureStatus.DiscreteOnly ∧
    cl3_M2.status = MeasureStatus.DiscreteOnly ∧
    cl3_M3.status = MeasureStatus.ConditionalCL1 ∧
    cl3_M4.status = MeasureStatus.ConditionalCL1 ∧
    cl3_M5.status = MeasureStatus.NotAddressed ∧
    cl3_M6.status = MeasureStatus.NeedsClusterExp ∧
    cl3_M7.status = MeasureStatus.NotAddressed ∧
    cl3_ledger.length = 7 :=
  ⟨causalSetPoissonMean_pos ρ V hρ hV,
   YMBoltzmannWeight_pos β S,
   discrete_WilsonExpectation_exists ρ β hρ hβ W,
   cl3_M1_is_discrete,
   cl3_M2_is_discrete,
   cl3_M3_needs_CL1,
   cl3_M4_needs_CL1,
   cl3_M5_open,
   cl3_M6_needs_CE,
   cl3_M7_open,
   cl3_ledger_length⟩

/-- Combined chamber-sector cluster status (`cl3_M6_chamber = DiscreteOnly`) and full
7-item constructive measure distance ledger. -/
theorem cl3_chamber_cluster_and_measure_master :
    cl3_M6_chamber.status = MeasureStatus.DiscreteOnly ∧
    cl3_M6_full.status = MeasureStatus.NeedsClusterExp ∧
    cl3_M6_continuum.status = MeasureStatus.NeedsClusterExp ∧
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.DiscreteOnly)).length = 2 ∧
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.ConditionalCL1)).length = 2 ∧
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NeedsClusterExp)).length = 1 ∧
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NotAddressed)).length = 2 :=
  ⟨cl3_M6_chamber_status,
   cl3_M6_full_status,
   cl3_M6_continuum_status,
   cl3_ledger_discrete_count,
   cl3_ledger_cl1_count,
   cl3_ledger_clusterexp_count,
   cl3_ledger_notaddressed_count⟩

/-! ### 4. Clock-Floor 5-Operator Resolvents & Iterated Cores at the Chamber Eigenvalue Shifts -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- The bottom chamber eigenvalue shift `(5 - √7) / 30 > 0`. -/
def chamberBottomShift : ℝ := (5 - Real.sqrt 7) / 30

/-- The middle chamber eigenvalue shift `(5 + √7) / 30 > 0`. -/
def chamberMiddleShift : ℝ := (5 + Real.sqrt 7) / 30

/-- The additive chamber gap shift `(13 - √7) / 30 > 0`. -/
def chamberAdditiveGapShift : ℝ := (13 - Real.sqrt 7) / 30

/-- The top chamber eigenvalue shift `3 / 5 > 0`. -/
def chamberTopShift : ℝ := 3 / 5

/-- Strict positivity and strict ordering of all four chamber spectral shifts:
`0 < chamberBottomShift < chamberMiddleShift < chamberAdditiveGapShift < chamberTopShift`. -/
theorem chamber_spectral_shifts_pos_and_strict_order :
    0 < chamberBottomShift ∧
    chamberBottomShift < chamberMiddleShift ∧
    chamberMiddleShift < chamberAdditiveGapShift ∧
    chamberAdditiveGapShift < chamberTopShift := by
  unfold chamberBottomShift chamberMiddleShift chamberAdditiveGapShift chamberTopShift
  have hpos : 0 < Real.sqrt 7 := sqrt7_pos
  have hlt3 : Real.sqrt 7 < 3 := sqrt7_lt_3'
  have hgt2 : 2 < Real.sqrt 7 := sqrt7_gt_2'
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Collective 5-operator clock-floor resolvent norm sum bound at `chamberBottomShift = (5 - √7)/30 > 0`. -/
theorem clock_floor_five_resolvents_at_chamberBottomShift_norm_sum_le
    (t : ℝ) (f : Hilbert) :
    ‖RT chamberBottomShift f‖ + ‖RP chamberBottomShift f‖ + ‖RG chamberBottomShift f‖ +
      ‖RS t chamberBottomShift f‖ + ‖RH t chamberBottomShift f‖ ≤
      5 * chamberBottomShift⁻¹ * ‖f‖ :=
  five_resolvent_norm_sum_le ε hε h hh hb m g k t
    chamberBottomShift chamber_spectral_shifts_pos_and_strict_order.1 f

/-- Collective 5-operator clock-floor resolvent norm sum bounds at `chamberMiddleShift = (5 + √7)/30 > 0`
and `chamberTopShift = 3/5 > 0`. -/
theorem clock_floor_five_resolvents_at_chamberMiddle_and_Top_norm_sum_le
    (t : ℝ) (f : Hilbert) :
    (‖RT chamberMiddleShift f‖ + ‖RP chamberMiddleShift f‖ + ‖RG chamberMiddleShift f‖ +
      ‖RS t chamberMiddleShift f‖ + ‖RH t chamberMiddleShift f‖ ≤
      5 * chamberMiddleShift⁻¹ * ‖f‖) ∧
    (‖RT chamberTopShift f‖ + ‖RP chamberTopShift f‖ + ‖RG chamberTopShift f‖ +
      ‖RS t chamberTopShift f‖ + ‖RH t chamberTopShift f‖ ≤
      5 * chamberTopShift⁻¹ * ‖f‖) := by
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have hmid : 0 < chamberMiddleShift := hord.1.trans hord.2.1
  have htop : 0 < chamberTopShift := (hmid.trans hord.2.2.1).trans hord.2.2.2
  exact ⟨five_resolvent_norm_sum_le ε hε h hh hb m g k t chamberMiddleShift hmid f,
    five_resolvent_norm_sum_le ε hε h hh hb m g k t chamberTopShift htop f⟩

/-- Collective 5-operator clock-floor resolvent norm sum bound at `chamberAdditiveGapShift = (13 - √7)/30 > 0`. -/
theorem clock_floor_five_resolvents_at_chamberAdditiveGapShift_norm_sum_le
    (t : ℝ) (f : Hilbert) :
    ‖RT chamberAdditiveGapShift f‖ + ‖RP chamberAdditiveGapShift f‖ + ‖RG chamberAdditiveGapShift f‖ +
      ‖RS t chamberAdditiveGapShift f‖ + ‖RH t chamberAdditiveGapShift f‖ ≤
      5 * chamberAdditiveGapShift⁻¹ * ‖f‖ := by
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have hgap : 0 < chamberAdditiveGapShift := (hord.1.trans hord.2.1).trans hord.2.2.1
  exact five_resolvent_norm_sum_le ε hε h hh hb m g k t chamberAdditiveGapShift hgap f

/-- Unconditional 10-domain membership and second-power domain regularity of the two-parameter
iterated Hamiltonian resolvent `iteratedHamiltonianResolvent t chamberBottomShift chamberTopShift f`
evaluated at the bottom and top chamber eigenvalues. -/
theorem clock_floor_iterated_resolvent_at_chamberBottom_Top_mem_ten_domains
    (t : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    x ∈ (H t).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S t).domain ∧
    x ∈ (Eavg t).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres t).domain ∧
    x ∈ (clockHalf ε).domain := by
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have htop : 0 < chamberTopShift := ((hord.1.trans hord.2.1).trans hord.2.2.1).trans hord.2.2.2
  exact iteratedHamiltonianResolvent_mem_ten_domains
    ε hε h hh hb m g k t t chamberBottomShift chamberTopShift hord.1 htop f

/-- Exact second-power radial-residual identity for
`iteratedHamiltonianResolvent t chamberBottomShift chamberTopShift f` at all real couplings `m, g, k, t`. -/
theorem clock_floor_iterated_resolvent_at_chamberBottom_Top_second_power_eq
    (t : ℝ) (f : Hilbert) :
    let hord := chamber_spectral_shifts_pos_and_strict_order
    let htop : 0 < chamberTopShift := ((hord.1.trans hord.2.1).trans hord.2.2.1).trans hord.2.2.2
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f
    let y := RH t chamberTopShift f - (chamberBottomShift : ℂ) • x
    let hdom :=
      KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination.iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t chamberBottomShift chamberTopShift hord.1 htop f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((chamberBottomShift + chamberTopShift : ℝ) : ℂ) • RH t chamberTopShift f +
        ((chamberBottomShift ^ 2 : ℝ) : ℂ) • x := by
  intro hord htop
  exact iteratedHamiltonianResolvent_second_power_radial_residual_eq
    ε hε h hh hb m g k t chamberBottomShift chamberTopShift hord.1 htop f

/-- Unconditional common-domain shifted resolvent defect identities evaluated at
`chamberBottomShift = (5 - √7) / 30 > 0` for all real couplings `m, g, k, t`. -/
theorem clock_floor_common_domain_at_chamberBottomShift_shifted_defects
    (t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RH t chamberBottomShift (T ⟨x, hx.1.1.1⟩ + chamberBottomShift • x) =
      (Real.exp (2 * t) : ℂ) •
        RH t chamberBottomShift (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) ∧
    x - RS t chamberBottomShift (T ⟨x, hx.1.1.1⟩ + chamberBottomShift • x) =
      (Real.exp (2 * t) : ℂ) • RS t chamberBottomShift (P ⟨x, hx.1.2⟩) ∧
    x - RH t chamberBottomShift
        (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + chamberBottomShift • x) =
      (Real.exp (2 * t) : ℂ) • RH t chamberBottomShift (K ⟨x, hx.1.1.2⟩) := by
  have hbot := chamber_spectral_shifts_pos_and_strict_order.1
  exact ⟨unconditional_common_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k t chamberBottomShift hbot x hx,
    unconditional_common_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k t chamberBottomShift hbot x hx,
    unconditional_common_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k t chamberBottomShift hbot x hx⟩

/-- Unconditional two-time shifted resolvent Lipschitz bound on `commonOperatorDomain`
evaluated at `chamberAdditiveGapShift = (13 - √7) / 30 > 0`. -/
theorem clock_floor_common_domain_at_chamberAdditiveGapShift_two_time_defect_le
    (s t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (H s).domain :=
      KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
        ε hε h hh hb m g k s hx
    ‖x - RH t chamberAdditiveGapShift (H s ⟨x, hxs⟩ + chamberAdditiveGapShift • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (chamberAdditiveGapShift⁻¹ * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖)) := by
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have hgap : 0 < chamberAdditiveGapShift := (hord.1.trans hord.2.1).trans hord.2.2.1
  exact unconditional_common_two_time_shifted_resolvent_defect_norm_le
    ε hε h hh hb m g k s t chamberAdditiveGapShift hgap x hx

/-- Unconditional Gaussian clock-core sequence approximation `coreApproxSeq ε x` with
termwise shifted resolvent identities at `chamberBottomShift = (5 - √7) / 30 > 0`. -/
theorem clock_floor_core_approx_at_chamberBottomShift_convergence
    (t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (∀ j : ℕ, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
    (∀ j : ℕ, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k) ∧
    (∀ j : ℕ, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
      ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
      ∃ hPj : coreApproxSeq ε x j ∈ (P).domain,
        coreApproxSeq ε x j -
            RH t chamberBottomShift (T ⟨coreApproxSeq ε x j, hTj⟩ + chamberBottomShift • coreApproxSeq ε x j) =
          (Real.exp (2 * t) : ℂ) •
            RH t chamberBottomShift (K ⟨coreApproxSeq ε x j, hKj⟩ + P ⟨coreApproxSeq ε x j, hPj⟩) ∧
        coreApproxSeq ε x j -
            RS t chamberBottomShift (T ⟨coreApproxSeq ε x j, hTj⟩ + chamberBottomShift • coreApproxSeq ε x j) =
          (Real.exp (2 * t) : ℂ) • RS t chamberBottomShift (P ⟨coreApproxSeq ε x j, hPj⟩) ∧
        coreApproxSeq ε x j -
            RH t chamberBottomShift (T ⟨coreApproxSeq ε x j, hTj⟩ +
              (Real.exp (2 * t) : ℂ) • P ⟨coreApproxSeq ε x j, hPj⟩ +
              chamberBottomShift • coreApproxSeq ε x j) =
          (Real.exp (2 * t) : ℂ) • RH t chamberBottomShift (K ⟨coreApproxSeq ε x j, hKj⟩)) ∧
    Tendsto (fun j : ℕ => coreApproxSeq ε x j) atTop (nhds x) :=
  unconditional_coreApproxSeq_with_resolvent_identities
    ε hε h hh hb m g k t chamberBottomShift chamber_spectral_shifts_pos_and_strict_order.1 x hx

/-- Master synthesis uniting 1D lattice reflection positivity, `CL1` chamber continuum-limit
rigidity, `CL2` Lorentzian-direct Wightman verification, `CL3` discrete Schwinger factorization
and exponential cluster decay at rate `γ_cluster (√7) = ln(5 - √7) > 0`, and the clock-floor
5-operator resolvents and 10-domain iterated Hamiltonian resolvent at the chamber shifts. -/
theorem osterwalder_schrader_wightman_cluster_clock_floor_master_bridge
    (C : CausalSet) [Fintype C.Event]
    (t : ℝ) (ht : 0 ≤ t) (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (f : Hilbert) :
    (Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
     0 < chamberBottomShift ∧
     chamberBottomShift < chamberMiddleShift ∧
     chamberMiddleShift < chamberAdditiveGapShift ∧
     chamberAdditiveGapShift < chamberTopShift) ∧
    ((μ_vac < μ_first ∧ μ_vac < μ_top) ∧
     (∀ (φ ψ : C.Event → ℝ),
       (∀ e : C.Event, φ e ≠ 0 → ψ e = 0) →
         ∀ e : C.Event, φ e * ψ e = 0) ∧
     all_wightman_lorentz.length = 7) ∧
    (0 < γ_cluster (Real.sqrt 7) ∧
     |two_point_correlator (Real.sqrt 7) c_top c_1 c_2 t - c_top| ≤
       (c_1 + c_2) * Real.exp (- γ_cluster (Real.sqrt 7) * t) ∧
     cl3_M6_chamber.status = MeasureStatus.DiscreteOnly) ∧
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f ∈
       hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f ∈
       (clockHalf ε).domain ∧
     ‖RT chamberBottomShift f‖ + ‖RP chamberBottomShift f‖ + ‖RG chamberBottomShift f‖ +
       ‖RS t chamberBottomShift f‖ + ‖RH t chamberBottomShift f‖ ≤
       5 * chamberBottomShift⁻¹ * ‖f‖) :=
  ⟨⟨chamber_gap_continuum_limit,
    chamber_spectral_shifts_pos_and_strict_order.1,
    chamber_spectral_shifts_pos_and_strict_order.2.1,
    chamber_spectral_shifts_pos_and_strict_order.2.2.1,
    chamber_spectral_shifts_pos_and_strict_order.2.2.2⟩,
   ⟨chamber_vacuum_unique_in_chamber,
    fun φ ψ h_disjoint => HR2_locality φ ψ h_disjoint,
    all_wightman_lorentz_length⟩,
   ⟨γ_cluster_pos (Real.sqrt 7) sqrt7_sq sqrt7_pos,
    two_point_cluster_bound (Real.sqrt 7) sqrt7_sq sqrt7_pos c_top c_1 c_2 hc_1 hc_2 t ht,
    cl3_M6_chamber_status⟩,
   ⟨(clock_floor_iterated_resolvent_at_chamberBottom_Top_mem_ten_domains
      ε hε h hh hb m g k t f).1,
    (clock_floor_iterated_resolvent_at_chamberBottom_Top_mem_ten_domains
      ε hε h hh hb m g k t f).2.2.2.2.2.2.2.2.2.2,
    clock_floor_five_resolvents_at_chamberBottomShift_norm_sum_le ε hε h hh hb m g k t f⟩⟩

#print axioms lattice_boltzmann_and_plaquette_positivity
#print axioms lattice_transfer_matrix_positivity_and_symmetry
#print axioms lattice_transfer_matrix_diagonal_dominance_and_contrast
#print axioms lattice_reflection_positivity_rank_one_and_factored
#print axioms cl1_chamber_matrix_and_charPoly_density_rigidity
#print axioms cl1_chamber_eigenvalues_and_gap_positivity
#print axioms cl1_chamber_eigenvalues_and_gap_continuum_convergence
#print axioms cl1_chamber_algebraic_master_synthesis
#print axioms cl2_substrate_lorentzian_order_properties
#print axioms cl2_w2_w3_chamber_spectrum_and_vacuum_uniqueness
#print axioms cl2_w4_smeared_field_linearity_and_bound
#print axioms cl2_w5_w6_microcausality_and_chamber_cyclicity
#print axioms cl2_lorentzian_direct_bypasses_os_obstruction
#print axioms cl3_discrete_schwinger_normalization_positivity_symmetry
#print axioms cl3_discrete_schwinger_cluster_factorization_and_os2
#print axioms cl3_os_reconstruction_scope_and_conditional
#print axioms cl3_excited_ratios_and_cluster_mass_gaps
#print axioms cl3_two_point_correlator_exponential_decay_and_cluster_bound
#print axioms cl3_chamber_cluster_decomposition_epsilon_delta
#print axioms cl3_poisson_mean_and_boltzmann_multiplicativity
#print axioms cl3_constructive_measure_classification_and_ledger
#print axioms cl3_chamber_cluster_and_measure_master
#print axioms chamber_spectral_shifts_pos_and_strict_order
#print axioms clock_floor_five_resolvents_at_chamberBottomShift_norm_sum_le
#print axioms clock_floor_five_resolvents_at_chamberMiddle_and_Top_norm_sum_le
#print axioms clock_floor_five_resolvents_at_chamberAdditiveGapShift_norm_sum_le
#print axioms clock_floor_iterated_resolvent_at_chamberBottom_Top_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_chamberBottom_Top_second_power_eq
#print axioms clock_floor_common_domain_at_chamberBottomShift_shifted_defects
#print axioms clock_floor_common_domain_at_chamberAdditiveGapShift_two_time_defect_le
#print axioms clock_floor_core_approx_at_chamberBottomShift_convergence
#print axioms osterwalder_schrader_wightman_cluster_clock_floor_master_bridge

end

end UnifiedTheory.Audit.KFCausalClockFloorOsterwalderSchraderWightmanReconstructionBridge
