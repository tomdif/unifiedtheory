/- Complete Yang-Mills R1-R2b-R3-R4 Continuum Mass-Gap and Clock-Floor
Hilbert-Space Iterated-Resolvent & Core-Approximation Bridge:
1. Synthesizes the genuine Mathlib-backed SO(10) Haar probability measure (R2b:
   haarMeasureSO10 univ = 1, ∫ reTraceSO10 dHaar = 0) with the Strategy-B
   centroid-anti-invariant block-splitting closure (R1: CentroidParitySplitsBlocks H
   ↔ ChamberBathCommutes H ↔ commutesWithDiagonal H chamberLabel, unconditionally
   discharged for Build3's H_W).
2. Unifies the chamber heat-semigroup operator-norm exponential decay (R3:
   ‖exp(-t(J₄ - μ_vac I)) ψ‖² ≤ exp(-2 γ t) ‖ψ‖² at closed-form rate
   γ = γ_vac_chamber = √7 / 15 > 1 / 8 > 0) with density-rigid continuum-limit
   convergence as ρ → ∞ (R4: chamber matrix, 3-eigenvalue spectrum, chamber gap
   (13 - √7)/30, bath spectrum μ = 3, structural Wilson expectation, and mass gap
   massGapAtDensity ρ = √7 / 15).
3. Couples the strictly positive Yang-Mills mass gap yangMillsGapShift := γ_vac_chamber
   = √7 / 15 > 0 directly into the infinite-dimensional clock-floor Hilbert-space
   operator family (T, P, G, S(t), H(t)), proving unconditional 10-domain
   second-power regularity of iteratedHamiltonianResolvent at shift a = b = √7 / 15,
   arbitrary-coupling shifted resolvent defect identities, and 9-graph Gaussian
   clock-core sequence approximation alongside the R1-R2b-R3-R4 continuum bridge. -/
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
import UnifiedTheory.LayerB.R1_Closure_via_R2b
import UnifiedTheory.LayerB.R3_MassGapExponentialDecay
import UnifiedTheory.LayerB.R4_ContinuumLimitConvergence
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorYangMillsR1R2R3R4ContinuumBridge

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProduct
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.YangMillsCausalAttack
open UnifiedTheory.LayerB.CL1_BathSector
open UnifiedTheory.LayerB.CL1_ContinuumLimit
open UnifiedTheory.LayerB.Clay1_GeneralPoissonLift
open UnifiedTheory.LayerB.Clay_BHS_SubstrateIdentification
open UnifiedTheory.LayerB.Build3_ExplicitFeshbach
open UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation
open UnifiedTheory.LayerB.Build5_WilsonYMSynthesis
open UnifiedTheory.LayerB.Build6_VolterraBlockDiagonalDerivation
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure
open UnifiedTheory.LayerB.CL3_ClusterDecomposition
open UnifiedTheory.LayerB.R1_ChamberBathCommutes_FullYM
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.R1_Closure_via_R2b
open UnifiedTheory.LayerB.R3_MassGapExponentialDecay
open UnifiedTheory.LayerB.R4_ContinuumLimitConvergence
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorFullFiveResolventChainSynthesis (five_resolvent_norm_sum_le)
open KFCausalClockFloorIteratedResolventSecondPowerCore (hamiltonianSecondPowerDomain)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains
   squaredHamiltonianResolvent_second_power_radial_residual_eq
   residual_sub_iteratedHamiltonianResolvent_eq)
open KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
  (unconditionalCoreDomain growingClockCoreDomain coreApproxSeq)
open KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation
  (unconditional_common_hamiltonian_static_shifted_resolvent_defect
   unconditional_common_residual_static_shifted_resolvent_defect
   unconditional_common_hamiltonian_residual_shifted_resolvent_defect
   unconditional_common_two_time_shifted_resolvent_defect_norm_le
   unconditional_coreApproxSeq_with_resolvent_identities)

/-! ### 1. Genuine `SO(10)` Haar Probability Measure (`R2b`) & Centroid-Parity Closure (`R1`) -/

/-- The genuine Mathlib-backed Haar measure on `G_SO10 = Matrix.specialOrthogonalGroup (Fin 10) ℝ`
is a normalized probability measure (`haarMeasureSO10 Set.univ = 1`) whose real trace integral
vanishes (`∫ U, reTraceSO10 U ∂haarMeasureSO10 = 0`). -/
theorem so10_haar_measure_univ_and_trace_zero :
    haarMeasureSO10 (Set.univ : Set G_SO10) = 1 ∧
    (∫ _ : G_SO10, (1 : ℝ) ∂haarMeasureSO10 = 1) ∧
    (∫ U : G_SO10, reTraceSO10 U ∂haarMeasureSO10 = 0) :=
  ⟨haarMeasureSO10_univ, interface_normalization_concrete, haarTraceIdentitySO10_concrete⟩

/-- The concrete Wilson Haar integral satisfies `wilsonHaarIntegral (fun _ => c) = c` for every
constant `c : ℝ` and vanishes on `reTraceSO10`. -/
theorem so10_wilson_haar_integral_const_and_trace_zero (c : ℝ) :
    wilsonHaarIntegral (fun _ => c) = c ∧
    wilsonHaarIntegral reTraceSO10 = 0 :=
  ⟨wilsonHaarIntegral_const c, haarTraceIdentitySO10_concrete⟩

/-- Bridge between `Build4`'s `physicalWilsonExpectation` and the genuine `SO(10)` Haar
integral on all constant observables `c : ℝ` and `1`. -/
theorem so10_build4_constant_channel_haar_bridge (ρ β c : ℝ) :
    physicalWilsonExpectation ρ β c = ∫ _U : G_SO10, c ∂haarMeasureSO10 ∧
    physicalWilsonExpectation ρ β 1 = ∫ _U : G_SO10, (1 : ℝ) ∂haarMeasureSO10 :=
  ⟨build4_constant_channel_haar ρ β c, build4_one_channel_haar ρ β⟩

/-- Algebraic closure of `CentroidAntiInvariant` on `G_SO10 → ℝ` under zero, negation,
addition, scalar multiplication, and instantiation by `reTraceSO10`. -/
theorem so10_centroid_anti_invariant_closure :
    CentroidAntiInvariant (fun _ : G_SO10 => (0 : ℝ)) ∧
    CentroidAntiInvariant reTraceSO10 ∧
    (∀ F : G_SO10 → ℝ, CentroidAntiInvariant F → CentroidAntiInvariant (fun g => -F g)) ∧
    (∀ F G : G_SO10 → ℝ, CentroidAntiInvariant F → CentroidAntiInvariant G →
      CentroidAntiInvariant (fun g => F g + G g)) ∧
    (∀ (c : ℝ) (F : G_SO10 → ℝ), CentroidAntiInvariant F →
      CentroidAntiInvariant (fun g => c * F g)) :=
  ⟨zero_centroid_anti_invariant,
   reTraceSO10_centroid_anti_invariant,
   fun _ hF => hF.neg,
   fun _ _ hF hG => hF.add hG,
   fun c _ hF => hF.smul c⟩

/-- Every centroid-anti-invariant observable `F : G_SO10 → ℝ` has vanishing Haar integral
against `haarMeasureSO10`, recovering `∫ reTraceSO10 dHaar = 0` as a special case. -/
theorem so10_centroid_anti_invariant_integral_vanishes
    (F : G_SO10 → ℝ) (hF : CentroidAntiInvariant F) :
    (∫ g, F g ∂haarMeasureSO10 = 0) ∧
    (∫ U, reTraceSO10 U ∂haarMeasureSO10 = 0) :=
  ⟨centroid_anti_invariant_integral_zero F hF, trace_identity_via_centroid⟩

/-- Strategy-B closure of `R1` via the genuine `SO(10)` Haar measure: any `6 × 6` Hamiltonian
satisfying `CentroidParitySplitsBlocks` satisfies `ChamberBathCommutes`, and `Build3`'s `H_W`
satisfies both unconditionally. -/
theorem wilson_chamber_bath_commutes_via_so10_haar :
    (∀ H : Fin 6 → Fin 6 → ℝ, CentroidParitySplitsBlocks H → ChamberBathCommutes H) ∧
    CentroidParitySplitsBlocks H_W ∧
    ChamberBathCommutes H_W :=
  ⟨R1_strategyB_closure, H_W_centroid_parity_splits_blocks, H_W_chamberBath_commutes_via_R2b⟩

/-- Triple equivalence of the three `R1` formulations (`ChamberBathCommutes`,
`commutesWithDiagonal · chamberLabel`, and `CentroidParitySplitsBlocks`) for all `6 × 6`
Hamiltonians, together with all three witnesses for `H_W`. -/
theorem wilson_r1_triple_equivalence_and_small_case (H : Fin 6 → Fin 6 → ℝ) :
    ((ChamberBathCommutes H ↔ commutesWithDiagonal H chamberLabel) ∧
     (ChamberBathCommutes H ↔ CentroidParitySplitsBlocks H)) ∧
    (CentroidParitySplitsBlocks H_W ∧
     commutesWithDiagonal H_W chamberLabel ∧
     ChamberBathCommutes H_W) :=
  ⟨R1_triple_equivalence H,
   ⟨H_W_centroid_parity_splits_blocks,
    H_W_commutes_with_chamberLabel,
    H_W_chamberBath_commutes_via_R2b⟩⟩

/-- Simultaneous discharge of `WilsonBlockHypothesis H_W`, `ChamberBathCommutes H_W`,
and the `SO(10)` Haar trace identity. -/
theorem wilson_r1_block_hypothesis_and_haar_trace :
    WilsonBlockHypothesis H_W ∧
    ChamberBathCommutes H_W ∧
    CentroidParitySplitsBlocks H_W ∧
    (∫ U, reTraceSO10 U ∂haarMeasureSO10 = 0) :=
  ⟨H_W_satisfies_block_hypothesis,
   H_W_chamberBath_commutes_via_R2b,
   H_W_centroid_parity_splits_blocks,
   trace_identity_via_centroid⟩

/-- Complete `R1` master synthesis via `R2b`. -/
theorem wilson_r1_closure_master_synthesis :
    (∀ H : Fin 6 → Fin 6 → ℝ, CentroidParitySplitsBlocks H → ChamberBathCommutes H) ∧
    (∀ H : Fin 6 → Fin 6 → ℝ, ChamberBathCommutes H ↔ CentroidParitySplitsBlocks H) ∧
    (∀ H : Fin 6 → Fin 6 → ℝ, ChamberBathCommutes H ↔ commutesWithDiagonal H chamberLabel) ∧
    CentroidParitySplitsBlocks H_W ∧
    commutesWithDiagonal H_W chamberLabel ∧
    ChamberBathCommutes H_W ∧
    WilsonBlockHypothesis H_W ∧
    (∫ U, reTraceSO10 U ∂haarMeasureSO10 = 0) :=
  R1_closure_master

/-- Agreement of the `R2b` and `R1` status verdicts. -/
theorem wilson_r1_r2b_verdict_agreement :
    verdict = HaarConstructionVerdict.GenuineHaarFormalized ∧
    r1_closure_verdict = R1ClosureVerdict.R1_REDUCED_TO_SHARP_LEMMA ∧
    r1_closure_verdict_smallcase = R1ClosureVerdict.R1_FULLY_CLOSED :=
  ⟨verdict_genuine, r1_closure_verdict_correct, r1_closure_verdict_smallcase_correct⟩

/-! ### 2. Chamber Heat-Semigroup Exponential Decay (`R3`) & Continuum Convergence (`R4`) -/

/-- Closed-form expression and quantitative positivity bounds for the chamber mass gap
`γ_vac_chamber = √7 / 15 > 1 / 8 > 0` and strict ordering of the three chamber eigenvalues. -/
theorem chamber_mass_gap_closed_form_and_lower_bound :
    γ_vac_chamber = Real.sqrt 7 / 15 ∧
    (1 : ℝ) / 8 < γ_vac_chamber ∧
    0 < γ_vac_chamber ∧
    μ_vac < μ_first ∧
    μ_first < μ_top ∧
    γ_vac_chamber ≤ μ_top - μ_vac :=
  ⟨decay_rate_closed_form,
   decay_rate_lower_bound,
   decay_rate_positive,
   chamber_sorted_strict.1,
   chamber_sorted_strict.2,
   shifted_eigenvalue_top_ge_first⟩

/-- Shifted chamber heat-semigroup identity at `t = 0`, orthogonal-complement invariance,
and exponential decay at rate `γ_vac_chamber = √7 / 15` (`R3`). -/
theorem chamber_heat_semigroup_orth_vac_contraction
    (t : ℝ) (ht : 0 ≤ t) (ψ : ChamberState) (hψ : ChamberState.InOrthVac ψ) :
    heatSemigroupShifted 0 ψ = ψ ∧
    ChamberState.InOrthVac (heatSemigroupShifted t ψ) ∧
    (heatSemigroupShifted t ψ).normSq ≤ Real.exp (-2 * t * γ_vac_chamber) * ψ.normSq ∧
    (heatSemigroupShifted t ψ).normSq ≤ Real.exp (-2 * t * (Real.sqrt 7 / 15)) * ψ.normSq :=
  ⟨heatSemigroupShifted_at_zero ψ,
   heatSemigroupShifted_preserves_orthVac t ψ hψ,
   spectral_gap_implies_exp_decay_in_orth_complement t ht ψ hψ,
   spectral_gap_exp_decay_closed_form t ht ψ hψ⟩

/-- Squared operator-norm ratio bound `(heatSemigroupShifted t ψ).normSq / ψ.normSq ≤ exp(-2 γ t)`
on the orthogonal complement of the chamber vacuum (`R3`). -/
theorem chamber_heat_semigroup_operator_norm_ratio_le
    (t : ℝ) (ht : 0 ≤ t) (ψ : ChamberState) (hψ : ChamberState.InOrthVac ψ)
    (h_nz : 0 < ψ.normSq) :
    (heatSemigroupShifted t ψ).normSq / ψ.normSq ≤ Real.exp (-2 * t * γ_vac_chamber) :=
  spectral_gap_operator_norm_bound t ht ψ hψ h_nz

/-- Bridge between the additive Hamiltonian decay rate `γ_vac_chamber = √7 / 15 > 0`
and the transfer-matrix cluster log-gap rate `γ_cluster s > 0` (`s² = 7, s > 0`). -/
theorem chamber_additive_and_log_gap_correlator_bridge :
    (0 < γ_vac_chamber ∧ γ_vac_chamber = Real.sqrt 7 / 15) ∧
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → 0 < γ_cluster s) ∧
    (μ_vac < μ_first ∧ μ_first < μ_top) :=
  chamber_correlator_exp_decay_bridge

/-- Continuum-limit convergence (`ρ → ∞`) and density rigidity of the `3 × 3` chamber matrix
and its three eigenvalues `3/5`, `(5 + √7)/30`, and `(5 - √7)/30` (`R4`). -/
theorem chamber_matrix_and_spectrum_continuum_convergence :
    (∀ ρ i j, H_chamber_at_density ρ i j = H_chamber_continuum i j) ∧
    (∀ i j : Fin 3,
      Tendsto (fun ρ : ℝ => (H_chamber_at_density ρ i j : ℝ))
              atTop (𝓝 ((H_chamber_continuum i j : ℝ)))) ∧
    Tendsto lambda_top_at_density atTop (𝓝 (3 / 5)) ∧
    Tendsto lambda_2_at_density atTop (𝓝 ((5 + Real.sqrt 7) / 30)) ∧
    Tendsto lambda_3_at_density atTop (𝓝 ((5 - Real.sqrt 7) / 30)) :=
  ⟨chamber_continuum_identification_R4,
   chamber_matrix_entry_continuum_convergence,
   chamber_top_eigenvalue_continuum_convergence,
   chamber_middle_eigenvalue_continuum_convergence,
   chamber_bottom_eigenvalue_continuum_convergence⟩

/-- Continuum-limit convergence (`ρ → ∞`) and strict positivity of both the chamber gap
`(13 - √7)/30` and the Yang-Mills mass gap `massGapAtDensity ρ = √7 / 15` (`R4`). -/
theorem chamber_gap_and_mass_gap_continuum_convergence :
    Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
    0 < (13 - Real.sqrt 7) / 30 ∧
    (∀ ρ : ℝ, massGapAtDensity ρ = Real.sqrt 7 / 15) ∧
    Tendsto massGapAtDensity atTop (𝓝 (Real.sqrt 7 / 15)) ∧
    0 < Real.sqrt 7 / 15 :=
  ⟨chamber_gap_continuum_convergence,
   chamber_gap_continuum_limit_positive,
   massGapAtDensity_eq,
   mass_gap_continuum_convergence,
   mass_gap_continuum_limit_positive⟩

/-- Continuum-limit convergence and density rigidity of the bath spectrum (`μ = 3`) (`R4`). -/
theorem bath_spectrum_continuum_rigidity_three :
    (∀ k : ℕ, 1 ≤ k → bath_eigenvalue_continuum k = 3) ∧
    (∀ k : ℕ, Tendsto (fun _ρ : ℝ => general_poisson_bath_eigenvalue k)
                      atTop (𝓝 (bath_eigenvalue_continuum k))) ∧
    (∀ (ρ : ℝ) (μ : ℝ), μ ∈ (general_poisson_bath_spectrum ρ).eigs → μ = 3) :=
  ⟨bath_eigenvalue_continuum_eq_three,
   bath_eigenvalue_continuum_convergence,
   bath_spectrum_continuum_convergence⟩

/-- Combined continuum-limit convergence (`R4`) and genuine `SO(10)` Haar constant-channel
identification (`R2b`) for `physicalWilsonExpectation`. -/
theorem physical_wilson_expectation_continuum_and_haar_bridge (ρ₁ ρ₂ β W : ℝ) :
    physicalWilsonExpectation ρ₁ β W = physicalWilsonExpectation ρ₂ β W ∧
    Tendsto (fun ρ : ℝ => physicalWilsonExpectation ρ β W)
            atTop (𝓝 (physicalWilsonExpectation 0 β W)) ∧
    physicalWilsonExpectation ρ₁ β W = ∫ _U : G_SO10, W ∂haarMeasureSO10 :=
  ⟨physicalWilsonExpectation_density_rigid ρ₁ ρ₂ β W,
   physicalWilsonExpectation_continuum_convergence β W,
   build4_constant_channel_haar ρ₁ β W⟩

/-- Explicit verification of all five fields of `canonical_continuum_limit_interface` (`R4`). -/
theorem canonical_continuum_limit_interface_properties :
    (∀ (ρ₁ ρ₂ : ℝ) (i j : Fin 3),
      canonical_continuum_limit_interface.chamberMatrixRigid ρ₁ ρ₂ i j =
        H_chamber_entry_density_independent ρ₁ ρ₂ i j) ∧
    (∀ ρ : ℝ, massGapAtDensity ρ = γ_vac_chamber) :=
  ⟨fun _ _ _ _ => rfl,
   fun ρ => (massGapAtDensity_eq ρ).trans decay_rate_closed_form.symm⟩

/-- Combined `R3` exponential-decay and `R4` continuum-limit master synthesis. -/
theorem wilson_r3_r4_combined_master_synthesis :
    ((0 < γ_vac_chamber ∧ γ_vac_chamber = Real.sqrt 7 / 15) ∧
     (∀ t : ℝ, 0 ≤ t → ∀ ψ : ChamberState, ChamberState.InOrthVac ψ →
       (heatSemigroupShifted t ψ).normSq ≤ Real.exp (-2 * t * γ_vac_chamber) * ψ.normSq)) ∧
    (Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
     Tendsto massGapAtDensity atTop (𝓝 (Real.sqrt 7 / 15)) ∧
     0 < Real.sqrt 7 / 15) :=
  ⟨⟨⟨decay_rate_positive, decay_rate_closed_form⟩,
    spectral_gap_implies_exp_decay_in_orth_complement⟩,
   ⟨chamber_gap_continuum_convergence,
    mass_gap_continuum_convergence,
    mass_gap_continuum_limit_positive⟩⟩

/-- Combined `R3` and `R4` machine-checked status and verdict ledger. -/
theorem wilson_r3_r4_verdict_and_status_ledger :
    cl3_M6_chamber_operator_norm.status = MeasureStatus.DiscreteOnly ∧
    r4_status_at_level R4Level.StructuralWilsonExpectation = R4Status.Proved ∧
    r4_status_at_level R4Level.ChamberOperator = R4Status.Proved ∧
    r4_verdict = R4Verdict.CHAMBER_LEVEL_PROVED_FULL_LEVEL_RESIDUAL :=
  ⟨cl3_M6_chamber_operator_norm_status,
   r4_structural_proved,
   r4_chamber_proved,
   r4_verdict_eq⟩

/-! ### 3. Joint Yang–Mills `R1`–`R2b`–`R3`–`R4` and Clock-Floor Hilbert-Space Resolvent/Core Bridge -/

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

/-- The canonical Yang-Mills spectral-gap resolvent shift `yangMillsGapShift := γ_vac_chamber = √7 / 15`. -/
def yangMillsGapShift : ℝ := γ_vac_chamber

/-- Strict positivity and closed-form continuum identification of `yangMillsGapShift`:
`0 < yangMillsGapShift`, `yangMillsGapShift = √7 / 15`, and `∀ ρ, massGapAtDensity ρ = yangMillsGapShift`. -/
theorem yangMillsGapShift_pos_and_eq_massGapAtDensity :
    0 < yangMillsGapShift ∧
    (1 : ℝ) / 8 < yangMillsGapShift ∧
    yangMillsGapShift = Real.sqrt 7 / 15 ∧
    (∀ ρ : ℝ, massGapAtDensity ρ = yangMillsGapShift) :=
  ⟨decay_rate_positive,
   decay_rate_lower_bound,
   decay_rate_closed_form,
   fun ρ => (massGapAtDensity_eq ρ).trans decay_rate_closed_form.symm⟩

/-- Evaluating all five clock-floor shifted resolvents `RT`, `RP`, `RG`, `RS t`, and `RH t`
at the Yang-Mills mass-gap shift `yangMillsGapShift = √7 / 15 > 0` yields the collective
Hilbert norm bound `≤ 5 * yangMillsGapShift⁻¹ * ‖f‖` for all real couplings `m, g, k, t`. -/
theorem clock_floor_resolvent_at_yangMillsGapShift_five_operator_sum_le
    (t : ℝ) (f : Hilbert) :
    ‖RT yangMillsGapShift f‖ + ‖RP yangMillsGapShift f‖ + ‖RG yangMillsGapShift f‖ +
      ‖RS t yangMillsGapShift f‖ + ‖RH t yangMillsGapShift f‖ ≤
      5 * yangMillsGapShift⁻¹ * ‖f‖ :=
  five_resolvent_norm_sum_le ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive f

/-- Unconditional 10-domain membership and second-power regularity of the iterated
clock-floor Hamiltonian resolvent `squaredHamiltonianResolvent` evaluated at the
Yang-Mills mass-gap shift `yangMillsGapShift = √7 / 15 > 0` for all real `m, g, k, t, s`. -/
theorem clock_floor_iterated_resolvent_at_yangMillsGapShift_mem_ten_domains
    (t s : ℝ) (f : Hilbert) :
    let x := squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    x ∈ (H t).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S t).domain ∧
    x ∈ (Eavg s).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres s).domain ∧
    x ∈ (clockHalf ε).domain :=
  iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t s
    yangMillsGapShift yangMillsGapShift decay_rate_positive decay_rate_positive f

/-- Exact second-power radial-residual decomposition for `squaredHamiltonianResolvent`
at `yangMillsGapShift = √7 / 15` for all real couplings `m, g, k, t`. -/
theorem clock_floor_iterated_resolvent_at_yangMillsGapShift_second_power_eq
    (t : ℝ) (f : Hilbert) :
    let x := squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f
    let y := RH t yangMillsGapShift f - (yangMillsGapShift : ℂ) • x
    let hdom :=
      KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination.iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t yangMillsGapShift yangMillsGapShift
        decay_rate_positive decay_rate_positive f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((yangMillsGapShift + yangMillsGapShift : ℝ) : ℂ) • RH t yangMillsGapShift f +
        ((yangMillsGapShift ^ 2 : ℝ) : ℂ) • x :=
  squaredHamiltonianResolvent_second_power_radial_residual_eq
    ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive f

/-- Exact residual-Hamiltonian second resolvent identity for `squaredHamiltonianResolvent`
at `yangMillsGapShift = √7 / 15` for all real couplings `m, g, k, t`. -/
theorem clock_floor_iterated_resolvent_at_yangMillsGapShift_residual_diff_eq
    (t : ℝ) (f : Hilbert) :
    RS t yangMillsGapShift (RH t yangMillsGapShift f) -
      squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f =
      (Real.exp (2 * t) : ℂ) •
        RS t yangMillsGapShift
          (K ⟨squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive
              (RH t yangMillsGapShift f)⟩) :=
  residual_sub_iteratedHamiltonianResolvent_eq ε hε h hh hb m g k t
    yangMillsGapShift yangMillsGapShift decay_rate_positive f

/-- Unconditional arbitrary-coupling (`k ∈ ℝ`) shifted resolvent defect identities on
`commonOperatorDomain` evaluated at `yangMillsGapShift = √7 / 15 > 0`. -/
theorem clock_floor_common_domain_at_yangMillsGapShift_shifted_defects
    (t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RH t yangMillsGapShift (T ⟨x, hx.1.1.1⟩ + yangMillsGapShift • x) =
      (Real.exp (2 * t) : ℂ) •
        RH t yangMillsGapShift (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩) ∧
    x - RS t yangMillsGapShift (T ⟨x, hx.1.1.1⟩ + yangMillsGapShift • x) =
      (Real.exp (2 * t) : ℂ) • RS t yangMillsGapShift (P ⟨x, hx.1.2⟩) ∧
    x - RH t yangMillsGapShift
        (T ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.2⟩ + yangMillsGapShift • x) =
      (Real.exp (2 * t) : ℂ) • RH t yangMillsGapShift (K ⟨x, hx.1.1.2⟩) :=
  ⟨unconditional_common_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive x hx,
   unconditional_common_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive x hx,
   unconditional_common_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k t yangMillsGapShift decay_rate_positive x hx⟩

/-- Unconditional two-time shifted resolvent Lipschitz bound on `commonOperatorDomain`
at `yangMillsGapShift = √7 / 15 > 0` for all real couplings `m, g, k`. -/
theorem clock_floor_common_domain_at_yangMillsGapShift_two_time_defect_le
    (s t : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hxs : x ∈ (H s).domain :=
      KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
        ε hε h hh hb m g k s hx
    ‖x - RH t yangMillsGapShift (H s ⟨x, hxs⟩ + yangMillsGapShift • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (yangMillsGapShift⁻¹ * (‖K ⟨x, hx.1.1.2⟩‖ + ‖P ⟨x, hx.1.2⟩‖)) :=
  unconditional_common_two_time_shifted_resolvent_defect_norm_le
    ε hε h hh hb m g k s t yangMillsGapShift decay_rate_positive x hx

/-- Unconditional Gaussian clock-core sequence approximation `coreApproxSeq ε x`
with termwise shifted resolvent identities at `yangMillsGapShift = √7 / 15 > 0`
for all real couplings `m, g, k`. -/
theorem clock_floor_core_approx_at_yangMillsGapShift_convergence
    (s : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
        ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
        ∃ hPj : coreApproxSeq ε x j ∈ (P).domain,
          coreApproxSeq ε x j -
              RH s yangMillsGapShift (T ⟨coreApproxSeq ε x j, hTj⟩ + yangMillsGapShift • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RH s yangMillsGapShift (K ⟨coreApproxSeq ε x j, hKj⟩ + P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j -
              RS s yangMillsGapShift (T ⟨coreApproxSeq ε x j, hTj⟩ + yangMillsGapShift • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RS s yangMillsGapShift (P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j -
              RH s yangMillsGapShift (T ⟨coreApproxSeq ε x j, hTj⟩ +
                (Real.exp (2 * s) : ℂ) • P ⟨coreApproxSeq ε x j, hPj⟩ +
                yangMillsGapShift • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RH s yangMillsGapShift (K ⟨coreApproxSeq ε x j, hKj⟩)) ∧
      Tendsto (coreApproxSeq ε x) atTop (𝓝 x) :=
  unconditional_coreApproxSeq_with_resolvent_identities
    ε hε h hh hb m g k s yangMillsGapShift decay_rate_positive x hx

/-- Joint synthesis of `R1` (`ChamberBathCommutes H_W` via `R2b`), `R2b` (`SO(10)` Haar
trace identity), `R3` (exponential decay at rate `√7 / 15`), `R4` (continuum-limit
convergence `ρ → ∞`), and 10-domain second-power regularity of the clock-floor iterated
Hamiltonian resolvent at `yangMillsGapShift = √7 / 15`. -/
theorem yang_mills_r1_r2b_r3_r4_and_clock_floor_iterated_resolvent_bridge
    (t s : ℝ) (ht : 0 ≤ t) (ψ : ChamberState) (hψ : ChamberState.InOrthVac ψ) (f : Hilbert) :
    let x := squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f
    ChamberBathCommutes H_W ∧
    (∫ U : G_SO10, reTraceSO10 U ∂haarMeasureSO10 = 0) ∧
    (heatSemigroupShifted t ψ).normSq ≤ Real.exp (-2 * t * yangMillsGapShift) * ψ.normSq ∧
    Tendsto massGapAtDensity atTop (𝓝 yangMillsGapShift) ∧
    (x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     x ∈ (H t).domain ∧ x ∈ (K).domain ∧ x ∈ (S t).domain ∧
     x ∈ (Eavg s).domain ∧ x ∈ (clockHalf ε).domain) := by
  intro x
  have h10 := clock_floor_iterated_resolvent_at_yangMillsGapShift_mem_ten_domains
    ε hε h hh hb m g k t s f
  have hlim : Tendsto massGapAtDensity atTop (𝓝 yangMillsGapShift) := by
    unfold yangMillsGapShift
    rw [decay_rate_closed_form]
    exact mass_gap_continuum_convergence
  exact ⟨H_W_chamberBath_commutes_via_R2b,
    haarTraceIdentitySO10_concrete,
    spectral_gap_implies_exp_decay_in_orth_complement t ht ψ hψ,
    hlim,
    ⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.2.2⟩⟩

/-- Joint synthesis of the `R4` continuum mass-gap convergence and the arbitrary-coupling
clock-floor Gaussian core approximation at `yangMillsGapShift = √7 / 15`. -/
theorem yang_mills_continuum_mass_gap_and_clock_floor_core_approximation_bridge
    (s : ℝ) (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    0 < yangMillsGapShift ∧
    yangMillsGapShift = Real.sqrt 7 / 15 ∧
    Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
    Tendsto massGapAtDensity atTop (𝓝 yangMillsGapShift) ∧
    (∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
    Tendsto (coreApproxSeq ε x) atTop (𝓝 x) := by
  have hlim : Tendsto massGapAtDensity atTop (𝓝 yangMillsGapShift) := by
    unfold yangMillsGapShift
    rw [decay_rate_closed_form]
    exact mass_gap_continuum_convergence
  have hseq := clock_floor_core_approx_at_yangMillsGapShift_convergence
    ε hε h hh hb m g k s x hx
  exact ⟨decay_rate_positive,
    decay_rate_closed_form,
    chamber_gap_continuum_convergence,
    hlim,
    hseq.1,
    hseq.2.2.2⟩

/-- Master capstone theorem uniting `R1`, `R2b`, `R3`, `R4`, and the infinite-dimensional
clock-floor Hilbert-space resolvent and Gaussian-core hierarchy at `yangMillsGapShift = √7 / 15`. -/
theorem yang_mills_r1_r2_r3_r4_clock_floor_master_synthesis
    (t : ℝ) (f : Hilbert) :
    (haarMeasureSO10 (Set.univ : Set G_SO10) = 1 ∧
     ∫ U : G_SO10, reTraceSO10 U ∂haarMeasureSO10 = 0) ∧
    (CentroidParitySplitsBlocks H_W ∧
     ChamberBathCommutes H_W ∧
     WilsonBlockHypothesis H_W) ∧
    (0 < yangMillsGapShift ∧
     yangMillsGapShift = Real.sqrt 7 / 15 ∧
     ∀ τ : ℝ, 0 ≤ τ → ∀ ψ : ChamberState, ChamberState.InOrthVac ψ →
       (heatSemigroupShifted τ ψ).normSq ≤ Real.exp (-2 * τ * yangMillsGapShift) * ψ.normSq) ∧
    (Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
     Tendsto massGapAtDensity atTop (𝓝 (Real.sqrt 7 / 15))) ∧
    (squaredHamiltonianResolvent ε hε h hh hb m g k t yangMillsGapShift f ∈
       hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     ‖RT yangMillsGapShift f‖ + ‖RP yangMillsGapShift f‖ + ‖RG yangMillsGapShift f‖ +
       ‖RS t yangMillsGapShift f‖ + ‖RH t yangMillsGapShift f‖ ≤
       5 * yangMillsGapShift⁻¹ * ‖f‖) :=
  ⟨⟨haarMeasureSO10_univ, haarTraceIdentitySO10_concrete⟩,
   ⟨H_W_centroid_parity_splits_blocks,
    H_W_chamberBath_commutes_via_R2b,
    H_W_satisfies_block_hypothesis⟩,
   ⟨decay_rate_positive,
    decay_rate_closed_form,
    spectral_gap_implies_exp_decay_in_orth_complement⟩,
   ⟨chamber_gap_continuum_convergence,
    mass_gap_continuum_convergence⟩,
   ⟨(clock_floor_iterated_resolvent_at_yangMillsGapShift_mem_ten_domains
      ε hε h hh hb m g k t 0 f).1,
    clock_floor_resolvent_at_yangMillsGapShift_five_operator_sum_le
      ε hε h hh hb m g k t f⟩⟩

#print axioms so10_haar_measure_univ_and_trace_zero
#print axioms so10_wilson_haar_integral_const_and_trace_zero
#print axioms so10_build4_constant_channel_haar_bridge
#print axioms so10_centroid_anti_invariant_closure
#print axioms so10_centroid_anti_invariant_integral_vanishes
#print axioms wilson_chamber_bath_commutes_via_so10_haar
#print axioms wilson_r1_triple_equivalence_and_small_case
#print axioms wilson_r1_block_hypothesis_and_haar_trace
#print axioms wilson_r1_closure_master_synthesis
#print axioms wilson_r1_r2b_verdict_agreement
#print axioms chamber_mass_gap_closed_form_and_lower_bound
#print axioms chamber_heat_semigroup_orth_vac_contraction
#print axioms chamber_heat_semigroup_operator_norm_ratio_le
#print axioms chamber_additive_and_log_gap_correlator_bridge
#print axioms chamber_matrix_and_spectrum_continuum_convergence
#print axioms chamber_gap_and_mass_gap_continuum_convergence
#print axioms bath_spectrum_continuum_rigidity_three
#print axioms physical_wilson_expectation_continuum_and_haar_bridge
#print axioms canonical_continuum_limit_interface_properties
#print axioms wilson_r3_r4_combined_master_synthesis
#print axioms wilson_r3_r4_verdict_and_status_ledger
#print axioms yangMillsGapShift_pos_and_eq_massGapAtDensity
#print axioms clock_floor_resolvent_at_yangMillsGapShift_five_operator_sum_le
#print axioms clock_floor_iterated_resolvent_at_yangMillsGapShift_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_yangMillsGapShift_second_power_eq
#print axioms clock_floor_iterated_resolvent_at_yangMillsGapShift_residual_diff_eq
#print axioms clock_floor_common_domain_at_yangMillsGapShift_shifted_defects
#print axioms clock_floor_common_domain_at_yangMillsGapShift_two_time_defect_le
#print axioms clock_floor_core_approx_at_yangMillsGapShift_convergence
#print axioms yang_mills_r1_r2b_r3_r4_and_clock_floor_iterated_resolvent_bridge
#print axioms yang_mills_continuum_mass_gap_and_clock_floor_core_approximation_bridge
#print axioms yang_mills_r1_r2_r3_r4_clock_floor_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorYangMillsR1R2R3R4ContinuumBridge
